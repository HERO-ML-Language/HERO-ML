module Value

open Bound

let assert_arr_elem_type (arr_type : AST.Type) (val_type : AST.Type) =
    if val_type <> arr_type then
        failwithf "Cannot store an element of type %s in an array of type %s"
            val_type.Str arr_type.Str

// if `index' doesn't fall inside `bbox' then a negative value is returned
let unfold_index (bbox : (int * int) list) (index : Index) : int =
    (0, bbox, index.Comps)
    |||> List.fold2 (fun res (l,u) c ->
        let c' = c - l
        let w = u - l + 1
        if 0 <= c' && c' < w then
            // note: if res < 0 from before, then this will also give a negative value since
            // w * res + c' < w * res + w = w * (res + 1) <= 0
            w * res + c'
        else -1)

let fold_index (bbox : (int * int) list) (index : int) : Index =
    (bbox, index)
    ||> List.mapFoldBack (fun (l,u) idx ->
        let w = u - l + 1
        let c = l + idx % w
        (c, idx / w))
    |> fst
    |> Index

let get_store_index (bbox : (int * int) list) (clust_dict : int array * int array * int array)
                    (index : Index) : int =
    let idx' = unfold_index bbox index
    let l1s, l2s, _ = clust_dict
    // `clust_dict' is sorted on the cluster starting index, and performing the search this way
    // always returns the first cluster whose starting index is less than or equal to the query
    // index
    let ci = System.Array.BinarySearch (l1s, idx' + 1) + 1 |> (~~~)
    l2s[ci] + idx' - l1s[ci]

type Value =
    | Int   of int
    | Float of float
    | Bool  of bool
    | Bound of Bound
    | Array of Abst_Array
    | Undef of AST.Type
    | Param of AST.Type
    // If an error is "demotable" then this means that it will be demoted to Undef if it occurs
    // inside the body of a forall expression
    | Error of message : string * demotable : bool * AST.Type

    member this.Type : AST.Type =
        match this with
        | Int   _   -> AST.Type.Int
        | Float _   -> AST.Type.Float
        | Bool  _   -> AST.Type.Bool
        | Bound bnd -> AST.Type.Bound bnd.Num_Dims
        | Array arr -> AST.Type.Array (arr.Elem_Type, arr.Num_Dims)
        | Undef t | Param t | Error (_,_,t) -> t

    // Tabulates `this' if it's an array, and simply copies other types of values.
    member this.Tabulate : Value =
        match this with
        | Array arr -> arr.Tabulate
        | _ -> this

    member this.Str =
        match this with
        | Int value   -> string value
        | Float value -> string value
        | Bool value  -> string value
        | Bound value -> value.Str
        | Array value -> value.Str
        | Undef _     -> "?"
        | Param _     -> "(parametric)"
        | Error (msg,_,_) -> sprintf "ERROR (%s)" msg

    override this.ToString () = this.Str

and Index_Elem_Map =
    | Impl of func : (Index -> Value)
    // `clust_dict' is conceptually a list of triples, but is represented instead as a triple of
    // arrays to support efficient binary searches for clusters
    | Expl of bbox : (int * int) list * clust_dict : (int array * int array * int array) * store : Value array

and Abst_Array private (elem_type : AST.Type, bound : Bound, index_elem_map : Index_Elem_Map) =
    member _.Elem_Type = elem_type
    member _.Num_Dims = bound.Num_Dims
    member _.Size = bound.Size
    member _.Bound = bound

    // Creates an uninitialized array.
    new (elem_type : AST.Type, bound : Bound) =
        Abst_Array (elem_type, bound, Impl (fun _ -> Undef elem_type))

    // Creates an array and initializes it using the generator function `elem_func'.
    new (elem_type : AST.Type, bound : Bound, elem_func : Index -> Value) =
        Abst_Array (elem_type, bound, Impl elem_func)

    // Creates an array initialized to `elems'. Elements of `bound' not included in `elems' become
    // uninitialized.
    new (elem_type : AST.Type, bound : Bound, elems : (Index * Value) seq) =
        let elems = Seq.cache elems
#if DEBUG
        elems |> Seq.iter (fun (i,v) ->
            assert_index_dims bound.Num_Dims i
            if not (bound.Contains i) then
                failwith "Index out of bounds"
            assert_arr_elem_type elem_type v.Type)
#endif
        // compute minimum bounding box of bound
        let bbox =
            let rec min_bound_box (bnd : Bound) : (int * int) list =
                match bnd with
                | Dense range -> [range]
                | Sparse_Fin (_, bnd_elems) ->
                    let bbox_0 = (Seq.head bnd_elems).Comps |> List.map (fun c -> (c,c))
                    (bbox_0, Seq.tail bnd_elems)
                    ||> Seq.fold (fun bbox idx ->
                        (bbox, idx.Comps)
                        ||> List.map2 (fun (bmin,bmax) c -> (min bmin c, max bmax c)))
                | Product (_, factors) -> factors |> List.collect min_bound_box
                | _ -> failwith "An empty or infinite bound has no minimum bounding box"
            min_bound_box bound
        // sort the elements by the lexicographical ordering of their indices
        let elems' =
            elems
            |> Seq.map (fun (idx,value) -> (unfold_index bbox idx, value))
            |> Seq.cache
            |> Seq.sortBy fst
#if DEBUG
        if elems' |> Seq.map fst |> Seq.pairwise |> Seq.exists ((<||) (=)) then
            failwith "Duplicate indices"
#endif
        // create the cluster dictionary
        let clust_dict =
            let unf_bnd = bound.Get_Seq |> Seq.map (unfold_index bbox)
            ([(-1,0,0)], unf_bnd) // begin with a temporary sentinel entry
            ||> Seq.fold (fun cd ui ->
                let (l1,l2,n) = cd.Head
                if ui = l1 + n then
                    // adjacent to the last index of the current cluster - extend the cluster
                    (l1, l2, n + 1) :: cd.Tail
                else
                    // a jump larger than one - start a new cluster
                    (ui, l2 + n, 1) :: cd)
            |> List.rev
            |> List.tail // remove sentinel entry
            |> fun tuples ->
                // turn list of triples into triple of arrays
                let num = tuples.Length
                let l1s = Array.zeroCreate num
                let l2s = Array.zeroCreate num
                let ns  = Array.zeroCreate num
                tuples |> List.iteri (fun i (l1,l2,n) ->
                    l1s[i] <- l1
                    l2s[i] <- l2
                    ns[i] <- n)
                (l1s,l2s,ns)
        // create the store
        let store =
            let bnd_size = bound.Size
            let num_elems = Seq.length elems'
            if bnd_size = num_elems then
                elems' |> Seq.map snd |> Array.ofSeq
            else
                let store = Array.replicate bnd_size (Undef elem_type)
                elems' |> Seq.iter (fun (i,v) -> store[i] <- v)
                store
        Abst_Array (elem_type, bound, Expl (bbox, clust_dict, store))

    // Creates an array initialized to `elems', with a sparse bound defined from the set of indices
    // of `elems'.
    new (elem_type : AST.Type, elems : (Index * Value) seq) =
        let bound = Bound.Bound (Seq.map fst elems)
        Abst_Array (elem_type, bound, elems)

    // Creates a dense array initialized to `elems'. `bound' should be dense and `elems' should have
    // an element for each element of `bound'. `elems' is assumed to be ordered lexicographically.
    new (elem_type : AST.Type, bound : Bound, elems : Value array) =
#if DEBUG
        if elems.Length <> bound.Size then
            failwith "Wrong number of elements given"
        elems |> Array.iter (fun v -> assert_arr_elem_type elem_type v.Type)
#endif
        match bound with
        | Dense_General (_,index_ranges) ->
            // the whole array is a single cluster
            let index_elem_map = Expl (index_ranges, ([|0|],[|0|],[|elems.Length|]), elems)
            Abst_Array (elem_type, bound, index_elem_map)
        | _ ->
            failwith "This constructor should only be used for dense arrays"
            Abst_Array (elem_type, bound) // dummy to avoid compile error

    member this.Access (index : Index) : Value =
        assert_index_dims this.Num_Dims index
        if this.Bound.Contains index then
            match index_elem_map with
            | Impl func ->
                func index
            | Expl (bbox, clust_dict, store) ->
                let index' = get_store_index bbox clust_dict index
                store[index']
        else
            Error ("Array access out-of-bounds", true, this.Elem_Type)

    member this.Slice (bound : Bound) =
        Abst_Array (this.Elem_Type, meet this.Bound bound, index_elem_map)

    member this.Tabulate : Value =
        let type_ = AST.Type.Array (this.Elem_Type, this.Num_Dims)
        let try_pick_error = Seq.tryPick (snd >> function Error (msg,_,_) -> Some msg | _ -> None)
        match this.Size with
        | -1 -> Error ("Infinite arrays cannot be tabulated", false, type_)
        |  0 -> Array this // empty arrays are trivial to tabulate
        |  _ ->
            match this.Elem_Type with
            | AST.Type.Array _ ->
                // this is an array of arrays; thus, the elements need to be tabulated recursively as well
                let tabbed_elems = this.Get_Seq |> Seq.map (fun (idx,elem) -> (idx,elem.Tabulate)) |> Seq.cache
                match try_pick_error tabbed_elems with
                | None -> Array (Abst_Array (this.Elem_Type, this.Bound, tabbed_elems))
                | Some msg -> Error (msg,false,type_)
            | _ ->
                let elems = this.Get_Seq |> Seq.cache
                match try_pick_error elems with
                | None ->
                    match index_elem_map with
                    | Impl _ -> Array (Abst_Array (this.Elem_Type, this.Bound, elems))
                    | Expl _ -> Array this
                | Some msg -> Error (msg,false,type_)

    member this.Update_Many' (mutate : bool) (new_elems : (Index * Value) seq) : Abst_Array =
        match index_elem_map with
        | Impl _ ->
            let this' = Abst_Array (this.Elem_Type, this.Bound, this.Get_Seq)
            this'.Update_Many' true new_elems
        | Expl (bbox, clust_dict, store) ->
#if DEBUG
            let new_elems = Seq.cache new_elems
            new_elems |> Seq.iter (fun (i,v) ->
                assert_index_dims this.Num_Dims i
                if not (this.Bound.Contains i) then
                    failwith "Index out of bounds"
                assert_arr_elem_type elem_type v.Type
                assert (new_elems |> Seq.forall (snd >> function Error _ -> false | _ -> true)))
#endif
            let store' = if mutate then store else Array.copy store
            new_elems |> Seq.iter (fun (idx,el) ->
                let idx' = get_store_index bbox clust_dict idx
                store'[idx'] <- el)
            let index_elem_map = Expl (bbox, clust_dict, store')
            Abst_Array (this.Elem_Type, this.Bound, index_elem_map)

    member this.Update' (mutate : bool) (index : Index) (new_elem : Value) : Abst_Array =
        this.Update_Many' mutate [(index,new_elem)]

    member this.Update_Many = this.Update_Many' false

    member this.Update = this.Update' false

    member this.Get_Seq : (Index * Value) seq =
        let bnd_seq = this.Bound.Get_Seq
        match index_elem_map with
        | Impl func ->
            Seq.map (fun idx -> idx, func idx) bnd_seq
        | Expl (bbox, clust_dict, store) ->
            seq {
                let l1s, l2s, ns = clust_dict
                let mutable ci = 0
                for idx in bnd_seq do
                    let idx' = unfold_index bbox idx
                    // increment `ci', if necessary, to the cluster that `idx' falls into
                    while (l1s[ci] + ns[ci] <= idx') do
                        ci <- ci + 1
                    idx, store[l2s[ci] + idx' - l1s[ci]]
            }

    interface System.IEquatable<Abst_Array> with
        member this.Equals (other : Abst_Array) : bool =
            this.Elem_Type = other.Elem_Type &&
            this.Bound = other.Bound &&
            Seq.forall2 (=) this.Get_Seq other.Get_Seq

    override this.Equals (other : obj) : bool = Equals_Overrider this other

    override _.GetHashCode () : int = 0 // to silence warning; not used at the moment

    member this.Str_Trunc max_elems =
        match this.Bound with
        | Empty _ -> "[]"
        | Infinite inf -> sprintf "(infinite array with bound %s)" inf.Str
        | bnd ->
            let max_elems = min (max 1 max_elems) bnd.Size // ensure 1 <= max_elems <= bnd.Size
            let seq = bnd.Get_Seq |> Seq.truncate max_elems
            match bnd with
            | Dense (l,u) ->
                let elems_str =
                    seq
                    |> Seq.fold (fun ss i -> (this.Access i).Str :: ss) []
                    |> (fun ss -> if this.Size > max_elems then "..." :: ss else ss)
                    |> List.rev
                    |> String.concat ", "
                if l = 0 then (sprintf "[ %s ]" elems_str) else (sprintf "[ %d..%d : %s ]" l u elems_str)
            | Dense_General (_,ranges) ->
                // There are at least 2 dimensions. The array is printed as a sequence of
                // 2-dimensional "slices", which are matrices with vertically aligned columns, where
                // the last dimension enumerates the columns and the next-to-last dimension
                // enumerates the rows. If there are exactly 2 dimensions then there is only a
                // single slice, otherwise the slices are printed in the lexicographical order of
                // the dimensions higher than 2 (indices within the same slice are indentical in
                // dimensions 3 and higher). The matrices are separated by single blank lines.
                let (l1,u1), (l2,u2) = let rs = List.rev ranges in rs[0], rs[1]
                // string representations of the elements, grouped by table rows, then by slices
                let slices : string list list list =
                    seq
                    |> Seq.fold (fun ss i -> (this.Access i).Str :: ss) []
                    |> (fun ss -> if this.Size > max_elems then "..." :: ss else ss)
                    |> List.rev
                    |> List.chunkBySize (u1-l1+1)
                    |> List.chunkBySize (u2-l2+1)
                // common set of column widths for the matrices
                let ws : int list =
                    let rec compute_widths acc ws (line : string list) =
                        if line.IsEmpty then
                            (List.rev acc) @ ws
                        else
                            compute_widths ((max ws.Head line.Head.Length)::acc) ws.Tail line.Tail
                    (List.replicate (u1-l1+1) 0, slices) ||> List.fold (fun ws slice ->
                        (ws, slice) ||> List.fold (fun ws line -> compute_widths [] ws line))
                // total row width; the "2" counts the width of the comma and space that separates the elements
                let line_wd = ws.Head + List.sumBy (fun w -> 2 + w) ws.Tail
                // pad and concatenate the strings in `slices' to form the sequence of matrices
                let elems_str : string =
                    slices
                    |> List.map (fun slice ->
                        slice
                        |> List.map (fun line ->
                            (([], ws), line)
                            ||> List.fold (fun (p_cols, ws) col -> (col.PadLeft ws.Head)::p_cols, ws.Tail)
                            |> fst |> List.rev
                            |> String.concat ", "
                            |> (fun line_str -> line_str.PadRight line_wd))
                        |> String.concat "\n  ")
                    |> String.concat "\n\n  "
                // unless all dimensions are indexed from 0, include a preamble specifying the index
                // ranges
                if List.forall (fst >> ((=) 0)) ranges then
                    sprintf "[ %s ]" elems_str
                else
                    sprintf "[ %s :\n  %s ]" bnd.Str elems_str
            | _ ->
                // The array is printed as a sequence of slices as in the dense case above, but not
                // with vertically aligned columns. In addition, the first element in each row has
                // its index written in front of it, which is the case also for elements where the
                // last dimension of the index changes by more than 1 from the preceding index. If
                // there are more than one slice, they are separated by single blank lines. (Also
                // note that in the one-dimensional case there will be a single slice consisting of
                // a single row.)
                (([], Seq.head seq), seq)
                ||> Seq.fold (fun (ss,prev_i) i ->
                    (   let ri, pi = List.rev i.Comps, List.rev prev_i.Comps
                        let ss =
                            (if ri.Tail = pi.Tail then ", "
                            elif ri.Tail.Tail = pi.Tail.Tail then "\n  "
                            else "\n\n  ") :: ss
                        (this.Access i).Str ::
                            (if ri.Tail <> pi.Tail || ri[0] <> pi[0] + 1
                            then ":" :: i.Str :: ss
                            else ss)
                    ), i)
                |> fst
                |> (fun ss -> " ]" :: if this.Size > max_elems then ", ..." :: ss else ss)
                |> List.rev
                |> (fun ss -> "[ " :: ss.Tail)
                |> String.concat ""

    member this.Str = this.Str_Trunc 100

    override this.ToString () = this.Str

// TODO: move this somewhere else
// If f x <> None for all x in l, then Some (map (fun x -> (f x).Value) l) is returned, otherwise
// None is returned (the computation is exited early as soon as f x = None for some x in l).
let tryMap f l =
    let rec tryMap' f acc l =
        match l with
        | [] -> Some (List.rev acc)
        | x::l' ->
            match f x with
            | Some y -> tryMap' f (y::acc) l'
            | None -> None
    tryMap' f [] l

let (|Index|_|) (comps : Value list) =
    comps |> tryMap (function Int c -> Some c | _ -> None) |> Option.map Bound.Index

let (|Index_List|_|) (comps : Value list list) =
    comps |> tryMap (|Index|_|)

let (|Bound_List|_|) (comps : Value list) =
    comps |> tryMap (function Bound b -> Some b | _ -> None)
