module Bound

type Index =
    | Index of int list

    member this.Comps =
        let (Index this') = this
        this'

    member this.Num_Dims = this.Comps.Length
    member this.Head = this.Comps.Head
    member this.Item (i : int) = this.Comps[i]

    member this.Str =
        if this.Num_Dims = 1 then string this.Head
        else sprintf "(%s)" (this.Comps |> List.map string |> String.concat ",")

    member this.Str_Emb (emb : int list) =
        let num_dims = this.Num_Dims
        if num_dims = 1 then
            string this.Head
        elif emb.Length = num_dims then
            this.Str
        else
            let xs =
                (if emb.Head = 0 then "" else String.replicate emb.Head "*,") ::
                (List.pairwise emb |> List.map (fun (a,b) -> "," + String.replicate (b-a-1) "*,")) @
                [String.replicate (num_dims - List.last emb - 1) ",*"]
            sprintf "(%s)" (
                ([xs.Head], this.Comps, xs.Tail)
                |||> List.fold2 (fun strs c x -> x :: (string c) :: strs)
                |> List.rev
                |> String.concat "")

    override this.ToString () = this.Str

let assert_index_dims (exp_dims : int) (index : Index) : unit =
    // note: if exp_dims = 0 then this represents "all" or "empty", with which
    // indices of any number of dimensions are compatible
    if index.Num_Dims <> exp_dims && exp_dims <> 0 then
        failwithf "Expected a %d-dimensional index, but a %d-dimensional index was given" exp_dims index.Num_Dims

let Equals_Overrider (this : 'T) (other : obj) : bool =
    match other with
    | :? 'T as other_T -> (this :> System.IEquatable<'T>).Equals other_T
    | _ -> false

type Bound private (num_dims : int, bound' : Bound') =
    member this.Num_Dims = num_dims
    member this.Bound' = bound'
    
    new (?is_all : bool) = Bound (0, defaultArg is_all false)

    new (num_dims : int, ?is_all : bool) =
        Bound (num_dims, if (defaultArg is_all false) then All else Empty)

    // Creates a dense bound.
    new (range : int * int) =
        if fst range > snd range then
            Bound (1, false)
        else
            Bound (1, Dense range)

    // Creates a dense bound.
    new (l : int, u : int) = new Bound ((l,u))

    // Creates a product of dense bounds (AKA a multidimensional dense bound).
    new (ranges : (int * int) list) = new Bound (ranges |> List.map Bound)

    new (num_dims : int, elems : Index seq, ?emb : int list) =
        let emb =
            if emb.IsSome then
                // all elements of `emb' should be < num_dims and there should be no duplicate elements
                if List.exists ((<=) num_dims) emb.Value || (List.distinct emb.Value).Length < emb.Value.Length then
                    failwith "Invalid `emb' member"
                emb.Value
            else [0..num_dims-1]
        if Seq.isEmpty elems then
            Bound (num_dims, false)
        else
            if elems |> Seq.exists (fun elem -> elem.Num_Dims <> emb.Length) then
                failwith "Dimensions do not match"
            // to simplify various operations on this type of bound we put it into a canonical form
            // where `emb' is sorted in increasing order
            if emb |> List.pairwise |> List.forall ((<||) (<)) then
                // `emb' already sorted
                Bound (num_dims, Sparse (set elems, emb))
            else
                // sort `emb' and then apply the corresponding permutation to each element of `elems'
                let pl, s_emb = emb |> List.indexed |> List.sortBy snd |> List.unzip
                let pa = Array.ofList pl
                let elems_set =
                    elems
                    |> Seq.map (fun idx -> idx.Comps |> List.permute (fun i -> pa[i]) |> Index)
                    |> set
                Bound (num_dims, Sparse (elems_set, s_emb))

    // Creates a sparse bound (or "empty") containing the indices given by `elems'.
    new (elems : Index seq) =
        let num_dims = (Seq.head elems).Num_Dims
        Bound (num_dims, elems)

    // Creates a sparse one-dimensional bound (or "empty") containing the indices given by `elems'.
    new (elems : int seq) = Bound (Seq.map (List.singleton >> Index) elems)

    new (num_dims : int, pred_func : Index -> bool) =
        if num_dims <= 0 then
            failwith "Bound must have at least one dimension. \
                      To create \"all\" or \"empty\", use the designated constructors"
        Bound (num_dims, Pred pred_func)

    // Creates a product bound (or "empty" if "empty" occurs in `factors')
    new (factors : Bound list) =
        if factors.IsEmpty || factors.Tail.IsEmpty then
            failwith "Bound products must have at least two factors"
        if factors |> List.exists (fun fac -> fac.Num_Dims <> 1) then
            failwith "Only one-dimensional factors are allowed in bound products"
        let num_dims = factors.Length
        if factors |> List.exists (fun fac -> match fac.Bound' with Empty -> true | _ -> false) then
            Bound (num_dims,false)
        else
            Bound (num_dims, Product factors)

    // Returns -1 for infinite bounds
    member this.Size : int =
        match this.Bound' with
        | Empty -> 0
        | All -> -1
        | Dense (l,u) -> u - l + 1
        | Sparse (elems,emb) -> if emb.Length < this.Num_Dims then -1 else elems.Count
        | Pred _ -> -1
        | Product factors ->
            let sizes = factors |> List.map (fun fac -> fac.Size)
            if List.contains -1 sizes then -1
            else List.reduce (*) sizes

    member this.Contains (index : Index) : bool =
        assert_index_dims this.Num_Dims index
        match this.Bound' with
        | Empty -> false
        | All -> true
        | Dense (l,u) ->
            let index' = index.Head
            l <= index' && index' <= u
        | Sparse (elems,emb) ->
            // note: the components index[i] where i is not found in `emb' are ignored, because the
            // corresponding dimensions are unconstrained by the bound
            let proj_idx = List.map (fun i -> index[i]) emb |> Index
            Set.contains proj_idx elems
        | Pred pred_func -> pred_func index
        | Product factors ->
            (factors, index.Comps) ||> List.forall2 (fun fac comp -> fac.Contains (Index [comp]))

    // Returns a sequence that enumerates the indices of this bound in lexicographical order.
    // Precondition: This bound is finite.
    member this.Get_Seq : seq<Index> =
        let rec prod_help =
            function
            | [] -> seq { Index [] }
            | h::t ->
                let tseq = prod_help t
                h |> Seq.collect (fun (i : Index) ->
                    Seq.map (fun (j : Index) -> Index (i.Comps @ j.Comps)) tseq)

        match this.Bound' with
        | Empty -> seq []
        | Dense (l,u) -> seq { for i in l..u -> Index [i] }
        | Sparse (elems,emb) when emb.Length = this.Num_Dims -> Set.toSeq elems
        | Product factors -> factors |> List.map (fun fac -> fac.Get_Seq |> Seq.cache) |> prod_help
        | _ -> failwith "Cannot enumerate infinite bound"

    interface System.IEquatable<Bound> with
        member this.Equals (other : Bound) : bool =
            this.Num_Dims = other.Num_Dims &&
            match this.Bound', other.Bound' with
            | Empty, Empty -> true
            | All, All -> true
            | Dense r1, Dense r2 when r1 = r2 -> true
            | Sparse (es1,emb1), Sparse (es2,emb2) when es1 = es2 && emb1 = emb2 -> true
            | Product fs1, Product fs2 when fs1 = fs2 -> true
            | Pred _, _ | _, Pred _ ->
                failwith "Comparisons involving predicate bounds are undefined"
            | _ ->
                false

    override this.Equals (other : obj) : bool = Equals_Overrider this other

    override this.GetHashCode () : int = 0 // to silence warning; not used at the moment

    member this.Str with get () =
        let dim_str _ = sprintf " (%s dim.)" (if this.Num_Dims = 0 then "d" else string this.Num_Dims)
        match this.Bound' with
        | Empty -> "empty" + (dim_str ())
        | All -> "all" + (dim_str ())
        | Dense (l,u) -> sprintf "%d..%d" l u
        | Sparse (elems,emb) ->
            sprintf "{ %s }" (elems |> Set.toSeq |> Seq.map (fun idx -> idx.Str_Emb emb) |> String.concat ", ")
        | Pred _ -> "(predicate)" + (dim_str ())
        | Product factors ->
            sprintf "(%s)" (factors |> List.map (fun fac -> fac.Str) |> String.concat ", ")

    override this.ToString () = this.Str

and Bound' =
    | Empty
    | All
    | Dense of range : (int * int)
    // `emb' specifies an injective mapping from the dimensions of `elems' to those of a
    // higher-dimensional space in which `elems' should be considered embedded.
    // Each element `e' of `elems' specifies the subset of elements
    // { (f : Index) : f.Length = Num_Dims, f[i] = e[j] if ∃j . emb[j] = i }.
    // Conversely, given a Num_Dims-dimensional index `i', it is contained in the bound
    // if and only if [i[emb[0]] ; i[emb[1]] ; ... ; i[emb[n-1]]] ∈ elems,
    // where n = emb.Length.
    | Sparse of elems : Set<Index> * emb : int list
    | Pred of pred_func : (Index -> bool)
    | Product of factors : Bound list

let (|Empty|All|Dense|Sparse|Pred|Product|) (b : Bound) =
    match b.Bound' with
    | Empty        -> Empty b.Num_Dims
    | All          -> All b.Num_Dims
    | Dense A      -> Dense A
    | Sparse (A,B) -> Sparse (b.Num_Dims,A,B)
    | Pred A       -> Pred (b.Num_Dims,A)
    | Product A    -> Product (b.Num_Dims,A)

let (|Finite|Infinite|) (b : Bound) =
    match b.Size with
    | -1 -> Infinite b
    | _  -> Finite b

let (|Dense_General|_|) (b : Bound) =
    match b with
    | Dense range -> Some (1,[range])
    | Product (_,facs) ->
        let ranges = facs |> List.choose (function Dense range -> Some range | _ -> None)
        let num_dense = ranges.Length
        if num_dense = facs.Length then
            Some (num_dense, ranges)
        else
            None
    | _ -> None

let (|Sparse_Fin|_|) (b : Bound) =
    match b with Sparse (num_dims,elems,_) & Finite _ -> Some (num_dims,elems) | _ -> None

let (|Sparse_Inf|_|) (b : Bound) =
    match b with Sparse (num_dims,elems,emb) & Infinite _ -> Some (num_dims,elems,emb) | _ -> None

// common constants mainly for use in the tests

let Empty   = Bound ()
let Empty_1 = Bound (1,false)
let Empty_2 = Bound (2,false)
let Empty_3 = Bound (3,false)

let All   = Bound true
let All_1 = Bound (1,true)
let All_2 = Bound (2,true)
let All_3 = Bound (3,true)

// approximates an infinite sparse bound as a product of one-dimensional bounds, with finite sparse
// bounds representing the constrained dimensions and "all" factors representing the unconstrained
// dimensions
let sparse_to_product (num_dims : int) (elems : Set<Index>) (emb : int list) =
    // turn `elems' from a set of lists (Index's) into a list of sets
    // (of one-dimensional Index's)
    let elems' =
        (List.replicate emb.Length (set []), elems)
        ||> Set.fold (fun res elem ->
            (res, elem.Comps) ||> List.map2 (fun s c -> Set.add c s))
    // create a one-dimensional factor for each set in `elems'', and make copies of "all" for the
    // dimensions not included in `emb' (note that the factors are create in the reverse order)
    (([],0), elems', emb)
    |||> List.fold2 (fun (facs,n) es d ->
        // invariant: n = facs.Length
        let num_all = d - n // number of copies of "all" to insert before the factor
        let fac = Bound es
        (fac :: (List.replicate num_all All_1) @ facs, n + num_all + 1))
    // finalize by adding copies of "all" so that facs.Length = num_dims, and then reversing the factors
    ||> fun facs n ->
        let num_all = num_dims - n
        (List.replicate num_all All_1) @ facs
        |> List.rev
    |> Bound

let rec join (bnd1 : Bound) (bnd2 : Bound) : Bound =
    let num_dims =
        let d1, d2 = bnd1.Num_Dims, bnd2.Num_Dims
        if d1 = d2 then d1
        elif d1 * d2 = 0 then d1 + d2
        else failwith "Dimensions do not match"

    match bnd1, bnd2 with
    // simplest cases, where one of the operands is just copied
    | All _, _ | _, All _ -> Bound (num_dims,true)
    | Empty 0, other | other, Empty _ | Empty _, other -> other

    // dense bounds
    | Dense (l1,u1), Dense (l2,u2) -> Bound (min l1 l2, max u1 u2)

    // sparse bounds, at least one of which is infinite (the case where both are finite is handled
    // more efficiently in the fallback rule for finite bounds that appears further on)
    | Sparse (_,elems1,emb1), Sparse_Inf (_,elems2,emb2)
    | Sparse_Inf (_,elems1,emb1), Sparse (_,elems2,emb2) ->
        // The `emb' member of the result should be the intersection of the elements of `emb1' and
        // `emb2' (since any dimension that is unconstrained in either bound has to be unconstrained
        // in the result). This help function assumes that `emb1' and `emb2' are sorted.
        let rec help_func emb p1 p2 j1 j2 e1 e2 =
            match e1,e2 with
            | [], _ | _ ,[] -> List.rev emb, List.rev p1, List.rev p2
            | i1::t1, i2::_  when i1 < i2 -> help_func emb p1 p2 (j1+1) j2 t1 e2
            | i1::_ , i2::t2 when i1 > i2 -> help_func emb p1 p2 j1 (j2+1) e1 t2
            | i1::t1, i2::t2 ->
                assert(i1 = i2)
                help_func (i1::emb) (j1::p1) (j2::p2) (j1+1) (j2+1) t1 t2
        let emb, p1, p2 = help_func [] [] [] 0 0 emb1 emb2
        // `p1' and `p2' can now be used to project the elements of `elems1' and `elems2' before
        // computing their union
        let proj_elems1 = elems1 |> Set.map (fun elem -> List.map (fun j -> elem[j]) p1 |> Index)
        let proj_elems2 = elems2 |> Set.map (fun elem -> List.map (fun j -> elem[j]) p2 |> Index)
        let elems = Set.union proj_elems1 proj_elems2
        Bound (num_dims, elems, emb)

    // product bounds
    | Product (_,facs1), Product (_,facs2) ->
        (facs1,facs2) ||> List.map2 join |> Bound

    // one operand is an infinite sparse bound and the other is a product bound:
    // reinterpret the sparse bound as a product
    | Sparse_Inf (d,elems,emb), (Product _ as prod)
    | (Product _ as prod), Sparse_Inf (d,elems,emb) ->
        let sparse_as_prod = sparse_to_product d elems emb
        join sparse_as_prod prod

    // any remaining cases where both bounds are finite: return a sparse bound
    | Finite fin1, Finite fin2 ->
        Bound (num_dims, Seq.append fin1.Get_Seq fin2.Get_Seq)

    // remaining cases: at least one operand is infinite, so the result must be infinite;
    // return an OR-predicate
    | b1, b2 ->
        Bound (num_dims, fun index -> b1.Contains index || b2.Contains index)

let rec meet (bnd1 : Bound) (bnd2 : Bound) : Bound =
    let num_dims =
        let d1, d2 = bnd1.Num_Dims, bnd2.Num_Dims
        if d1 = d2 then d1
        elif d1 * d2 = 0 then d1 + d2
        else failwith "Dimensions do not match"

    match bnd1, bnd2 with
    // simplest cases, where one of the operands is just copied (note that for "all" and "empty",
    // the number of dimensions can be 0, "any number of dimensions", and this case must be handled
    // with special care so that the result is `num_dims' dimensions)
    | Empty _, other | other, Empty _ -> Bound (num_dims,false)
    | All _, All _ -> Bound (num_dims,true)
    | All _, other | other, All _ -> other

    // dense bounds
    | Dense (l1,u1), Dense (l2,u2) -> Bound (max l1 l2, min u1 u2)

    // sparse bounds, at least one of which is infinite (the case where both are finite is handled
    // more efficiently in the fallback rule that appears further on for when at least one operand is finite)
    | Sparse (_,elems1,emb1), Sparse_Inf (_,elems2,emb2)
    | Sparse_Inf (_,elems1,emb1), Sparse (_,elems2,emb2) ->
        // The `emb' member of the result should be the union of the elements of `emb1' and `emb2'.
        // Each tuple in the `elems' member of a bound represents, together with the `emb' member,
        // a subset of the bound. Thus, we want to compute the union of all pairwise intersections
        // of such subsets from the two bounds (or tuples representing these intersections). This
        // becomes the `elems' member of the result.
        // The list `p' is used to combine two tuples `elem1' and `elem2' into one representing such
        // an intersection. It has the same length as `emb', with negative values representing
        // indices into `elem1' by their bitwise complement and non-negative values representing
        // indices into `elem2'.
        // The list `q' is used to first check that the subsets represented by two tuples has a
        // non-empty intersection, which it has if and only if the tuples are equal in the positions
        // mapped to the same dimensions (that is, positions mapped to the dimensions included in the
        // intersection of `emb1' and `emb2').
        // This help function assumes that `emb1' and `emb2' are sorted.
        let rec help_func emb p q j1 j2 e1 e2 =
            match e1,e2 with
            | [], _ ->
                (List.rev emb) @ e2,
                (List.rev p) @ [j2 .. j2+e2.Length-1],
                List.rev q
            | _, [] ->
                (List.rev emb) @ e1,
                List.rev ([~~~(j1+e1.Length-1) .. ~~~j1] @ p),
                List.rev q
            | i1::t1, i2::_  when i1 < i2 -> help_func (i1::emb) (~~~j1::p) q (j1+1) j2 t1 e2
            | i1::_ , i2::t2 when i1 > i2 -> help_func (i2::emb)    (j2::p) q j1 (j2+1) e1 t2
            | i1::t1, i2::t2 ->
                assert(i1 = i2)
                help_func (i1::emb) (~~~j1::p) ((j1,j2)::q) (j1+1) (j2+1) t1 t2
        let emb, p, q = help_func [] [] [] 0 0 emb1 emb2
        let elems =
            (Set.empty<_>, elems1) ||> Set.fold (fun acc elem1 ->
                elems2
                |> Seq.choose (fun elem2 ->
                    // if the intersection of the subsets represented by `elem1' and `elem2' is
                    // non-empty (checked using `q'), merge them using `p'
                    if List.forall (fun (j1,j2) -> elem1[j1] = elem2[j2]) q then
                        let merged = List.map (fun p_i ->
                            if p_i < 0 then elem1[~~~p_i] else elem2[p_i]) p |> Index
                        Some merged
                    else
                        None)
                |> Set.ofSeq
                |> Set.union acc)
        Bound (num_dims, elems, emb)

    // product bounds
    | Product (_,facs1), Product (_,facs2) ->
        (facs1,facs2) ||> List.map2 meet |> Bound

    // one operand is an infinite sparse bound and the other is a product bound:
    // reinterpret the sparse bound as a product
    | Sparse_Inf (d,elems,emb), (Product _ as prod)
    | (Product _ as prod), Sparse_Inf (d,elems,emb) ->
        let sparse_as_prod = sparse_to_product d elems emb
        meet sparse_as_prod prod

    // at least one operand is finite: interpret the operand with the smaller number of elements as
    // a sparse bound and filter it based on containment in the other bound
    | Finite fin, other | other, Finite fin when other.Size = -1 || fin.Size <= other.Size ->
        Bound (num_dims, fin.Get_Seq |> Seq.filter other.Contains)

    // both bounds are infinite: return an AND-predicate
    | b1, b2 ->
        Bound (num_dims, fun index -> b1.Contains index && b2.Contains index)
