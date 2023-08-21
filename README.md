# Quickstart

## Build instructions

On Windows, the easiest way to build and run the project is by using Visual Studio (open the solution file [HERO-ML.sln](HERO-ML.sln)). Visual Studio Community is [available for free](https://visualstudio.microsoft.com/vs/community/).

On Unix (the following has only been tested on Ubuntu Desktop), first install .NET (more details and other methods can be found here: https://fsharp.org/use/linux/):

- Download the bash script https://dot.net/v1/dotnet-install.sh
- Install .NET using the following commands:

```shell
chmod u+x dotnet-install.sh
./dotnet-install.sh --channel Current
```

- Add .NET to your PATH variable:

```shell
export PATH=$PATH:~/.dotnet
```

- Run the HERO-ML interpreter:

```shell
cd HERO-ML/Interpreter
dotnet run my_hero-ml_file.hml
```

(Substitute ''HERO-ML/'' above for the actual path where the repository has been cloned.)

## Command-line interface

To run a HERO-ML program in the interpreter, simply give the file name as a command-line argument. It is also possible to list more than one program on the command line. In this case they are each executed in turn, and any values written using `out` statements (see the [language spec](https://www.es.mdu.se/publications/6649-HERO_ML_Specification)) by one program are placed in a LIFO (last-in-first-out) queue to be read by the `in` statements of the subsequent programs in the sequence. Any values output by the last program are written with a textual representation to the console.
