module FsLogical.Benchmarks.Program

open BenchmarkDotNet.Running
open FsLogical.Benchmarks.Benchmarks

[<EntryPoint>]
let main argv =
    BenchmarkSwitcher
        .FromTypes(
            [| typeof<UnificationBenchmarks>
               typeof<ApplySubstBenchmarks>
               typeof<SolverBenchmarks>
               typeof<AncestorBenchmarks>
               typeof<SubstitutionBenchmarks> |])
        .Run(argv)
    |> ignore
    0
