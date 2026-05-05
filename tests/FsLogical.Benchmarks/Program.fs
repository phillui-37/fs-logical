module FsLogical.Benchmarks.Program

open BenchmarkDotNet.Configs
open BenchmarkDotNet.Jobs
open BenchmarkDotNet.Running
open BenchmarkDotNet.Toolchains.NativeAot
open FsLogical.Benchmarks.Benchmarks

/// Config that runs every benchmark under both the default (JIT) runtime and
/// Native AOT, producing a side-by-side table for comparison.
let private aotCompareConfig () =
    // Use the ILCompiler version that matches the currently running .NET runtime
    // so the NativeAOT compilation is consistent with the JIT baseline.
    let ilcVersion = System.Environment.Version.ToString()
    let nativeAotJob =
        Job.Default
            .WithToolchain(
                NativeAotToolchain.CreateBuilder()
                    .UseNuGet(ilcVersion)
                    .ToToolchain())
            .WithId("NativeAOT")
    ManualConfig.Create(DefaultConfig.Instance).AddJob(nativeAotJob)

[<EntryPoint>]
let main argv =
    // When "--aot" is the first argument the runner adds the NativeAOT job so
    // that both JIT and AOT results appear in the same table.  Without the flag
    // only the regular JIT job is executed (faster for day-to-day use).
    let config : IConfig =
        if argv.Length > 0 && argv.[0] = "--aot" then
            aotCompareConfig ()
        else
            DefaultConfig.Instance

    let remainingArgs =
        if argv.Length > 0 && argv.[0] = "--aot" then argv.[1..] else argv

    BenchmarkSwitcher
        .FromTypes(
            [| typeof<UnificationBenchmarks>
               typeof<ApplySubstBenchmarks>
               typeof<SolverBenchmarks>
               typeof<AncestorBenchmarks>
               typeof<SubstitutionBenchmarks> |])
        .Run(remainingArgs, config)
    |> ignore
    0
