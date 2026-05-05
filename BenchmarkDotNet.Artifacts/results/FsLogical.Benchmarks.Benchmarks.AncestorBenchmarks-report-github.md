```

BenchmarkDotNet v0.15.8, Linux Ubuntu 24.04.4 LTS (Noble Numbat)
AMD EPYC 9V74 2.60GHz, 1 CPU, 4 logical and 2 physical cores
.NET SDK 10.0.201
  [Host]   : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3 DEBUG
  ShortRun : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3


```
| Method                                          | Job       | Toolchain         | IterationCount | LaunchCount | WarmupCount | ChainDepth | Mean      | Error     | StdDev   | Gen0    | Gen1   | Allocated  |
|------------------------------------------------ |---------- |------------------ |--------------- |------------ |------------ |----------- |----------:|----------:|---------:|--------:|-------:|-----------:|
| **&#39;ancestor - find all descendants (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.0** | **Default**        | **Default**     | **Default**     | **5**          |        **NA** |        **NA** |       **NA** |      **NA** |     **NA** |         **NA** |
| &#39;ancestor - find all descendants (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | 5          |  68.89 μs |  3.621 μs | 0.198 μs |  8.0566 | 0.2441 |  133.15 KB |
| **&#39;ancestor - find all descendants (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.0** | **Default**        | **Default**     | **Default**     | **10**         |        **NA** |        **NA** |       **NA** |      **NA** |     **NA** |         **NA** |
| &#39;ancestor - find all descendants (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | 10         | 183.42 μs | 23.589 μs | 1.293 μs | 22.4609 | 1.2207 |  369.35 KB |
| **&#39;ancestor - find all descendants (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.0** | **Default**        | **Default**     | **Default**     | **20**         |        **NA** |        **NA** |       **NA** |      **NA** |     **NA** |         **NA** |
| &#39;ancestor - find all descendants (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | 20         | 555.15 μs | 73.180 μs | 4.011 μs | 70.3125 | 8.7891 | 1149.68 KB |

Benchmarks with issues:
  AncestorBenchmarks.'ancestor - find all descendants (non-indexed)': NativeAOT(Toolchain=ILCompiler 10.0.0) [ChainDepth=5]
  AncestorBenchmarks.'ancestor - find all descendants (non-indexed)': NativeAOT(Toolchain=ILCompiler 10.0.0) [ChainDepth=10]
  AncestorBenchmarks.'ancestor - find all descendants (non-indexed)': NativeAOT(Toolchain=ILCompiler 10.0.0) [ChainDepth=20]
