```

BenchmarkDotNet v0.15.8, Linux Ubuntu 24.04.4 LTS (Noble Numbat)
AMD EPYC 9V74 2.86GHz, 1 CPU, 4 logical and 2 physical cores
.NET SDK 10.0.201
  [Host]    : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3 DEBUG
  NativeAOT : .NET 10.0.5, X64 NativeAOT x86-64-v3
  ShortRun  : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3


```
| Type               | Method                                                | Job       | Toolchain         | IterationCount | LaunchCount | WarmupCount | ChainDepth | DatabaseSize | Mean      | Error      | StdDev   | Gen0     | Gen1    | Allocated  |
|------------------- |------------------------------------------------------ |---------- |------------------ |--------------- |------------ |------------ |----------- |------------- |----------:|-----------:|---------:|---------:|--------:|-----------:|
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **5**          | **?**            |  **67.35 μs** |   **0.380 μs** | **0.355 μs** |   **8.1787** |  **0.2441** |  **133.62 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (non-indexed)&#39;       | ShortRun  | Default           | 3              | 1           | 3           | 5          | ?            |  68.67 μs |   6.217 μs | 0.341 μs |   8.0566 |  0.2441 |  133.14 KB |
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **10**         | **?**            | **179.16 μs** |   **0.655 μs** | **0.581 μs** |  **22.4609** |  **1.2207** |  **370.29 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (non-indexed)&#39;       | ShortRun  | Default           | 3              | 1           | 3           | 10         | ?            | 187.67 μs |  36.825 μs | 2.018 μs |  22.4609 |  1.4648 |  369.41 KB |
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **20**         | **?**            | **534.21 μs** |  **10.104 μs** | **9.451 μs** |  **70.3125** |  **7.8125** | **1151.36 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (non-indexed)&#39;       | ShortRun  | Default           | 3              | 1           | 3           | 20         | ?            | 555.32 μs | 124.550 μs | 6.827 μs |  70.3125 |  8.7891 | 1149.65 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **?**          | **50**           |  **34.89 μs** |   **0.400 μs** | **0.374 μs** |   **5.4932** |  **0.2441** |   **90.13 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | ?          | 50           |  37.24 μs |   4.074 μs | 0.223 μs |   5.4932 |  0.2441 |   90.13 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **?**          | **200**          | **138.94 μs** |   **0.698 μs** | **0.583 μs** |  **21.7285** |  **3.4180** |  **357.32 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | ?          | 200          | 139.78 μs |  12.258 μs | 0.672 μs |  21.7285 |  3.4180 |  357.32 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **NativeAOT** | **ILCompiler 10.0.5** | **Default**        | **Default**     | **Default**     | **?**          | **1000**         | **748.41 μs** |   **7.496 μs** | **7.012 μs** | **108.3984** | **53.7109** | **1782.32 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (non-indexed)&#39; | ShortRun  | Default           | 3              | 1           | 3           | ?          | 1000         | 730.19 μs |  88.958 μs | 4.876 μs | 108.3984 | 53.7109 | 1782.32 KB |
