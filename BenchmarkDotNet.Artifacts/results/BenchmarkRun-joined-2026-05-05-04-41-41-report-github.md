```

BenchmarkDotNet v0.15.8, Linux Ubuntu 24.04.4 LTS (Noble Numbat)
AMD EPYC 9V74 2.83GHz, 1 CPU, 4 logical and 2 physical cores
.NET SDK 10.0.201
  [Host]   : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3 DEBUG
  ShortRun : .NET 10.0.5 (10.0.5, 10.0.526.15411), X64 RyuJIT x86-64-v3

Job=ShortRun  IterationCount=3  LaunchCount=1  
WarmupCount=3  

```
| Type               | Method                                                | ChainDepth | DatabaseSize | Mean      | Error      | StdDev   | Gen0     | Gen1    | Allocated  |
|------------------- |------------------------------------------------------ |----------- |------------- |----------:|-----------:|---------:|---------:|--------:|-----------:|
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **5**          | **?**            |  **69.50 μs** |   **5.812 μs** | **0.319 μs** |   **8.0566** |  **0.2441** |  **133.14 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (indexed)&#39;           | 5          | ?            |  59.32 μs |  14.035 μs | 0.769 μs |   6.6528 |  0.1831 |  108.79 KB |
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **10**         | **?**            | **185.82 μs** |  **32.030 μs** | **1.756 μs** |  **22.4609** |  **1.2207** |  **369.39 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (indexed)&#39;           | 10         | ?            | 145.08 μs |  26.594 μs | 1.458 μs |  17.3340 |  0.7324 |  285.24 KB |
| **AncestorBenchmarks** | **&#39;ancestor - find all descendants (non-indexed)&#39;**       | **20**         | **?**            | **549.23 μs** |  **74.993 μs** | **4.111 μs** |  **70.3125** |  **7.8125** | **1149.72 KB** |
| AncestorBenchmarks | &#39;ancestor - find all descendants (indexed)&#39;           | 20         | ?            | 399.18 μs |  28.731 μs | 1.575 μs |  51.2695 |  5.3711 |  843.72 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **?**          | **50**           |  **35.40 μs** |   **3.873 μs** | **0.212 μs** |   **5.4932** |  **0.2441** |   **90.13 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (indexed)&#39;     | ?          | 50           |  38.76 μs |   3.621 μs | 0.199 μs |   5.8594 |  0.2441 |   96.43 KB |
| SolverBenchmarks   | &#39;solve - first result only (non-indexed)&#39;             | ?          | 50           |  11.06 μs |   0.071 μs | 0.004 μs |   1.9073 |  0.0763 |    31.2 KB |
| SolverBenchmarks   | &#39;solve - first result only (indexed)&#39;                 | ?          | 50           |  14.35 μs |   5.251 μs | 0.288 μs |   2.2888 |  0.1068 |    37.5 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **?**          | **200**          | **140.55 μs** |  **15.281 μs** | **0.838 μs** |  **21.7285** |  **3.4180** |  **357.32 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (indexed)&#39;     | ?          | 200          | 161.08 μs |  46.562 μs | 2.552 μs |  23.1934 |  4.1504 |   381.2 KB |
| SolverBenchmarks   | &#39;solve - first result only (non-indexed)&#39;             | ?          | 200          |  41.32 μs |   2.463 μs | 0.135 μs |   7.2021 |  1.0986 |  117.92 KB |
| SolverBenchmarks   | &#39;solve - first result only (indexed)&#39;                 | ?          | 200          |  55.48 μs |   3.498 μs | 0.192 μs |   8.6670 |  1.5869 |   141.8 KB |
| **SolverBenchmarks**   | **&#39;solve - enumerate all from fan-out DB (non-indexed)&#39;** | **?**          | **1000**         | **742.07 μs** |  **55.084 μs** | **3.019 μs** | **108.3984** | **53.7109** | **1782.32 KB** |
| SolverBenchmarks   | &#39;solve - enumerate all from fan-out DB (indexed)&#39;     | ?          | 1000         | 806.58 μs | 174.946 μs | 9.589 μs | 116.2109 | 65.4297 | 1899.95 KB |
| SolverBenchmarks   | &#39;solve - first result only (non-indexed)&#39;             | ?          | 1000         | 207.88 μs |   3.751 μs | 0.206 μs |  35.4004 | 17.5781 |  580.42 KB |
| SolverBenchmarks   | &#39;solve - first result only (indexed)&#39;                 | ?          | 1000         | 275.51 μs |  66.745 μs | 3.659 μs |  42.4805 | 24.9023 |  698.05 KB |
