#r "/home/runner/.nuget/packages/fsharpx.collections/3.1.0/lib/netstandard2.0/FSharpx.Collections.dll"
open FSharpx.Collections

// Test PersistentHashMap
let m1 = PersistentHashMap.empty<string, int>
let m2 = PersistentHashMap.add "a" 1 m1
let v = PersistentHashMap.tryFind "a" m2
printfn "PersistentHashMap tryFind: %A" v

// Test ofSeq/toSeq
let m3 = PersistentHashMap.ofSeq [("x", 10); ("y", 20)]
printfn "PersistentHashMap ofSeq count: %d" (PersistentHashMap.length m3)

// Test DList
let d1 = DList.empty<int>
let d2 = DList.singleton 1
let d3 = DList.append d2 (DList.singleton 2)
printfn "DList toList: %A" (DList.toList d3)

// Check if ofSeq exists
let d4 = DList.ofSeq [1;2;3]
printfn "DList.ofSeq: %A" (DList.toList d4)
