import Std.Internal.Async
import Std.Sync.Mutex
open Std.Internal.IO Async Std

def writeSlow (n: Nat) (s: String := "")(count : Std.Mutex Nat) : Async Nat := do
  IO.sleep (n * 1000).toUInt32
  IO.FS.writeFile "slow.txt" s!"This is a slow write operation after {n} seconds."
  IO.eprintln s!"Write operation completed after {n} seconds."
  unless s.isEmpty do
    IO.eprintln s!"Additional input: {s}"
  count.atomically (·.modify (fun n ↦ n + 1))
  let c ← count.atomically (·.get)
  IO.eprintln s!"Total writes completed: {c}"
  return n

def main (args: List String) : IO Unit := do
  AsyncTask.block <| ←
    Async.toIO do
      let n := args[0]! |>.toNat!
      let count ←  Std.Mutex.new 0
      let stdin ← IO.getStdin
      for m in [1:n] do
        background (prio := Task.Priority.default) (writeSlow m "" count)
      IO.eprintln "Write operation started, check slow.txt. Waiting for input."
      let inp ← stdin.getLine
      for m in [1:n] do
        background (prio := Task.Priority.default) (writeSlow m inp count)
