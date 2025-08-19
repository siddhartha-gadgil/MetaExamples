import Std.Internal.Async
import Std.Sync.Mutex
open Std.Internal.IO Async Std

def writeSlow (n: Nat) (s: String := "")(count : Std.Mutex Nat) : Async Nat := do
  IO.sleep (n * 1000).toUInt32
  IO.eprintln s!"Write operation completed after {n} seconds; phase: {s}"
  count.atomically (·.modify (fun n ↦ n + 1))
  let c ← count.atomically (·.get)
  IO.eprintln s!"Total writes completed: {c}"
  return n

partial def loop (n: Nat) (s: String) (count : Std.Mutex Nat) (stdin : IO.FS.Stream) : Async Unit := do
  for m in [1:n] do
    background (prio := Task.Priority.default) (writeSlow m s count)
  IO.eprintln s!"Write operations started in phase {s}. Waiting for input. Type 'q' to quit"
  let inp ← stdin.getLine
  unless inp.startsWith "q" do
    loop n inp count stdin

def main (args: List String) : IO Unit := do
  AsyncTask.block <| ←
    Async.toIO do
      let n := args[0]! |>.toNat!
      let count ←  Std.Mutex.new 0
      let stdin ← IO.getStdin
      loop n "intial" count stdin
