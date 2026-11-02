import Std.Async
/-!
How early does a libuv timer fire, by `IO.monoNanosNow`?  `sleepers` tasks each sleep `ms`
milliseconds `rounds` times through `Std.Async.Sleep` and record how long each sleep took; `hammer`
dedicated threads meanwhile start and stop timers in a loop, contending for the event loop's lock.
Prints how many sleeps ended more than 1 ms early and the earliest.
-/
open Std.Async

def kv (args : List String) (k : String) (d : Nat) : Nat :=
  (args.findSome? fun a => match a.splitOn "=" with
    | [k', v] => if k' == k then v.toNat? else none
    | _ => none).getD d

def sleeper (ms rounds : Nat) (out : IO.Ref (Array Int)) : Async Unit := do
  for _ in [0:rounds] do
    let t0 ← IO.monoNanosNow
    let s ← Sleep.mk (.ofNat ms)
    s.wait
    let t1 ← IO.monoNanosNow
    out.modify (·.push ((t1 - t0 : Nat) - (ms * 1000000 : Nat) : Int))

partial def hammer (stop : IO.Ref Bool) (n : Nat) : IO Nat := do
  if ← stop.get then return n
  let s ← (Sleep.mk (.ofNat 1000)).block
  discard <| (EAsync.toBaseIO s.wait : BaseIO _)
  s.stop
  hammer stop (n + 1)

/-- The thread of this process that waits in `epoll_wait`: libuv's event loop, while it is idle. -/
def loopThread : IO (Option String) := do
  for e in ← System.FilePath.readDir "/proc/self/task" do
    let sc ← IO.FS.readFile (e.path / "syscall")
    let n := (sc.splitOn " ").head?.getD ""
    -- epoll_wait, epoll_pwait, epoll_pwait2 on x86-64
    if n == "232" || n == "281" || n == "441" then return some e.fileName
  return none

def main (args : List String) : IO Unit := do
  if let some cpu := (args.findSome? fun a => if a.startsWith "pinloop=" then some (a.drop 8).toString else none) then
    -- Start the loop, then pin its thread to `cpu`, where the caller runs busy loops.
    (Std.Async.sleep 50).block
    match ← loopThread with
    | some tid =>
      let out ← IO.Process.output { cmd := "taskset", args := #["--pid", "--cpu-list", cpu, tid] }
      IO.println s!"pinned the loop thread {tid} to cpu {cpu}: {out.stdout.trimAscii}"
    | none => IO.println "found no thread in epoll_wait"
  let sleepers := kv args "sleepers" 4
  let ms := kv args "ms" 50
  let rounds := kv args "rounds" 100
  let nh := kv args "hammer" 0
  let stop ← IO.mkRef false
  let hs ← (List.range nh).mapM fun _ => IO.asTask (prio := .dedicated) (hammer stop 0)
  let out ← IO.mkRef #[]
  let tasks ← (List.range sleepers).mapM fun _ => EAsync.toBaseIO (sleeper ms rounds out)
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => IO.eprintln s!"sleeper failed: {e}"
  stop.set true
  let mut hn := 0
  for h in hs do
    match ← IO.wait h with
    | .ok n => hn := hn + n
    | .error _ => pure ()
  let d := (← out.get).qsort (· < ·)
  let early := d.filter (· < -1000000)
  let us (x : Int) := x / 1000
  IO.println s!"sleepers={sleepers} ms={ms} rounds={rounds} hammer={nh} hammered={hn} sleeps={d.size} early_over_1ms={early.size} earliest_us={us (d[0]?.getD 0)} p50_us={us (d[d.size / 2]?.getD 0)} latest_us={us (d.back?.getD 0)}"
  IO.println s!"earliest ten (us): {(d.extract 0 10).toList.map us}"
