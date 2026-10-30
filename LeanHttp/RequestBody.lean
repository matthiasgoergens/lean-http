module

public import Std.Async.Basic
public import LeanHttp.Call.Redirect

public section

/-!
# Request bodies

A request body is bytes held in memory, which can be sent any number of times, or a stream the
caller produces while the request is sent, which can be read only once.

A stream is pulled: the client calls its `next` for each chunk, one call at a time, and the next
call only once everything before it has been written to the connection, so the caller produces no
faster than the connection takes the bytes and the client holds at most one chunk.  A pull-based
source fits the client's model, in which the calling task drives the exchange and every operation
it waits for (a write, a read, a pull) is a task it races against the exchange's deadlines: a pull
is one more such operation, it can be abandoned when the exchange ends, and nothing runs that the
exchange did not ask for.  A push-based writer would need a task of its own running the producer and
a rendezvous between it and the exchange, and a way to stop that task when the exchange ends early.

`next` returns `some chunk` for each chunk (an empty one is skipped) and `none` at the end; an
exception from it fails the call with `Cause.requestBody`.  It is first called once the request head
has been written, never before: a call that fails before it wrote anything has read none of the
stream, so retrying it, which the per-call planner allows whatever the method, is safe.  Once any of
the request was written, a streamed body is never sent again: no retry, no re-dispatch on a fresh
connection, and a 307 or 308 redirect, which would have to send the body again, is delivered to the
caller instead of followed.

With a declared size the body is sent with a `Content-Length`, and a producer that gives more or
fewer bytes fails the call (`Cause.requestBody`) before more than the declared size goes out.  After
the last of those bytes the producer is asked once more, to check that it ends there; if the
response has already ended the call, that answer is not waited for.  Without a declared size the
body is sent with `Transfer-Encoding: chunked`, which needs HTTP/1.1.
-/

namespace LeanHttp

set_option linter.all true

open Std.Async

/--
A request body: bytes, or a stream the caller produces while the request is sent.
-/
inductive RequestBody where
  /--
  Bytes held in memory, sent with a `Content-Length`.  They can be sent again, by a retry or a
  redirect.
  -/
  | bytes (data : ByteArray)

  /--
  A stream: `next` gives the next chunk, or `none` at the end, and is called one chunk at a time,
  each once everything before it has been written.  With `size`, the body must have exactly that
  many bytes and is sent with a `Content-Length`; without, it is sent chunked.  It is read once and
  never sent again.
  -/
  | stream (size : Option Nat) (next : Async (Option ByteArray))

instance : Inhabited RequestBody := ⟨.bytes .empty⟩

namespace RequestBody

/--
The kind of the body, as the per-call planner sees it: an empty byte array is no body, other bytes
can be sent again, and a stream cannot.
-/
def kind : RequestBody → Call.BodyKind
  | .bytes data => if data.isEmpty then .none else .bytes
  | .stream .. => .stream

/--
A stream that gives `chunks`, in order, with their total size declared (or, if `declareSize` is
false, sent chunked).
-/
def ofChunks (chunks : Array ByteArray) (declareSize : Bool := true) : BaseIO RequestBody := do
  let index ← IO.mkRef 0
  let next : Async (Option ByteArray) := do
    let i ← index.modifyGet fun i => (i, i + 1)
    return chunks[i]?
  let size := if declareSize then some (chunks.foldl (· + ·.size) 0) else none
  return .stream size next

end RequestBody

end LeanHttp
