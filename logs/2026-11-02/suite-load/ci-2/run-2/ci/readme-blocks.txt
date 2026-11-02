$ /py/bin/python3 -I scripts/check-readme.py README.md examples
ok   'let client ← Client.new' is in examples/RequestExample.lean
ok   'let json := "{\\"name\\": \\"lean-http\\", \\"stars\\": 5}"' is in examples/RequestExample.lean
ok   'let req := Request.get (.parse! s!"{base}/numbers?count=100000") |>.body .empty' is in examples/StreamExample.lean
ok   'def numberedLines (count : Nat) : BaseIO RequestBody := do' is in examples/UploadExample.lean
ok   'let body ← numberedLines 10000' is in examples/UploadExample.lean
ok   'let token ← Std.CancellationToken.new' is in examples/RequestExample.lean
ok   'def patientClient : BaseIO Client :=' is in examples/StreamExample.lean
ok   'def privateCaClient : BaseIO Client :=' is in examples/RequestExample.lean
ok   'def advice (err : Error) : String :=' is in examples/RequestExample.lean
9 Lean blocks checked, 0 not in an example
exit status 0, wall 173 ms
