$ /py/bin/python3 -I scripts/check-readme.py README.md examples
ok   'let client ← Client.new' is in examples/RequestExample.lean
ok   'let json := "{\\"name\\": \\"lean-http\\", \\"stars\\": 5}"' is in examples/RequestExample.lean
ok   'let req := Request.get (.parse! s!"{base}/numbers?count=100000") |>.body .empty' is in examples/StreamExample.lean
ok   'def patientClient : BaseIO Client :=' is in examples/StreamExample.lean
ok   'def privateCaClient : BaseIO Client :=' is in examples/RequestExample.lean
ok   'def advice (err : Error) : String :=' is in examples/RequestExample.lean
6 Lean blocks checked, 0 not in an example
exit status 0, wall 188 ms
