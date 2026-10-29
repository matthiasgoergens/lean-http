module

@[expose] public section

/-!
# `Retry-After`

The value of a `Retry-After` field (RFC 9110 section 10.2.3): a number of seconds, or an HTTP-date.
A recipient must accept an HTTP-date in each of its three formats (section 5.6.7): the preferred
IMF-fixdate (`Sun, 06 Nov 1994 08:49:37 GMT`), the obsolete RFC 850 format
(`Sunday, 06-Nov-94 08:49:37 GMT`, with a two-digit year) and C's `asctime` format
(`Sun Nov  6 08:49:37 1994`).  The parser is a plain recursive-descent one over the characters of
the value; it is total and reads each character once.

The grammar is case-sensitive, as section 5.6.7 says.  The day name is checked to be one of the
seven but not against the date, which section 5.6.7 does not ask for.  A date before 1970 counts
as 1970-01-01T00:00:00Z, since all the planner does with a date is wait until it has passed.
-/

namespace LeanHttp.Call.RetryAfter

set_option linter.all true

/--
A parsed `Retry-After` value.
-/
inductive Value where
  /--
  `delay-seconds`: wait this many seconds after the response was received.
  -/
  | seconds (n : Nat)

  /--
  `HTTP-date`: wait until this time, in seconds since 1970-01-01T00:00:00Z.
  -/
  | date (epochSeconds : Nat)
deriving Repr, BEq, DecidableEq, Inhabited

/--
A parser over the characters of a field value: what it read and the characters left, or `none`.
-/
abbrev Parser (α : Type) := List Char → Option (α × List Char)

/--
Reads exactly `n` decimal digits, as a number.
-/
def digits : Nat → Parser Nat
  | 0 => fun cs => some (0, cs)
  | n + 1 => fun cs =>
    match cs with
    | c :: rest =>
      if c.isDigit then
        (digits n rest).map fun (v, rest) => ((c.toNat - '0'.toNat) * 10 ^ n + v, rest)
      else none
    | [] => none

/--
Reads the characters of `s`, exactly.
-/
def lit (s : List Char) : Parser Unit := fun cs =>
  if s.isPrefixOf cs then some ((), cs.drop s.length) else none

/--
Reads one of `words` and returns its index.
-/
def oneOf (words : List String) : Parser Nat := fun cs =>
  let rec go (i : Nat) : List String → Option (Nat × List Char)
    | [] => none
    | w :: ws => match lit w.toList cs with
      | some ((), rest) => some (i, rest)
      | none => go (i + 1) ws
  go 0 words

/--
`day-name` (section 5.6.7).
-/
def dayNames : List String := ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

/--
`day-name-l`, the long day names of the RFC 850 format.
-/
def longDayNames : List String :=
  ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

/--
`month`, numbered from 0.
-/
def monthNames : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/--
Whether `y` is a leap year of the Gregorian calendar.
-/
def isLeap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/--
The number of days in month `m` (1 to 12) of year `y`.
-/
def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 2 => if isLeap y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/--
Days from 0000-03-01 to the date (year at least 1, month 1 to 12), in the proleptic Gregorian
calendar: Howard Hinnant's `days_from_civil`, shifted so that every quantity is a natural number.
-/
def daysFromMarch0 (y m d : Nat) : Nat :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y % 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe

/--
Days from 0000-03-01 to 1970-01-01.
-/
def epochDays : Nat := 719468

/--
Seconds since 1970-01-01T00:00:00Z of a date and time, or 0 for an earlier one.
-/
def epochSeconds (y m d hh mm ss : Nat) : Nat :=
  (daysFromMarch0 y m d - epochDays) * 86400 + hh * 3600 + mm * 60 + ss

/--
The year in which a time given in seconds since 1970-01-01T00:00:00Z falls: Howard Hinnant's
`civil_from_days`.
-/
def yearOf (epochSec : Nat) : Nat :=
  let z := epochSec / 86400 + epochDays
  let era := z / 146097
  let doe := z % 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400
  if m ≤ 2 then y + 1 else y

/--
The year a two-digit RFC 850 year stands for (section 5.6.7): the year with those last two digits
nearest to the present without being more than 50 years in the future.
-/
def fullYear (twoDigits currentYear : Nat) : Nat :=
  let candidate := currentYear / 100 * 100 + twoDigits
  if candidate > currentYear + 50 then candidate - 100 else candidate

/--
Checks a date and time and converts it, or `none` when a field is out of range.  A second of 60 is
allowed, for a leap second.
-/
def checked (y m d hh mm ss : Nat) : Option Nat :=
  if 1 ≤ y && 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ daysInMonth y m && hh ≤ 23 && mm ≤ 59 && ss ≤ 60 then
    some (epochSeconds y m d hh mm ss)
  else none

/--
`time-of-day = hour ":" minute ":" second`, each two digits.
-/
def timeOfDay : Parser (Nat × Nat × Nat) := fun cs => do
  let (hh, cs) ← digits 2 cs
  let ((), cs) ← lit [':'] cs
  let (mm, cs) ← digits 2 cs
  let ((), cs) ← lit [':'] cs
  let (ss, cs) ← digits 2 cs
  return ((hh, mm, ss), cs)

/--
`IMF-fixdate = day-name "," SP date1 SP time-of-day SP GMT`, with `date1 = day SP month SP year`
(two, three and four characters).
-/
def imfFixdate : Parser Nat := fun cs => do
  let (_, cs) ← oneOf dayNames cs
  let ((), cs) ← lit [',', ' '] cs
  let (d, cs) ← digits 2 cs
  let ((), cs) ← lit [' '] cs
  let (m, cs) ← oneOf monthNames cs
  let ((), cs) ← lit [' '] cs
  let (y, cs) ← digits 4 cs
  let ((), cs) ← lit [' '] cs
  let ((hh, mm, ss), cs) ← timeOfDay cs
  let ((), cs) ← lit " GMT".toList cs
  return (← checked y (m + 1) d hh mm ss, cs)

/--
`rfc850-date = day-name-l "," SP date2 SP time-of-day SP GMT`, with
`date2 = day "-" month "-" 2DIGIT`.  The two-digit year is read relative to `currentYear`.
-/
def rfc850Date (currentYear : Nat) : Parser Nat := fun cs => do
  let (_, cs) ← oneOf longDayNames cs
  let ((), cs) ← lit [',', ' '] cs
  let (d, cs) ← digits 2 cs
  let ((), cs) ← lit ['-'] cs
  let (m, cs) ← oneOf monthNames cs
  let ((), cs) ← lit ['-'] cs
  let (yy, cs) ← digits 2 cs
  let ((), cs) ← lit [' '] cs
  let ((hh, mm, ss), cs) ← timeOfDay cs
  let ((), cs) ← lit " GMT".toList cs
  return (← checked (fullYear yy currentYear) (m + 1) d hh mm ss, cs)

/--
`asctime-date = day-name SP date3 SP time-of-day SP year`, with
`date3 = month SP ( 2DIGIT / ( SP DIGIT ))`.
-/
def asctimeDate : Parser Nat := fun cs => do
  let (_, cs) ← oneOf dayNames cs
  let ((), cs) ← lit [' '] cs
  let (m, cs) ← oneOf monthNames cs
  let ((), cs) ← lit [' '] cs
  let (d, cs) ← match cs with
    | ' ' :: rest => digits 1 rest
    | _ => digits 2 cs
  let ((), cs) ← lit [' '] cs
  let ((hh, mm, ss), cs) ← timeOfDay cs
  let ((), cs) ← lit [' '] cs
  let (y, cs) ← digits 4 cs
  return (← checked y (m + 1) d hh mm ss, cs)

/--
Whether `c` is optional whitespace (`OWS`: space or horizontal tab).
-/
def isOws (c : Char) : Bool := c == ' ' || c == '\t'

/--
Removes optional whitespace at both ends.
-/
def trimOws (cs : List Char) : List Char :=
  ((cs.dropWhile isOws).reverse.dropWhile isOws).reverse

/--
Parses an `HTTP-date` in any of its three formats, the whole of `cs`, as seconds since
1970-01-01T00:00:00Z.  `currentYear` places a two-digit year.
-/
def httpDate (currentYear : Nat) (cs : List Char) : Option Nat :=
  let whole (p : Parser Nat) : Option Nat :=
    match p cs with
    | some (v, []) => some v
    | _ => none
  (whole imfFixdate).orElse fun _ => (whole (rfc850Date currentYear)).orElse fun _ => whole asctimeDate

/--
Parses a `Retry-After` field value: `delay-seconds` (one or more digits) or an `HTTP-date`.
`nowSec`, the present in seconds since 1970-01-01T00:00:00Z, places a two-digit year.  Returns
`none` for anything else, which the planner treats as a missing field.
-/
def parse (value : String) (nowSec : Nat) : Option Value :=
  let cs := trimOws value.toList
  if !cs.isEmpty && cs.all Char.isDigit then
    some (.seconds (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0))
  else
    (httpDate (yearOf nowSec) cs).map .date

/--
How long to wait, in milliseconds: the seconds given, or the time from `referenceSec` until the date
given (zero if it has passed).
-/
def Value.delayMs (v : Value) (referenceSec : Nat) : Nat :=
  match v with
  | .seconds n => n * 1000
  | .date t => (t - referenceSec) * 1000

end LeanHttp.Call.RetryAfter
