import Leanify.Library.Core

/-! # Vocabulary: the Gregorian calendar

Leap years, month lengths and weekdays by arithmetic (`We write $w(d,m,y)$ for the day of the
week of the day $d$ of month $m$ of the year $y$.`).

* nouns and modifiers: `leap year` (an integer divisible by `4`, and by `400` if by `100`).
* notions: the number of days `365` or `366` of a year and of a month (`28` to `31`); the day
  of the week of a date by Zeller's congruence, `0` for Saturday to `6` for Friday; the number
  `⌊y/4⌋ - ⌊y/100⌋ + ⌊y/400⌋` of leap years among `1, …, y`.

Every meaning is a term of the core language. -/

namespace Leanify.Calendar
open Build Core

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def divBy (k y : B) : B := isInt (div y k)
def leap (y : B) : B := and (isInt y) (and (divBy (num 4) y) (or (not (divBy (num 100) y)) (divBy (num 400) y)))
def leapTm : Tm := predR leap
def month (m : B) : B := and (isInt m) (and (le (num 1) m) (le m (num 12)))
def modB (a k : B) : B := sub a (mul k (floor (div a k)))
def ind (p : B) : B := cases p (num 1) (num 0)
def daysIn (m y : B) : B :=
  cases (eq m (num 2)) (add (num 28) (ind (leap y)))
    (cases (or (or (eq m (num 4)) (eq m (num 6))) (or (eq m (num 9)) (eq m (num 11)))) (num 30) (num 31))
/-- Zeller: January and February count as months 13 and 14 of the year before. -/
def zeller (d m y : B) : B :=
  let mm := cases (lt m (num 3)) (add m (num 12)) m
  let yy := cases (lt m (num 3)) (sub y (num 1)) y
  let k := modB yy (num 100)
  let j := floor (div yy (num 100))
  modB (add (add (add d (floor (div (mul (num 13) (add mm (num 1))) (num 5)))) (add k (floor (div k (num 4)))))
    (add (floor (div j (num 4))) (mul (num 5) j))) (num 7)

def vocab : Vocab where
  nouns := [noun phrase!"leap year" phrase!"leap years" leapTm "an integer divisible by `4`, and by `400` if it is divisible by `100`"]
  mods := [{ phrase := phrase!"leap year", prenominal := false, ty := .real, pred := leapTm,
             doc := "divisible by `4`, and by `400` if divisible by `100`" }]
  notions := [
    { name := phrase!"number of days of the year $v$", ty := .real ⟶ .real, doms := [dom1 .real isInt],
      doc := "`366` for a leap year, `365` otherwise",
      value := close <| lamT .real isInt fun y => add (num 365) (ind (leap y)) },
    { name := phrase!"number of days of month $v$ of the year $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real month, dom2 .real fun _ y => isInt y], doc := "`28` to `31`",
      value := close <| lamT .real month fun m => lamT .real isInt fun y => daysIn m y },
    { name := phrase!"day of the week of the day $v$ of month $v$ of the year $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun d m => and (month m) (le d (num 31)), dom3 .real fun d m y => and (isInt y) (le d (daysIn m y))],
      doc := "Zeller's congruence: `0` for Saturday, `1` for Sunday, …, `6` for Friday",
      value := close <| lamT .real posInt fun d => lamT .real (fun m => and (month m) (le d (num 31))) fun m =>
        lamT .real (fun y => and (isInt y) (le d (daysIn m y))) fun y => zeller d m y },
    { name := phrase!"number of leap years up to the year $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`⌊y/4⌋ - ⌊y/100⌋ + ⌊y/400⌋`",
      value := close <| lamT .real posInt fun y =>
        add (sub (floor (div y (num 4))) (floor (div y (num 100)))) (floor (div y (num 400))) }]

end Leanify.Calendar
