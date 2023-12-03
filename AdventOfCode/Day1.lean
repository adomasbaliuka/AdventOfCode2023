import Std.Data.String.Basic

-- =============================================================== helpers

def splitLines (s : String) : List String
    :=
    let s := s.stripPrefix "\n"
    let s := s.stripSuffix "\n"
    s.splitOn "\n"

namespace Day1 -- ================================================== Day 1

def input := "
1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet
"

def numsFromFirstLastDigit (lines : List String) : List (Option Nat) :=
    let digits_perline := lines.map ((List.filter (Char.isDigit)) ∘ String.data)
    let first := digits_perline.map (List.get? · 0)
    let last := digits_perline.map (fun chars ↦
        (List.get? chars (chars.length-1)))
    (first.zip last).map (fun (char1?, char2?) ↦ do
        let c1 ← char1?
        let c2 ← char2?
        pure ((←c1.toString.toNat?)*10 + (←c2.toString.toNat?))
    )

def result : Option Nat := do
    let nums := input |> splitLines |> numsFromFirstLastDigit
    Nat.sum (←nums.allSome)

#guard result == some 142


-- part 2

def inputpart2 := "
two1nine
eightwothree
abcone2threexyz
xtwone3four
4nineeightseven2
zoneight234
7pqrstsixteen
"

def parsenumFromstart (s : String) : Option Nat := do
    let c0 := ←(s.get? 0)
    if c0.isDigit then
        c0.toString.toNat?
    else
        if s.startsWith "one" then pure 1
        else if s.startsWith "two" then pure 2
        else if s.startsWith "three" then pure 3
        else if s.startsWith "four" then pure 4
        else if s.startsWith "five" then pure 5
        else if s.startsWith "six" then pure 6
        else if s.startsWith "seven" then pure 7
        else if s.startsWith "eight" then pure 8
        else if s.startsWith "nine" then pure 9
        else none

def firstNum (s : String) : Option Nat := do
    for i in [0:s.length] do
        let stopPos := s.length
        let parsed := parsenumFromstart (s.extract ⟨i⟩ ⟨stopPos⟩)
        if parsed.isSome then return (←parsed)
    failure

def lastNum (s : String) : Option Nat := do
    for i in [0:s.length+1] do
        let startPos := s.length - i
        let parsed := parsenumFromstart (s.extract ⟨startPos⟩ ⟨s.length⟩)
        if parsed.isSome then return (←parsed)
    failure

def twodigitNum (s : String) : Option Nat := do (←firstNum s) * 10 + (←lastNum s)

def sumFirstLastTwodigit (lines : List String) : Option Nat
    := do
    let nums := (lines.map twodigitNum).allSome
    Nat.sum (←nums)

#guard (inputpart2 |> splitLines |> sumFirstLastTwodigit)
        == pure 281
