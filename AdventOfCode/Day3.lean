import Mathlib.Tactic -- not actually using Mathlib. TODO fix imports

open System Lean

-- =============================================================== helpers

def splitLines (s : String) : List String
    :=
    let s := s.stripPrefix "\n"
    let s := s.stripSuffix "\n"
    s.splitOn "\n"

-- This is now basically a `Lean.Parsec`. Will use `Parsec` in next day maybe...
/- Parse one natural number from position.-/
def parseNat (s : String.Iterator) : (Option ℕ) × String.Iterator :=
    let firstNondigitIdx : ℕ := Id.run do
        for i in [s.i.byteIdx : s.s.length] do
            if !Char.isDigit (s.s.get ⟨i⟩) then return i
        return s.s.length
    let nat := s.s.extract s.i ⟨firstNondigitIdx⟩ |> String.toNat?
    match nat with
    | some n => ⟨some n, ⟨s.s, ⟨firstNondigitIdx⟩⟩⟩
    | none => ⟨none, s⟩

namespace Day3 -- ================================================== Day 3

structure Symbol where
x : Nat
y : Nat
isStar : Bool
deriving Repr, BEq

structure Number where
n : Nat
startx : Nat
endx : Nat
y : Nat
deriving Repr, BEq

inductive Obj
| Num : Number → Obj
| Period
| Symbol : Symbol → Obj -- any character besides [0-9] and '.'!
deriving Repr

instance instToStringObj : ToString Obj where
    toString : Obj → String
    | .Num n => s!"{n.n}"
    | .Period => "."
    | .Symbol _ => "#"

/- Parse one `Obj`.
Returns `none` result only for empty input. -/
def parseObj (s : String.Iterator) (lineIdx : Nat) : (Option Obj) × String.Iterator :=
Id.run do
    -- check if iterator is valid
    if s.i.byteIdx + 1 ≥ s.s.length then return (none, s)
    let c := s.curr -- result known from first char
    if c == '.' then return ⟨Obj.Period, s.next⟩ -- Period
    if c.isDigit then -- Num
        let ⟨n, s'⟩ := parseNat s
        let num : Option Number := do some {
            n:=(←n), startx:=s.i.byteIdx, endx:=s'.i.byteIdx, y:=lineIdx}
        let obj? : Option Obj := do some (Obj.Num (←num))
        return (obj?, s')
    -- Symbol
    let symbol : Symbol := ⟨s.i.byteIdx, lineIdx, c == '*'⟩
    let symbol' : Option Obj := do some (Obj.Symbol symbol)
    return (symbol', s.next)

-- set_option trace.Meta.synthInstance true in
-- #eval (parseObj "asdf".iter (99)).2 |> (parseObj · 5)

def Symbol.isAdjacent (s : Symbol) (n : Number) : Bool :=
    |(s.y : ℤ) - n.y| ≤ 1
    ∧ s.x ≤ n.endx
    ∧ s.x + 1 ≥ n.startx

def isAnySymbolAdjacent (ss : List Obj) (n : Obj) : Bool :=
    match n with
    | .Num n =>
        ss.any fun s ↦ (match s with
            | .Symbol s => s.isAdjacent n
            | _ => false
        )
    | _ => false

def parseLine (lineIdx : ℕ) (s : String) : List Obj := Id.run do
    let mut result : List Obj := []
    let mut sIt : String.Iterator := s.iter
    for _ in [0:s.length] do -- trivial upper bound
        let (obj?, it) := parseObj sIt lineIdx
        -- dbg_trace s!"{obj?}"
        -- dbg_trace s!"{it.curr}"
        -- dbg_trace s!"{result}"
        sIt := it
        match obj? with
        | none => return result
        | some obj =>
            result := obj :: result
            ()
    return [] -- unreachable code

def Obj.isNum : Obj → Bool
    | .Num _ => true
    | _ => false

def Obj.isStar : Obj → Bool
    | .Symbol s => s.isStar
    | _ => false


def l1 := parseLine 0 "467..114.."
def l2 := parseLine 1 "...*......"

def Obj.num : Obj → Nat
    | .Num n => n.n
    | _ => 0

def Obj.numO : Obj → Option Number
    | .Num n => some n
    | _ => none


def input := "
467..114..
...*......
..35..633.
......#...
617*......
.....+.58.
..592.....
......755.
...$.*....
.664.598..
"

def partNumbers (input : String) : List Number :=
    let lines := input |> splitLines
    Id.run do
        let mut partNumbers : List Number := []
        for i in [0:lines.length] do
            let prevL := if i > 0 then lines.get! (i-1) else ""
            let currL := lines.get! i    -- TODO not nice!
            let nextL :=  if i + 1 < lines.length then lines.get! (i+1) else ""
            let nums := (parseLine i currL).filter Obj.isNum
            let surrObjs := (parseLine (i-1) prevL)
                ++ (parseLine i currL)
                ++ (parseLine (i+1) nextL)
            let partNumObjs := nums.filter (fun num ↦
                isAnySymbolAdjacent surrObjs num)
            let newPartNumbers := (partNumObjs.map Obj.numO).allSome
            match newPartNumbers with
            | some L => partNumbers := L ++ partNumbers
            | none => ()
        return partNumbers


def result (input : String) : Nat := ((partNumbers input).map Number.n).sum

#guard result input == 4361


-- part 2

def filterStars (l : List Obj) : List Symbol := do
    match (←l) with
    | .Symbol s => if s.isStar then [s] else []
    | _ => []


def result2 (input : String) : Nat :=
    let lines := input |> splitLines
    let partNumbers := partNumbers input
    Id.run do
        let mut result : Nat := 0
        for i in [0:lines.length] do
            let currL := lines.get! i  -- TODO not nice!
            let stars := filterStars (parseLine i currL)
            let gearRatios : List Nat := stars.map (fun s ↦
                let adjPartNums := partNumbers.filter (Symbol.isAdjacent s ·)
                match adjPartNums with
                | [pn1, pn2] => pn1.n * pn2.n
                | _ => 0
                )
            result := result + gearRatios.sum
        return result

#guard result2 input == 467835
