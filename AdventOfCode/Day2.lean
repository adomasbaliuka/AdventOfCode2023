import Mathlib.Tactic
-- =============================================================== helpers

def splitLines (s : String) : List String
    :=
    let s := s.stripPrefix "\n"
    let s := s.stripSuffix "\n"
    s.splitOn "\n"


namespace Day2 -- ================================================== Day 2


structure Bag where
    red : ℕ
    green : ℕ
    blue : ℕ
deriving DecidableEq, Repr, Inhabited

instance instToStringBag : ToString Bag where
    toString := fun b ↦ s!"({b.red}, {b.green}, {b.blue})"

inductive Color
| Red
| Green
| Blue
deriving DecidableEq, Repr, Fintype, Inhabited
open Color

/-
A bag `lhs` is a subset of a bag `rhs` if `rhs` contains at least as many cubes
of each each color.
-/
def Bag.isSubset (lhs rhs : Bag) : Prop :=
    lhs.red ≤ rhs.red ∧ lhs.green ≤ rhs.green ∧ lhs.blue ≤ rhs.blue

-- Allows writing `(b1 : Bag) ⊆ (b2 : Bag)`
instance instHasSubsetBag : HasSubset Bag where
    Subset := Bag.isSubset

-- Allows evaluating `(b1 : Bag) ⊆ (b2 : Bag)` to `Bool`
instance instDecidableHasSubsetBag (lhs rhs : Bag) : Decidable (lhs ⊆ rhs) := by
    simp [Subset, Bag.isSubset]
    infer_instance

/- Parse first natural number from start of string.
Return unparsed rest of string.-/
def parseNatEat (s : String) : (Option ℕ) × String :=
    let firstNondigitIdx := Id.run do
        for i in [0:s.length] do
            if !Char.isDigit (s.get ⟨i⟩) then return i
        return s.length
    let nat := s.extract ⟨0⟩ ⟨firstNondigitIdx⟩ |> String.toNat?
    match nat with
    | some n => ⟨some n, s.extract ⟨firstNondigitIdx⟩ ⟨s.length⟩⟩
    | none => ⟨none, s⟩

/- Parse color. Return unparsed rest of string. -/
def parseColorEat (s : String) : (Option Color) × String :=
    if s.startsWith "red" then (pure Red, s.extract ⟨3⟩ ⟨s.length⟩)
    else if s.startsWith "green" then (pure Green, s.extract ⟨5⟩ ⟨s.length⟩)
    else if s.startsWith "blue" then (pure Blue, s.extract ⟨4⟩ ⟨s.length⟩)
    else (none, s)

def dropLeftWhitespaceCommaColon (s : String) : String :=
    let condition (c : Char) := c.isWhitespace ∨ c == ',' ∨ c == ':'
    s.toSubstring.dropWhile condition |> toString

def dropLeftWhitespaceSemicolon (s : String) : String :=
    let condition (c : Char) := c.isWhitespace ∨ c == ';'
    s.toSubstring.dropWhile condition |> toString

def parseNatColorEat (s_ : String) : (Option (Nat × Color)) × String :=
    let s := dropLeftWhitespaceCommaColon s_
    let ⟨n, s⟩ := parseNatEat s
    let s := s.trimLeft
    let ⟨color, s⟩ := parseColorEat s
    match n, color with
    | some n, some color => ((some (n, color)), s)
    | _, _ => (none, s_)

def Bag.update (b : Bag) (data : ℕ × Color) : Bag :=
    match data.2 with
    | Red => {red:=data.1, green:=b.green, blue:=b.blue}
    | Green => {red:=b.red, green:=data.1, blue:=b.blue}
    | Blue => {red:=b.red, green:=b.green, blue:=data.1}

def parseBagEat (s_ : String) : (Option Bag) × String :=
    let s := dropLeftWhitespaceSemicolon s_
    let ⟨natcolor?, s⟩ := parseNatColorEat s
    match natcolor? with
    | none => ⟨none, s_⟩
    | some valColor =>
        let bag : Bag := Bag.update ⟨0,0,0⟩ valColor
        let ⟨natcolor?, s⟩ := parseNatColorEat s
        match natcolor? with
        | none => ⟨bag, s⟩
        | some valColor =>
            let bag := bag.update valColor
            let ⟨natcolor?, s⟩ := parseNatColorEat s
            match natcolor? with
            | none => ⟨bag, s⟩
            | some valColor =>
                ⟨bag.update valColor, s⟩

def parseLine (s : String) : Option (ℕ × List Bag)
:= do
    let start := s.extract ⟨0⟩ ⟨5⟩
    if start != "Game " then none else
    let s := s.extract ⟨5⟩ ⟨s.length⟩
    let ⟨n, s⟩ := parseNatEat s
    let gameN ← n
    -- parse bags until end... don't know how to do it in a nice way
    Id.run do
        let mut bags : List Bag := []
        let mut s := s
        let upperBound := s.length -- trivial upper bound on number of bags
        for _ in [0:upperBound] do
            let ⟨currBag, tmp⟩ := parseBagEat s
            s := tmp
            match currBag with
            | none => return some ⟨gameN, bags⟩
            | some currBag => bags := currBag :: bags
        return some (gameN, [])


def bagTotal : Bag := ⟨12, 13, 14⟩

def Bag.isPossible (b : Bag) : Bool := b ⊆ bagTotal

def isPossible (bags : List Bag) : Bool := ∀b ∈ bags, b.isPossible

def input := "
Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green
"

def result : ℕ :=
    let allGames := (input |> splitLines).map parseLine
    let possibleGameIdsToSum := allGames.map
        (fun idBags? ↦
            match idBags? with
            | none => 0 -- summing zero later is like dropping them
            | some ⟨id, bags⟩ => if isPossible bags then id else 0)
    possibleGameIdsToSum.sum


#guard result == 8

-- part 2

def Bag.power (b : Bag) : ℕ := b.red * b.green * b.blue

def Bag.inter (b1 b2 : Bag) : Bag :=
        {red:=max b1.red b2.red, green:=max b1.green b2.green, blue:=max b1.blue b2.blue}

def result2 (input : String) : Option ℕ
:= do
    let allGames ← ((input |> splitLines).map parseLine).allSome
    let minimalBags ← (allGames.map (fun idxBag ↦ do
        let bags := idxBag.2
        let bag0 ← bags.get? 0
        some (bags.foldl Bag.inter bag0)
        )).allSome
    pure (minimalBags.map Bag.power).sum


#guard result2 input == some 2286
