import Std.Data.String.Basic

open Lean (Parsec)
open Lean.Parsec

namespace Day4

-- =============================================================== helpers

def splitLines (s : String) : List String
    :=
    let s := s.stripPrefix "\n"
    let s := s.stripSuffix "\n"
    s.splitOn "\n"

-- =============================================================== Day 4

def winningHaving (line : String) : Option (List Nat × List Nat) := do
    let afterColon ← (line.splitOn ":").get? 1
    let splitBar := afterColon.splitOn "|"
    let winning ← (((← splitBar.get? 0).splitOn " ").map String.toNat?).filter Option.isSome |> List.allSome
    let having ← (((← splitBar.get? 1).splitOn " ").map String.toNat?).filter Option.isSome |> List.allSome
    (winning, having)

def score (winning : List Nat) (having : List Nat) : Nat :=
    let nWinners := (having ∩ winning).length
    if nWinners == 0 then 0 else (Nat.pow 2 (nWinners-1))

def result (input : String) : Option Nat := do
    let winning_having ← ((input |> splitLines).map winningHaving).allSome
    let scores := winning_having.map (fun ⟨w, h⟩ ↦ score w h)
    Nat.sum scores

def input := "
Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11
"

#guard result input == some 13

-- part 2

structure Card where
idx : Nat
winning : List Nat
having : List Nat
deriving Repr

structure EvaluatedCard where
idx : Nat
nWinners : Nat
deriving Repr

instance : ToString EvaluatedCard where
    toString c := s!"<{c.idx}, {c.nWinners}>"

def Card.evaluate (c : Card) : EvaluatedCard :=
    let nWinners := (c.having ∩ c.winning).length
    ⟨c.idx, nWinners⟩

def Card.parse (line : String) : Option Card := do
    let idx ← (←((←(line.splitOn ":").get? 0).splitOn " ").getLast?).toNat?
    let afterColon ← (line.splitOn ":").get? 1
    let splitBar := afterColon.splitOn "|"
    let winning ← (((← splitBar.get? 0).splitOn " ").map String.toNat?).filter Option.isSome |> List.allSome
    let having ← (((← splitBar.get? 1).splitOn " ").map String.toNat?).filter Option.isSome |> List.allSome
    pure ⟨idx, winning, having⟩

def getCardByIdx (cards : List Card) (idx : Nat) : Option Card :=
    cards.filter (fun c : Card ↦
    match c with | ⟨i, _, _⟩ => i == idx
    ) |>.get? 0

def parseCards (input : String) : Option (List Card) := do
    ((input |> splitLines).map Card.parse).allSome

/- Unfortunately, this is too slow to solve the puzzle with big input :(
    TODO try with `Array` and tail recursion?
    Solved the puzzle with Julia instead, which is much easier :( -/
partial def doResult2 (cards : List EvaluatedCard) (acc : Nat) : List Card × Nat := Id.run do
match cards with
| [] => ([], acc)
| c :: cs =>
    -- dbg_trace "{cards.map EvaluatedCard.idx}. Work on {c.idx} with {c.nWinners} winners"
    let mut remainingCards := cs
    for i in [c.idx+1:c.idx+c.nWinners+1] do
        if let some take := (remainingCards.filter (·.idx == i)).get? 0 then
            -- dbg_trace s!"take {take}"
            remainingCards := remainingCards ++ [take]
    doResult2 remainingCards (acc + 1)
-- TODO prove termination...

def result2 (input : String) : Option Nat := do
    let cards := (←parseCards input).map Card.evaluate
    (doResult2 cards 0).2


#guard result2 input == some 30
