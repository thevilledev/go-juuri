/-
Copyright (c) 2026 Ville Vesilehto
SPDX-License-Identifier: MPL-2.0

The executable model: runs a script of tree operations through the Lean
transcription (JuuriFormal/Tree.lean) and prints every result, one line per
command, in the format formal/conformance/conformance_test.go expects from
the Go implementation. Comparing the two outputs on random scripts checks
that the model the theorems are about is the code that ships.

Commands (keys in hex, `-` for the empty key; values are integers):

  C       commit            -> "ok"  (the model is persistent: a no-op)
  I k v   insert            -> "old v" | "new"
  D k     delete            -> "del v" | "miss"
  P k     delete prefix     -> "true" | "false"
  G k     get               -> "v" | "none"
  L k     longest prefix    -> "v" | "none"
  F k     first with prefix -> "v" | "none"
  Z k     last with prefix  -> "v" | "none"
  S k     iterate from lower bound k            -> values
  R k     iterate down from reverse lower bound -> values
  X k     iterate keys with prefix k            -> values
  Y k     iterate keys with prefix k, reversed  -> values
  N       number of keys
-/
import JuuriFormal.Tree

open JuuriFormal Node

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

partial def parseHex : List Char → Option Key
  | [] => some []
  | a :: b :: rest => do
    let x ← hexVal a
    let y ← hexVal b
    let r ← parseHex rest
    pure ((16 * x + y) :: r)
  | _ => none

def parseKey (s : String) : Option Key :=
  if s = "-" then some [] else parseHex s.toList

def showOpt : Option Nat → String
  | some v => toString v
  | none => "none"

def showVals (l : List (Option Nat)) : String :=
  " ".intercalate (l.map showOpt)

def fuelFor (t : Node Nat) : Nat := 4 * size t + 4

def step (t : Node Nat) (line : String) : Node Nat × String :=
  match (line.splitOn " ").filter (· ≠ "") with
  | ["I", k, v] =>
    match parseKey k, v.toNat? with
    | some k, some v =>
      let (t', old) := insert t k v
      (t', match old with | some o => s!"old {o}" | none => "new")
    | _, _ => (t, "bad")
  | ["D", k] =>
    match parseKey k with
    | some k =>
      match delete true t k with
      | some (some t', v) => (t', s!"del {v}")
      | some (none, _) => (t, "root removed")
      | none => (t, "miss")
    | none => (t, "bad")
  | ["P", k] =>
    match parseKey k with
    | some k =>
      match deletePrefix true t k with
      | some (some t') => (t', "true")
      | some none => (t, "root removed")
      | none => (t, "false")
    | none => (t, "bad")
  | ["G", k] => (t, match parseKey k with | some k => showOpt (get t k) | none => "bad")
  | ["L", k] => (t, match parseKey k with | some k => showOpt (longestPrefix t k none) | none => "bad")
  | ["F", k] => (t, match parseKey k with | some k => showOpt (firstPrefix t k) | none => "bad")
  | ["Z", k] => (t, match parseKey k with | some k => showOpt (lastPrefix t k) | none => "bad")
  | ["S", k] =>
    (t, match parseKey k with
      | some k => showVals (run nextStep (fuelFor t) (seekLowerBound t k []))
      | none => "bad")
  | ["R", k] =>
    (t, match parseKey k with
      | some k => showVals (run prevStep (fuelFor t) (seekReverseLowerBound t k []))
      | none => "bad")
  | ["X", k] =>
    (t, match parseKey k with
      | some k => showVals (run nextStep (fuelFor t) (seekPrefixFwd t k))
      | none => "bad")
  | ["Y", k] =>
    (t, match parseKey k with
      | some k => showVals (run prevStep (fuelFor t) (seekPrefixRev t k))
      | none => "bad")
  | ["N"] => (t, toString (entries t).length)
  | ["C"] => (t, "ok")
  | _ => (t, "bad")

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (t : Node Nat) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimRight
  if line.isEmpty then loop stdin stdout t
  else
    let (t', out) := step t line
    stdout.putStrLn out
    loop stdin stdout t'

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout (.mk [] none [])
  stdout.flush
