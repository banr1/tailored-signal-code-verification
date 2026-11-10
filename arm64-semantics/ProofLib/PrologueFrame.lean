/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.SepLogic

/-!
# Prologue Stack-Frame Inference and Symbol-Keyed Stack Frames

Static analyzer inferring downward stack-frame allocations from AArch64 function prologues,
kernel-reducible $O(N \log N)$ merge sort and `.text` symbol span helpers, and the
`HasFnFrameBytes` typeclass backing `stackFrameFor`.
-/

namespace Arm64

@[expose] public section

/-- Effect of a 32-bit AArch64 instruction word on `SP` during prologue analysis. -/
inductive SpEffect where
  | none
  | alloc (delta : Nat)
  | dealloc (delta : Nat)
  | unknown
  deriving DecidableEq, Repr, Inhabited

/-- Control-flow classification of a 32-bit AArch64 instruction word for prologue analysis. -/
inductive FlowKind where
  | normal
  | endPrologue
  | fwdCond (targetIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- State of the prologue stack-frame analyzer. -/
inductive PrologueState where
  | before (minFwd : Option Nat)
  | inPrologue (acc : Nat) (minFwd : Option Nat)
  | after (acc : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Group a byte list into 32-bit little-endian instruction words. -/
def wordsOfBytes : List (BitVec 8) → List (BitVec 32)
  | b0 :: b1 :: b2 :: b3 :: rest => (b3 ++ b2 ++ b1 ++ b0) :: wordsOfBytes rest
  | _ => []

/-- Classify how a 32-bit AArch64 instruction word `w` modifies `SP`. -/
def classifySpWord (w : BitVec 32) : SpEffect :=
  let wn := w.toNat
  if (wn &&& 0xff8003ff) == 0xd10003ff then
    let sh := (wn >>> 22) &&& 1
    let imm12 := (wn >>> 10) &&& 0xfff
    let delta := if sh == 1 then imm12 <<< 12 else imm12
    if delta > 0 then .alloc delta else .none
  else if (wn &&& 0xff8003ff) == 0x910003ff then
    let sh := (wn >>> 22) &&& 1
    let imm12 := (wn >>> 10) &&& 0xfff
    let delta := if sh == 1 then imm12 <<< 12 else imm12
    if delta > 0 then .dealloc delta else .none
  else if (wn &&& 0x3a0003e0) == 0x280003e0 then
    let idxMode := (wn >>> 23) &&& 3
    if idxMode != 3 && idxMode != 1 then .none
    else
      let opc := (wn >>> 30) &&& 3
      let v := (wn >>> 26) &&& 1
      let l := (wn >>> 22) &&& 1
      let imm7 := (wn >>> 15) &&& 0x7f
      let scale? : Option Nat :=
        if v == 0 then
          if opc == 0 then some 2 else if opc == 2 then some 3 else none
        else
          if opc == 0 then some 2 else if opc == 1 then some 3 else if opc == 2 then some 4 else none
      match scale? with
      | none => .unknown
      | some scale =>
        if idxMode == 3 && l == 0 && imm7 >= 64 then .alloc ((128 - imm7) <<< scale)
        else if idxMode == 1 && l == 1 && imm7 > 0 && imm7 < 64 then .dealloc (imm7 <<< scale)
        else .unknown
  else if (wn &&& 0x3b2003e0) == 0x380003e0 then
    let idxMode := (wn >>> 10) &&& 3
    if idxMode != 3 && idxMode != 1 then .none
    else
      let opc := (wn >>> 22) &&& 3
      let imm9 := (wn >>> 12) &&& 0x1ff
      if idxMode == 3 && opc == 0 && imm9 >= 256 then .alloc (512 - imm9)
      else if idxMode == 1 && opc != 0 && imm9 > 0 && imm9 < 256 then .dealloc imm9
      else .unknown
  else if wn == 0x910003bf then .dealloc 0
  else if (wn &&& 0x3f00001f) == 0x1100001f then .unknown
  else if (wn &&& 0x3f20001f) == 0x0b20001f then .unknown
  else if (wn &&& 0x1f80001f) == 0x1200001f && ((wn >>> 29) &&& 3) != 3 then .unknown
  else .none

/-- Classify the control-flow behavior of instruction word `w` at word index `idx`. -/
def classifyFlowWord (w : BitVec 32) (idx : Nat) : FlowKind :=
  let wn := w.toNat
  if (wn &&& 0xfc000000) == 0x94000000 || (wn &&& 0xfc000000) == 0x14000000 then .endPrologue
  else if (wn &&& 0xfffffc1f) == 0xd63f0000 || (wn &&& 0xfffffc1f) == 0xd61f0000 ||
          (wn &&& 0xfffffc1f) == 0xd65f0000 then .endPrologue
  else if (wn &&& 0xff000010) == 0x54000000 || (wn &&& 0x7e000000) == 0x34000000 then
    let imm19 := (wn >>> 5) &&& 0x7ffff
    if imm19 == 0 || imm19 >= 0x40000 then .endPrologue else .fwdCond (idx + imm19)
  else if (wn &&& 0x7e000000) == 0x36000000 then
    let imm14 := (wn >>> 5) &&& 0x3fff
    if imm14 == 0 || imm14 >= 0x2000 then .endPrologue else .fwdCond (idx + imm14)
  else .normal

/-- Whether word index `idx` has reached or passed `minFwd`. -/
def pastMinFwd (idx : Nat) : Option Nat → Bool
  | some t => idx >= t
  | none => false

/-- Step the prologue stack-frame analyzer over a list of instruction words. -/
def inferPrologueWords (idx : Nat) (state : PrologueState) : List (BitVec 32) → Option Nat
  | [] =>
    let total? := match state with
      | .before _ => some 0
      | .inPrologue acc minFwd => if pastMinFwd idx minFwd then none else some acc
      | .after acc => some acc
    match total? with
    | some total => if total % 16 == 0 then some total else none
    | none => none
  | w :: ws =>
    let state : PrologueState := match state with
      | .inPrologue acc minFwd =>
        if pastMinFwd idx minFwd then .after acc else .inPrologue acc minFwd
      | s => s
    let nextState? : Option PrologueState :=
      match state, classifySpWord w with
      | _, .unknown => none
      | .before minFwd, .alloc d =>
        if pastMinFwd idx minFwd then none else some (.inPrologue d minFwd)
      | .inPrologue acc minFwd, .alloc d =>
        some (.inPrologue (acc + d) minFwd)
      | .after _, .alloc _ => none
      | .before _, .dealloc _ => none
      | .inPrologue acc _, .dealloc _ => some (.after acc)
      | .after acc, .dealloc _ => some (.after acc)
      | .before minFwd, .none =>
        match classifyFlowWord w idx with
        | .normal => some (.before minFwd)
        | .endPrologue => some (.after 0)
        | .fwdCond targetIdx =>
          let nextMin := match minFwd with
            | some t => some (Nat.min t targetIdx)
            | none => some targetIdx
          some (.before nextMin)
      | .inPrologue acc minFwd, .none =>
        match classifyFlowWord w idx with
        | .normal => some (.inPrologue acc minFwd)
        | .endPrologue | .fwdCond _ => some (.after acc)
      | .after acc, .none => some (.after acc)
    match nextState? with
    | some nextState => inferPrologueWords (idx + 1) nextState ws
    | none => none

/-- Drop leading `0x00000000` words from a reversed word list (keeping at least one word if non-empty). -/
def dropLeadingZeroWords : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | [w] => [w]
  | w :: rest => if w == 0#32 then dropLeadingZeroWords rest else w :: rest

/-- Drop trailing `0x00000000` padding words (keeping at least one word if non-empty). -/
def trimTrailingZeroWords (ws : List (BitVec 32)) : List (BitVec 32) :=
  (dropLeadingZeroWords ws.reverse).reverse

/-- Infer the downward stack frame size in bytes allocated by a function's prologue from its
    raw code bytes (`some 0` for leaf functions that do not allocate a frame; `none` if the
    function uses dynamic/non-standard `SP` adjustments or has a misaligned frame). -/
def inferPrologueFrameBytes? (bs : List (BitVec 8)) : Option Nat :=
  if bs.length % 4 != 0 then none
  else inferPrologueWords 0 (.before none) (trimTrailingZeroWords (wordsOfBytes bs))

/-- Smallest offset in `stubs` at most `best` (`best` if none). -/
def Obj.minStubOff (best : Nat) : List (String × Nat) → Nat
  | [] => best
  | (_, o) :: rest =>
    match Nat.ble best o with
    | true => Obj.minStubOff best rest
    | false => Obj.minStubOff o rest

/-- Fuel-bounded structural merge of two sorted runs. -/
def Obj.mergeRuns {α : Type} (le : α → α → Bool) :
    Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | fuel + 1, xs, ys =>
    match xs, ys with
    | [], ys => ys
    | xs, [] => xs
    | x :: xs', y :: ys' =>
      match le x y with
      | true => x :: Obj.mergeRuns le fuel xs' (y :: ys')
      | false => y :: Obj.mergeRuns le fuel (x :: xs') ys'

def Obj.mergePairsAux {α : Type} (le : α → α → Bool) :
    Option (List α) → List (List α) → List (List α)
  | acc, [] =>
    match acc with
    | none => []
    | some xs => [xs]
  | acc, ys :: rest =>
    match acc with
    | none => Obj.mergePairsAux le (some ys) rest
    | some xs =>
      Obj.mergeRuns le (xs.length + ys.length) xs ys ::
        Obj.mergePairsAux le none rest

/-- Merge adjacent pairs of runs in a single pass. -/
def Obj.mergePairs {α : Type} (le : α → α → Bool) (runs : List (List α)) :
    List (List α) :=
  Obj.mergePairsAux le none runs

def Obj.mergeAllFuel {α : Type} (le : α → α → Bool) :
    Nat → List (List α) → List α
  | 0, xs => xs.flatten
  | fuel + 1, xs =>
    match xs with
    | [] => []
    | [x] => x
    | _ => Obj.mergeAllFuel le fuel (Obj.mergePairs le xs)

/-- Structural bottom-up $O(N \log N)$ merge sort that reduces directly in kernel WHNF. -/
def Obj.sortList {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  Obj.mergeAllFuel le xs.length (xs.map fun x => [x])

/-- Tag elements with consecutive indices starting at `i`. -/
def Obj.tagWithIdx {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: Obj.tagWithIdx (i + 1) xs

/-- Walk `.text` `(idx, name, off)` triples ordered by non-decreasing `off` from right to left,
    pairing each symbol with `(idx, name, (off, nextHigherOff - off))`. -/
def Obj.assignSpans (textEnd : Nat) :
    List (Nat × String × Nat) → Nat × Nat × List (Nat × String × (Nat × Nat))
  | [] => (textEnd, textEnd, [])
  | (idx, name, off) :: rest =>
    match Obj.assignSpans textEnd rest with
    | (prevOff, nextHigher, acc) =>
      match Nat.blt off prevOff with
      | true => (off, prevOff, (idx, name, (off, prevOff - off)) :: acc)
      | false => (off, nextHigher, (idx, name, (off, nextHigher - off)) :: acc)

/-- Byte length of `bs` after stripping trailing 4-byte zero (`0x00000000`) padding words
    (keeping at least 4 bytes when non-empty). -/
def trimTrailingZeroBytesLen (bs : List (BitVec 8)) : Nat :=
  if bs.length % 4 != 0 then bs.length
  else 4 * (trimTrailingZeroWords (wordsOfBytes bs)).length

/-- Typeclass for containers providing a function's prologue stack-frame size in bytes by symbol
    name. -/
class HasFnFrameBytes (α : Type) where
  frameBytes : α → String → Nat

/-- Prologue stack frame size in bytes of function `name` in `src`. -/
def fnFrameBytes {α : Type} [HasFnFrameBytes α] (src : α) (name : String) : Nat :=
  HasFnFrameBytes.frameBytes src name

/-- Separation logic assertion for the prologue stack frame of function `name` in `src` at stack
    pointer `sp` (`[sp - fnFrameBytes src name, sp)`). -/
abbrev stackFrameFor {α : Type} [HasFnFrameBytes α] (src : α) (name : String) (sp : BitVec 64) :
    SepProp :=
  stackFrameAt sp (fnFrameBytes src name)

end

end Arm64
