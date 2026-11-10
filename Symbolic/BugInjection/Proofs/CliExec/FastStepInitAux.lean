/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooks

/-!
# Pre-Decoded `FastProg` Table and Soundness

Defines `FastProg` and `PrebuiltElf`, which combine a depth-19 radix tree of hooked stub symbols
(`overlayHooks`) with shared 64-byte cache lines (`rxLines`) for on-demand instruction decoding
above `cliBase`. Proves `FastProgSound`, which relates `lookupStepEntry` to `Program.fetchMem` and
`Program.externAt?` across any memory transition that preserves frozen bytes (`Memory.KeepsFrozen`).
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastStepInitAux

set_option autoImplicit false

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks cliBase cliExternsAbortOnPanic)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
open Symbolic.BugInjection.Proofs.CliExec.FastHooks

/-- Word-index radix-tree depth (`2 ^ 19` 32-bit words = `2 MiB` above `cliBase`). -/
def progDepth : Nat := 19

def progWordBound : Nat := 2 ^ progDepth

def progByteBound : Nat := 4 * progWordBound

/-- Dispatch entry at word index `(pc - cliBase).toNat / 4`: decoded instruction, extern hook, or
unmapped. -/
inductive StepEntry where
  | instr (i : Arm64.Instr)
  | hook (name : String)
  | unmapped
  deriving Repr

/-- Program lookup tables above `cliBase`: `hooks` maps hooked stub word indices to symbol names,
and `rxLines` shares `baseLines` for on-demand instruction decoding. -/
structure FastProg where
  hooks   : BinTree String := .empty
  rxLines : BinTree Line64 := .empty
  deriving Repr

/-- Shared per-ELF prebuilt bundle: token-patched segment `baseLines` and `prog`. -/
structure PrebuiltElf where
  baseLines : BinTree Line64
  prog      : FastProg

private theorem cliBase_mod64 : cliBase.toNat % 64 = 0 := by
  simp [cliBase]

private theorem cliBase_mod4 : cliBase.toNat % 4 = 0 := by
  simp [cliBase]

private theorem cliBase_progByteBound_le : cliBase.toNat + progByteBound ≤ 2 ^ 48 := by
  simp [cliBase, progByteBound, progWordBound, progDepth]

/-- Decode 32-bit word `w < 16` of a 64-byte cache line `line` when all four bytes are executable
and non-writable (`Frozen`). -/
def decodeStepFromLine (line : Line64) (w : Nat) : StepEntry :=
  match btGet 6 line (4 * w), btGet 6 line (4 * w + 1),
        btGet 6 line (4 * w + 2), btGet 6 line (4 * w + 3) with
  | some (some p0, b0), some (some p1, b1), some (some p2, b2), some (some p3, b3) =>
    if p0.x && !p0.w && p1.x && !p1.w && p2.x && !p2.w && p3.x && !p3.w then
      match Arm64.decode (b3 ++ b2 ++ b1 ++ b0) with
      | some inst => .instr inst
      | none => .unmapped
    else .unmapped
  | _, _, _, _ => .unmapped

def withForcedUInt8List {α : Type} : List UInt8 → (List UInt8 → α) → α
  | [], k => k []
  | b :: bs, k => withForcedUInt8List bs fun bs' => k (b :: bs')

@[simp] private theorem withForcedUInt8List_eq {α : Type} (bs : List UInt8)
    (k : List UInt8 → α) : withForcedUInt8List bs k = k bs := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => exact ih (fun bs' => k (b :: bs'))

def withForcedNameTable {α : Type} : List (List UInt8) → (List (List UInt8) → α) → α
  | [], k => k []
  | nm :: nms, k =>
    withForcedUInt8List nm fun nm' =>
    withForcedNameTable nms fun nms' =>
      k (nm' :: nms')

@[simp] private theorem withForcedNameTable_eq {α : Type} (nms : List (List UInt8))
    (k : List (List UInt8) → α) : withForcedNameTable nms k = k nms := by
  induction nms generalizing k with
  | nil => rfl
  | cons nm nms ih =>
    simp only [withForcedNameTable, withForcedUInt8List_eq]
    exact ih (fun nms' => k (nm :: nms'))

def hookExactNamesBs (W : CliHooks) : List (List UInt8) :=
  panicAllExactNamesBs ++ ((fastHookTable W).map Prod.fst).map strUtf8Bytes

def hasHookBs (pfx : List UInt8) (tbl : List (List UInt8)) (bs : List UInt8) : Bool :=
  listUInt8IsPrefix pfx bs || tbl.any (fun p => listUInt8Eq bs p)

def overlayHooksAux (pfx : List UInt8) (tbl : List (List UInt8)) :
    List (String × Nat) → BinTree String → BinTree String
  | [], tr => tr
  | (name, o) :: rest, tr =>
    withForcedBinTree (overlayHooksAux pfx tbl rest tr) fun tr' =>
      if Nat.beq (Nat.mod o 4) 0 && Nat.blt (Nat.div o 4) progWordBound &&
          hasHookBs pfx tbl (strUtf8Bytes name) then
        btSet progDepth tr' (Nat.div o 4) name
      else
        tr'

/-- Insert hooked stubs from `stubs` in reverse order so earlier entries take precedence, as in
`Program.hookAtOff?`. -/
def overlayHooks (W : CliHooks) (stubs : List (String × Nat)) (tr : BinTree String) :
    BinTree String :=
  withForcedUInt8List panicPrefixBs fun pfx =>
  withForcedNameTable (hookExactNamesBs W) fun tbl =>
    overlayHooksAux pfx tbl stubs tr

/-- Look up word index `idx = (pc - cliBase).toNat / 4`: return `.hook` if present in `fp.hooks`,
otherwise decode from `fp.rxLines`. -/
def lookupStepEntry (fp : FastProg) (idx : Nat) : StepEntry :=
  match btGet progDepth fp.hooks idx with
  | some name => .hook name
  | none =>
    match btGet 58 fp.rxLines (Nat.add (Nat.div cliBase.toNat 64) (Nat.div idx 16)) with
    | some line => decodeStepFromLine line (Nat.mod idx 16)
    | none => .unmapped

/-- Construct a `FastProg` from `li.stubs` and `baseLines`. -/
def buildFastProgWithLens (W : CliHooks) (li : LinkedImage)
    (_regsWithLen : List (Snapshot.Region × Nat)) (baseLines : BinTree Line64) : FastProg :=
  withForcedBinTree (overlayHooks W li.stubs .empty) fun hk =>
    { hooks := hk, rxLines := baseLines }

def buildFastProg (W : CliHooks) (li : LinkedImage) (_elf : ElfImage)
    (baseLines : BinTree Line64) : FastProg :=
  buildFastProgWithLens W li [] baseLines

abbrev buildFastProg0 : LinkedImage → ElfImage → BinTree Line64 → FastProg :=
  buildFastProg compHooks0

/-- Agreement of `lookupStepEntry fp` with `Program.fetchMem` and `Program.externAt?` on
`li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)` for every memory `m` with
`m0.KeepsFrozen m`. -/
def FastProgSound (W : CliHooks) (li : LinkedImage) (fp : FastProg) (m0 : Memory) : Prop :=
  let prog := li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)
  ∀ (pc : BitVec 64) (m : Memory),
    m0.KeepsFrozen m →
    let off := (pc - cliBase).toNat
    off % 4 = 0 →
    off / 4 < progWordBound →
    match lookupStepEntry fp (off / 4) with
    | .instr inst => prog.fetchMem m pc = some inst
    | .hook name =>
        ∀ h, cliExternsAbortOnPanic W name = some h → prog.externAt? pc = some h
    | .unmapped => True

private def ByteExecRo (baseLines : BinTree Line64) (a : Nat) (p : Perm) (b : BitVec 8) : Prop :=
  rawCellAt baseLines a = some (some p, b) ∧ p.x = true ∧ p.w = false

private def BaseWordValid (baseLines : BinTree Line64) (idx : Nat) (e : StepEntry) : Prop :=
  match e with
  | .hook _ => False
  | .unmapped => True
  | .instr inst =>
    let addr := cliBase.toNat + 4 * idx
    ∃ (p0 : Perm) (b0 : BitVec 8) (p1 : Perm) (b1 : BitVec 8)
      (p2 : Perm) (b2 : BitVec 8) (p3 : Perm) (b3 : BitVec 8),
      ByteExecRo baseLines addr p0 b0 ∧
      ByteExecRo baseLines (addr + 1) p1 b1 ∧
      ByteExecRo baseLines (addr + 2) p2 b2 ∧
      ByteExecRo baseLines (addr + 3) p3 b3 ∧
      Arm64.decode (b3 ++ b2 ++ b1 ++ b0) = some inst

private theorem rawCellAt_block_word (baseLines : BinTree Line64) (block w j : Nat) (line : Line64)
    (hline : btGet 58 baseLines (cliBase.toNat / 64 + block) = some line)
    (hw : w < 16) (hj : j < 4) :
    rawCellAt baseLines (cliBase.toNat + 4 * (16 * block + w) + j) = btGet 6 line (4 * w + j) := by
  have hmod := cliBase_mod64
  set addr := cliBase.toNat + 4 * (16 * block + w) + j
  have hdiv : addr / 64 = cliBase.toNat / 64 + block := by omega
  have hrem : addr % 64 = 4 * w + j := by omega
  simp only [rawCellAt, hdiv, hline, hrem]

private theorem decodeStepFromLine_valid (baseLines : BinTree Line64) (block w : Nat) (line : Line64)
    (hline : btGet 58 baseLines (cliBase.toNat / 64 + block) = some line) (hw : w < 16) :
    BaseWordValid baseLines (16 * block + w) (decodeStepFromLine line w) := by
  unfold decodeStepFromLine
  have h0 := rawCellAt_block_word baseLines block w 0 line hline hw (by omega)
  have h1 := rawCellAt_block_word baseLines block w 1 line hline hw (by omega)
  have h2 := rawCellAt_block_word baseLines block w 2 line hline hw (by omega)
  have h3 := rawCellAt_block_word baseLines block w 3 line hline hw (by omega)
  simp only [Nat.add_zero] at h0
  rcases hc0 : btGet 6 line (4 * w) with _ | ⟨_ | p0, b0⟩
  · trivial
  · trivial
  · rcases hc1 : btGet 6 line (4 * w + 1) with _ | ⟨_ | p1, b1⟩
    · trivial
    · trivial
    · rcases hc2 : btGet 6 line (4 * w + 2) with _ | ⟨_ | p2, b2⟩
      · trivial
      · trivial
      · rcases hc3 : btGet 6 line (4 * w + 3) with _ | ⟨_ | p3, b3⟩
        · trivial
        · trivial
        · dsimp only
          split
          · rename_i hflags
            cases hdec : Arm64.decode (b3 ++ b2 ++ b1 ++ b0) with
            | none => trivial
            | some inst =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hflags
              rcases hflags with ⟨⟨⟨⟨⟨⟨⟨hx0, hw0⟩, hx1⟩, hw1⟩, hx2⟩, hw2⟩, hx3⟩, hw3⟩
              exact ⟨p0, b0, p1, b1, p2, b2, p3, b3,
                ⟨h0.trans hc0, hx0, hw0⟩, ⟨h1.trans hc1, hx1, hw1⟩,
                ⟨h2.trans hc2, hx2, hw2⟩, ⟨h3.trans hc3, hx3, hw3⟩, hdec⟩
          · trivial

private def hookStubAt? (W : CliHooks) (stubs : List (String × Nat)) (off : Nat) : Option String :=
  stubs.findSome? fun (n, o) => if o == off then (if hasCliHook W n then some n else none) else none

private theorem hookStubAt_cons (W : CliHooks) (name : String) (o : Nat)
    (rest : List (String × Nat)) (off : Nat) :
    hookStubAt? W ((name, o) :: rest) off =
      match if o == off then (if hasCliHook W name then some name else none) else none with
      | some b => some b
      | none => hookStubAt? W rest off := by
  unfold hookStubAt?
  rw [List.findSome?_cons]
  dsimp only
  cases o == off <;> cases hasCliHook W name <;> rfl

private theorem lookupStrUtf8_isSome {β : Type} (bs : List UInt8) :
    ∀ (tbl : List (String × β)),
      (lookupStrUtf8 bs tbl).isSome = ((tbl.map Prod.fst).map strUtf8Bytes).any (listUInt8Eq bs)
  | [] => rfl
  | (k, _) :: rest => by
    simp only [lookupStrUtf8, List.map_cons, List.any_cons]
    cases listUInt8Eq bs (strUtf8Bytes k) <;> simp [lookupStrUtf8_isSome bs rest]

private theorem hasHookBs_eq_hasCliHook (W : CliHooks) (name : String) :
    hasHookBs panicPrefixBs (hookExactNamesBs W) (strUtf8Bytes name) = hasCliHook W name := by
  unfold hasHookBs hookExactNamesBs hasCliHook fastExternRaw? fastIsImagePanicSymbolBs
  dsimp only
  rw [List.any_append, ← Bool.or_assoc]
  cases listUInt8IsPrefix panicPrefixBs (strUtf8Bytes name) ||
      panicAllExactNamesBs.any (fun p => listUInt8Eq (strUtf8Bytes name) p)
  · simp [lookupStrUtf8_isSome]
  · simp

private theorem overlayHooksAux_cond_eq (W : CliHooks) (name : String) (o : Nat) :
    (Nat.beq (Nat.mod o 4) 0 && Nat.blt (Nat.div o 4) progWordBound &&
      hasHookBs panicPrefixBs (hookExactNamesBs W) (strUtf8Bytes name)) =
    (o % 4 == 0 && decide (o / 4 < progWordBound) && hasCliHook W name) := by
  have hmod : Nat.mod o 4 = o % 4 := rfl
  have hdiv : Nat.div o 4 = o / 4 := rfl
  rw [hmod, hdiv, hasHookBs_eq_hasCliHook]
  have hbeq : Nat.beq (o % 4) 0 = (o % 4 == 0) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.beq_eq]
  have hblt : Nat.blt (o / 4) progWordBound = decide (o / 4 < progWordBound) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]
  rw [hbeq, hblt]

private theorem btGet_overlayHooks (W : CliHooks) (stubs : List (String × Nat))
    (tr : BinTree String) {idx : Nat} (hidx : idx < progWordBound) :
    btGet progDepth (overlayHooks W stubs tr) idx =
      match hookStubAt? W stubs (4 * idx) with
      | some name => some name
      | none => btGet progDepth tr idx := by
  simp only [overlayHooks, withForcedUInt8List_eq, withForcedNameTable_eq]
  induction stubs with
  | nil => simp [overlayHooksAux, hookStubAt?]
  | cons hd rest ih =>
    rcases hd with ⟨name, o⟩
    rw [hookStubAt_cons]
    have hdiv_eq : Nat.div o 4 = o / 4 := rfl
    simp only [overlayHooksAux, withForcedBinTree_eq]
    rw [overlayHooksAux_cond_eq, hdiv_eq]
    have hidx' : idx < 2 ^ progDepth := hidx
    by_cases hcond : (o % 4 == 0 && decide (o / 4 < progWordBound) && hasCliHook W name) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨hmod, hdiv_lt⟩, hhook⟩
      have ho_lt : o / 4 < 2 ^ progDepth := hdiv_lt
      by_cases heq : o / 4 = idx
      · have ho_eq : o = 4 * idx := by omega
        subst heq
        rw [btGet_btSet_same progDepth (o / 4) _ _ ho_lt]
        have hob : (o == 4 * (o / 4)) = true := beq_iff_eq.mpr ho_eq
        simp only [hob, hhook, ↓reduceIte]
      · have ho_ne : (o == 4 * idx) = false :=
          Bool.eq_false_iff.mpr fun hb => heq (by have := eq_of_beq hb; omega)
        rw [btGet_btSet_ne progDepth (o / 4) idx _ _ ho_lt hidx' heq, ih]
        simp only [ho_ne, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hcond
      simp only [hcond, Bool.false_eq_true, ↓reduceIte, ih]
      have hhead_none : (if o == 4 * idx then if hasCliHook W name then some name else none else none) = none := by
        by_cases ho : (o == 4 * idx) = true
        · have ho_eq : o = 4 * idx := eq_of_beq ho
          have hmod : (o % 4 == 0) = true := beq_iff_eq.mpr (by omega)
          have hlt : decide (o / 4 < progWordBound) = true := decide_eq_true (by omega)
          have hh_false : hasCliHook W name = false := by
            cases hh : hasCliHook W name
            · rfl
            · exfalso
              have : (o % 4 == 0 && decide (o / 4 < progWordBound) && hasCliHook W name) = true := by
                simp [hmod, hlt, hh]
              exact absurd this (by simpa using hcond)
          simp [ho, hh_false]
        · simp only [Bool.not_eq_true] at ho
          simp [ho]
      rw [hhead_none]

private theorem findSome_stubs_of_hookStubAt_some {W : CliHooks} {stubs : List (String × Nat)}
    {off : Nat} {name : String} {h : State → State}
    (hs : hookStubAt? W stubs off = some name)
    (hext : cliExternsAbortOnPanic W name = some h) :
    (stubs.findSome? fun (n, o) => if o == off then cliExternsAbortOnPanic W n else none) = some h := by
  induction stubs with
  | nil => simp [hookStubAt?] at hs
  | cons hd rest ih =>
    rcases hd with ⟨n, o⟩
    rw [hookStubAt_cons] at hs
    dsimp only [List.findSome?]
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at hs ⊢
      cases hh : hasCliHook W n with
      | true =>
        simp only [hh, ↓reduceIte] at hs
        injection hs with hs
        subst hs
        simp only [hext]
      | false =>
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at hs
        have hnone : cliExternsAbortOnPanic W n = none := by
          have his := hasCliHook_eq_isSome W n
          rw [hh] at his
          cases hc : cliExternsAbortOnPanic W n with
          | none => rfl
          | some _ => rw [hc] at his; cases his
        simp only [hnone]
        exact ih hs
    · simp only [Bool.not_eq_true] at ho
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact ih hs

private theorem findSome_stubs_of_hookStubAt_none {W : CliHooks} {stubs : List (String × Nat)}
    {off : Nat} (hs : hookStubAt? W stubs off = none) :
    (stubs.findSome? fun (n, o) => if o == off then cliExternsAbortOnPanic W n else none) = none := by
  induction stubs with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨n, o⟩
    rw [hookStubAt_cons] at hs
    dsimp only [List.findSome?]
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at hs ⊢
      cases hh : hasCliHook W n with
      | true => simp [hh] at hs
      | false =>
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at hs
        have hnone : cliExternsAbortOnPanic W n = none := by
          have his := hasCliHook_eq_isSome W n
          rw [hh] at his
          cases hc : cliExternsAbortOnPanic W n with
          | none => rfl
          | some _ => rw [hc] at his; cases his
        simp only [hnone]
        exact ih hs
    · simp only [Bool.not_eq_true] at ho
      simp only [ho, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact ih hs

private theorem symbols_findSome_none (syms : List (String × Nat)) :
    (syms.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
  induction syms with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem rebase_externAt_eq (W : CliHooks) (li : LinkedImage) (pc : BitVec 64) :
    (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)).externAt? pc =
      (li.stubs.findSome? fun (n, o) =>
        if o == (pc - cliBase).toNat then cliExternsAbortOnPanic W n else none) := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase, LinkedImage.toProgram]
  have hsym : (li.symbols.findSome? fun (x : String × Nat) =>
      if x.2 == (pc - cliBase).toNat then (none : Option (State → State)) else none) = none := by
    have : (fun (x : String × Nat) =>
        if x.2 == (pc - cliBase).toNat then (none : Option (State → State)) else none) =
        fun _ => none := by
      funext x; split <;> rfl
    rw [this]
    exact symbols_findSome_none li.symbols
  rw [hsym, Option.or_none]

private theorem cell_frozen_exec_read8 {m0 m : Memory} {a : BitVec 64} {p : Perm} {b : BitVec 8}
    (hkf : m0.KeepsFrozen m) (hcell : m0.cells a = some (some p, b))
    (hx : p.x = true) (hw : p.w = false) :
    (m.perm a).x = true ∧ m.read8 a = b := by
  have hm0_perm : m0.perm a = some p.rwx := by
    simp [Memory.perm, hcell]
  have hm0_read : m0.read8 a = b := by
    simp [Memory.read8, hcell]
  have hfrz : m0.Frozen a := by
    simp [Memory.Frozen, hm0_perm, Perm.frozen, Perm.rwx, hx, hw]
  rcases hkf a hfrz with ⟨hr, hp, _, _⟩
  rw [hp, hm0_perm]
  exact ⟨by simp [Perm.rwx, hx], hr.trans hm0_read⟩

private theorem pc_eq_cliBase_add_idx (pc : BitVec 64)
    (hmod4 : (pc - cliBase).toNat % 4 = 0) :
    pc = cliBase + BitVec.ofNat 64 (4 * ((pc - cliBase).toNat / 4)) := by
  have hoff : 4 * ((pc - cliBase).toNat / 4) = (pc - cliBase).toNat := by omega
  rw [hoff, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  have h1 := pc.isLt
  have h2 := cliBase.isLt
  omega

theorem fastProgSound_of_cells_agree (W : CliHooks) (li : LinkedImage)
    (regsWithLen : List (Snapshot.Region × Nat)) (baseLines : BinTree Line64) (m0 : Memory)
    (hm0 : ∀ a : BitVec 64, a.toNat < cliBase.toNat + progByteBound →
      m0.cells a = rawCellAt baseLines a.toNat) :
    FastProgSound W li (buildFastProgWithLens W li regsWithLen baseLines) m0 := by
  intro pc m hkf off hmod4 hlt
  simp only [buildFastProgWithLens, withForcedBinTree_eq, lookupStepEntry,
    btGet_overlayHooks W li.stubs .empty hlt, btGet_empty]
  have hoff_eq : 4 * (off / 4) = off := by omega
  cases hstub : hookStubAt? W li.stubs (4 * (off / 4)) with
  | some name =>
    dsimp only
    intro h hext
    rw [hoff_eq] at hstub
    rw [rebase_externAt_eq]
    exact findSome_stubs_of_hookStubAt_some hstub hext
  | none =>
    have hkey : Nat.add (Nat.div cliBase.toNat 64) (Nat.div (off / 4) 16) =
        cliBase.toNat / 64 + (off / 4) / 16 := rfl
    have hrem : Nat.mod (off / 4) 16 = (off / 4) % 16 := rfl
    dsimp only
    rw [hkey, hrem]
    cases hline : btGet 58 baseLines (cliBase.toNat / 64 + (off / 4) / 16) with
    | none => trivial
    | some line =>
      dsimp only
      have hv := decodeStepFromLine_valid baseLines ((off / 4) / 16) ((off / 4) % 16) line hline (by omega)
      have hdiv_mod : 16 * ((off / 4) / 16) + (off / 4) % 16 = off / 4 := Nat.div_add_mod (off / 4) 16
      rw [hdiv_mod] at hv
      cases hdec_e : decodeStepFromLine line ((off / 4) % 16) with
      | hook _ => rw [hdec_e] at hv; exact False.elim hv
      | unmapped => trivial
      | instr inst =>
        rw [hdec_e] at hv
        rcases hv with ⟨p0, b0, p1, b1, p2, b2, p3, b3,
          ⟨hc0, hx0, hw0⟩, ⟨hc1, hx1, hw1⟩, ⟨hc2, hx2, hw2⟩, ⟨hc3, hx3, hw3⟩, hdec⟩
        have hpc_eq : pc = cliBase + BitVec.ofNat 64 (4 * (off / 4)) :=
          pc_eq_cliBase_add_idx pc hmod4
        have hbnd := cliBase_progByteBound_le
        have hlt_bytes : 4 * (off / 4) + 4 ≤ progByteBound := by
          unfold progByteBound; omega
        have htoNat_j : ∀ j, j < 4 →
            (pc + BitVec.ofNat 64 j).toNat = cliBase.toNat + 4 * (off / 4) + j ∧
              (pc + BitVec.ofNat 64 j).toNat < cliBase.toNat + progByteBound := by
          intro j hj
          rw [hpc_eq]
          have hpc_nat : (cliBase + BitVec.ofNat 64 (4 * (off / 4))).toNat =
              cliBase.toNat + 4 * (off / 4) := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have hsum_nat : (cliBase + BitVec.ofNat 64 (4 * (off / 4)) + BitVec.ofNat 64 j).toNat =
              cliBase.toNat + 4 * (off / 4) + j := by
            rw [BitVec.toNat_add, hpc_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          exact ⟨hsum_nat, by omega⟩
        obtain ⟨hn0, hb0_lt⟩ := htoNat_j 0 (by omega)
        obtain ⟨hn1, hb1_lt⟩ := htoNat_j 1 (by omega)
        obtain ⟨hn2, hb2_lt⟩ := htoNat_j 2 (by omega)
        obtain ⟨hn3, hb3_lt⟩ := htoNat_j 3 (by omega)
        simp only [Nat.add_zero] at hn0
        have hm0_0 : m0.cells (pc + 0#64) = some (some p0, b0) :=
          (hm0 (pc + 0#64) hb0_lt).trans (by rw [hn0]; exact hc0)
        have hm0_1 : m0.cells (pc + 1#64) = some (some p1, b1) :=
          (hm0 (pc + 1#64) hb1_lt).trans (by rw [hn1]; exact hc1)
        have hm0_2 : m0.cells (pc + 2#64) = some (some p2, b2) :=
          (hm0 (pc + 2#64) hb2_lt).trans (by rw [hn2]; exact hc2)
        have hm0_3 : m0.cells (pc + 3#64) = some (some p3, b3) :=
          (hm0 (pc + 3#64) hb3_lt).trans (by rw [hn3]; exact hc3)
        obtain ⟨hex0, hrd0⟩ := cell_frozen_exec_read8 hkf hm0_0 hx0 hw0
        obtain ⟨hex1, hrd1⟩ := cell_frozen_exec_read8 hkf hm0_1 hx1 hw1
        obtain ⟨hex2, hrd2⟩ := cell_frozen_exec_read8 hkf hm0_2 hx2 hw2
        obtain ⟨hex3, hrd3⟩ := cell_frozen_exec_read8 hkf hm0_3 hx3 hw3
        have hpc0 : pc + 0#64 = pc := BitVec.add_zero pc
        rw [hpc0] at hex0 hn0
        have ha2 : pc + 1#64 + 1#64 = pc + 2#64 := by
          rw [BitVec.add_assoc]; rfl
        have ha3 : pc + 2#64 + 1#64 = pc + 3#64 := by
          rw [BitVec.add_assoc]; rfl
        have hcanExec : m.canExec pc 4 = true := by
          simp only [Memory.canExec, Memory.allPerm, hex0, Bool.true_and, ha2, hex1, ha3, hex2, hex3]
        have hread32 : m.read32 pc = b3 ++ b2 ++ b1 ++ b0 := by
          simp only [Memory.read32, hrd0, hrd1, hrd2, hrd3]
        have hext_none : (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)).externAt? pc = none := by
          rw [rebase_externAt_eq]
          rw [hoff_eq] at hstub
          exact findSome_stubs_of_hookStubAt_none hstub
        have hpc_mod4 : pc.toNat % 4 = 0 := by
          have := cliBase_mod4
          omega
        simp only [Program.fetchMem, hext_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          hpc_mod4, ne_eq, not_true_eq_false, hcanExec, Bool.not_true, hread32, hdec]

end Symbolic.BugInjection.Proofs.CliExec.FastStepInitAux
