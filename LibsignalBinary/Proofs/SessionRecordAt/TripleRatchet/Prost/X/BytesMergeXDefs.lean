/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WPp

/-!
# Definitions and Stack Lemmas for `prost::encoding::bytes::merge`

Fetch macro, stack-frame decomposition, and `memcpy` / `Bytes` vtable-drop helper specifications for
`prost::encoding::bytes::merge` (`0x2788`) on `contractProg img.base ext` and under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge_fnOff

/-- Fetch hypotheses for `bytes::merge` (`0x2788`) on arbitrary `H`, from fn-relative offset `k0`, `len` bytes. -/
elab "merge_fetches_H " b:term:max H:term:max
    hfn:term:max k0:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat (← `((num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))) "merge_fetches_H "))
  let k0Lit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat k0 "merge_fetches_H "))
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "merge_fetches_H "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-- `memcpy` contract with `decodeVarintSliceStackW` (`24656` bytes). -/
def sessionMemcpySpecBMX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp decodeVarintSliceStackW)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp decodeVarintSliceStackW

def L1_BytesMergeXDefs : Unit := ()

/-- `bytes::merge` stack layout at entry: splits `decodeVarintSliceStackW = 24656`
at bottom and 224 bytes of local frame. -/
theorem stackAt_bytesMergeX_entry (sp0 : BitVec 64) :
    stackAt sp0 bytesMergeStackW =
      stackAt (sp0 - 224#64) decodeVarintSliceStackW ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  have h1 : stackAt sp0 bytesMergeStackW =
      stackAt (sp0 - 224#64) decodeVarintSliceStackW ∗ memRegion (sp0 - 224#64) 224 := by
    unfold stackAt
    change memRegion (sp0 - 24880#64) (24656 + 224) =
      memRegion (sp0 - 224#64 - 24656#64) 24656 ∗ memRegion (sp0 - 224#64) 224
    rw [memRegion_split (sp0 - 24880#64) 24656 224 (by decide)]
    have e1 : sp0 - 24880#64 = sp0 - 224#64 - 24656#64 := by bv_lin
    have e2 : sp0 - 224#64 - 24656#64 + 24656#64 = sp0 - 224#64 := by bv_lin
    rw [e1, e2]
  have h2 : memRegion (sp0 - 224#64) 224 =
      memRegion (sp0 - 224#64) 8 ∗ memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗ cells (sp0 - 64#64) 8 := by
    rw [show (224 : Nat) = 8 + (48 + (104 + 8 * 8)) from rfl,
      memRegion_split (sp0 - 224#64) 8 (48 + (104 + 8 * 8)) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64) 48 (104 + 8 * 8) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64 + 48#64) 104 (8 * 8) (by decide),
      memRegion_cells _ 8 (by decide)]
    have e1 : sp0 - 224#64 + 8#64 = sp0 - 216#64 := by bv_lin
    have e2 : sp0 - 216#64 + 48#64 = sp0 - 168#64 := by bv_lin
    have e3 : sp0 - 168#64 + 104#64 = sp0 - 64#64 := by bv_lin
    rw [e1, e2, e3]
  rw [h1, h2]

theorem fold_stackAt_bytesMergeX (sp0 : BitVec 64)
    (w29 w30 w24 w23 w22 w21 w20 w19 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW ∗
    memRegion (sp0 - 224#64) 8 ∗
    memRegion (sp0 - 216#64) 48 ∗
    memRegion (sp0 - 168#64) 104 ∗
    ((sp0 - 64#64) ↦₆₄ w29) ∗ ((sp0 - 56#64) ↦₆₄ w30) ∗
    ((sp0 - 48#64) ↦₆₄ w24) ∗ ((sp0 - 40#64) ↦₆₄ w23) ∗
    ((sp0 - 32#64) ↦₆₄ w22) ∗ ((sp0 - 24#64) ↦₆₄ w21) ∗
    ((sp0 - 16#64) ↦₆₄ w20) ∗ ((sp0 - 8#64) ↦₆₄ w19) ⊢
    stackAt sp0 bytesMergeStackW := by
  rw [stackAt_bytesMergeX_entry sp0]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (fold_cells_8 sp0 w29 w30 w24 w23 w22 w21 w20 w19))))

theorem stackAt_sliceX_to_decodeErrorX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 80 ∗ stackAt (sp0 - 224#64) decodeErrorHookStackW := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 80 decodeErrorHookStackW (by decide)

theorem stackAt_sliceX_to_varintSlowX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 16 ∗ stackAt (sp0 - 224#64) (64 + decodeErrorHookStackW) := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16 (64 + decodeErrorHookStackW) (by decide)

theorem stackAt_sliceX_to_allocX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 8272 ∗ stackAt (sp0 - 224#64) CryptoVerification.LibsignalTripleRatchet.extHookStack := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 8272 CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)

theorem stackAt_sliceX_to_bytesFromVecX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 24608 ∗ stackAt (sp0 - 224#64) bytesFromVecStack := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 24608 bytesFromVecStack (by decide)

theorem stackAt_sliceX_to_doReserveX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 8160 ∗ stackAt (sp0 - 224#64) doReserveStackX := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 8160 doReserveStackX (by decide)

abbrev bytesVtableDropStackBMX : Nat := CryptoVerification.LibsignalTripleRatchet.extHookStack + 48

def bytesVtableDropSpecBMX (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackBMX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackBMX

theorem stackAt_sliceX_to_vtableDropX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 8224 ∗ stackAt (sp0 - 224#64) bytesVtableDropStackBMX := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 8224 bytesVtableDropStackBMX (by decide)

theorem stackAt_sliceX_to_memcpyX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackW =
      memRegion (sp0 - 24880#64) 8272 ∗ stackAt (sp0 - 224#64) CryptoVerification.LibsignalTripleRatchet.extHookStack := by
  have h : sp0 - 224#64 - 24656#64 = sp0 - 24880#64 := by bv_lin
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 8272 CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)

abbrev MergePostW (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecW A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanicW (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecW A).onPanic x s0 sf ∗ R)

def bm_HighCalleeSavedX (s0 s : State) : Prop :=
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.vregs.calleeSaved = s0.vregs.calleeSaved

theorem bm_HighCalleeSavedX.refl (s0 : State) : bm_HighCalleeSavedX s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bm_HighCalleeSavedX.of_calleeSaved {s0 s sf : State}
    (h : bm_HighCalleeSavedX s0 s) (hcs : CalleeSavedPreserved s sf) :
    bm_HighCalleeSavedX s0 sf := by
  obtain ⟨h25, h26, h27, h28, hv⟩ := h
  obtain ⟨_, _, _, _, _, _, h25', h26', h27', h28', _, hv'⟩ := hcs
  exact ⟨h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hv'.trans hv⟩

/-! ## Relocatable `[LibsignalPlacement]` Definitions & Spec Bridges -/

section Placed

open CryptoVerification

abbrev MergePlacedPostW [LibsignalPlacement] (A : RustAlloc) (x : BytesMergeGhost)
    (s0 : State) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergePlacedSpecW A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePlacedPanicW [LibsignalPlacement] (A : RustAlloc) (x : BytesMergeGhost)
    (s0 : State) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergePlacedSpecW A).onPanic x s0 sf ∗ R)

theorem sessionMemcpySpecBMX_eq_gen :
    sessionMemcpySpecBMX = bmMemcpySpecGen decodeErrorHookStackW := rfl

theorem bytesVtableDropSpecBMX_eq_gen (A : RustAlloc) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (off : Nat) :
    bytesVtableDropSpecBMX A ptr bs off =
      bytesVtableDropSpecBMGen A CryptoVerification.LibsignalTripleRatchet.extHookStack ptr bs off := rfl

theorem bytesMergePlacedSpecW_eq_gen [LibsignalPlacement] (A : RustAlloc) :
    bytesMergePlacedSpecW A =
      withLsCodeRoLoaded lsmpl (bytesMergeRawSpecGen A decodeErrorHookStackW false) := rfl

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
