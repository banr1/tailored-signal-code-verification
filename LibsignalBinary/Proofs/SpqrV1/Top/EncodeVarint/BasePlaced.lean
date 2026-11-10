/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import ProofLib.SepLogic.WPp

/-!
# Relocatable Base Step Lemmas for `spqr::encode_varint` (Block `326`, 164 insns)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
  (encodeVarintLoop MAX_VARINT_BYTES_LEN GrowOneCall newCapU8 growOneU8Spec growOneU8Name SpqrHooks)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Wrap a spec with `⌜StepInvPlaced s0 s⌝` in the precondition. -/
def spqrWithStepInvPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜StepInvPlaced s0 s⌝ ∗ spec.pre x s }

/-- `grow_one` (`lsmpl.base 619`) contract at step state `s` given `StepInvPlaced s0 s`. -/
def GrowOneU8StepOk [LibsignalPlacement] (s0 : State) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs))
    (lsmpl.base 619)
    (spqrWithStepInvPlaced s0 (growOneU8Spec A))

theorem growOneU8_stepOk_of_cl [LibsignalPlacement] {s0 : State} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hgrow : GrowOneU8PlacedOkExt A abs) :
    GrowOneU8StepOk s0 A abs :=
  subroutine_ok_mono hgrow
    (fun _ s _ hp => by
      dsimp only [spqrWithStepInvPlaced, withLsCodeLoaded] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0.of_keepsFrozen hp.1.2, hp.2⟩)
    (fun _ _ _ _ hq => hq)

/-- Execute a `bl <RawVec<u8>>::grow_one` call at `s.pc = lsmpl.base 619`
when `curCap.toNat = curBs.length`. -/
theorem step_growOneU8_placed_call [LibsignalPlacement] (A : RustAlloc)
    (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8StepOk s0 A abs)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 619)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs_s : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curBs.length < newCap.toNat →
      curCap.toNat ≤ newCap.toNat →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  obtain ⟨hmax_lt, hnew_toNat, hnew_ne, hnew_gt, hnew_ge⟩ := newCapU8_bounds hcap_eq hlen_lt
  refine SepWPp.call_cs_placed (x := GrowOneCall.mk v curCap curPtr curBs) (F := F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_for_growOne A curCap curPtr curBs hcap_eq] at hm
    have hm' : s.mem ⊨ ⌜curCap.toNat < 2 ^ 63 ∧ curPtr ≠ 0⌝ ∗
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          (if curCap = 0 then emp else A.live curPtr curBs.length 1 ∗ (curPtr ↦ₛ curBs)) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ (F ∗ R')) := by
      convert hm using 1; ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    simp only [spqrWithStepInvPlaced, growOneU8Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs_s.2.2.2.2, ⟨hx0, hcap_eq.symm, hm'.1.2, hmax_lt⟩, ?_⟩
    convert hm'.2 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [spqrWithStepInvPlaced, growOneU8Spec, spqrEncodeVarintSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [spqrWithStepInvPlaced, growOneU8Spec, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hpost_eq :
        (⌜p' ≠ 0⌝ ∗ (v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * curCap.toNat) 8) 1 ∗ (p' ↦ₛ curBs) ∗
          memRegion (p' + BitVec.ofNat 64 curBs.length) (max (2 * curCap.toNat) 8 - curCap.toNat)) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F =
        (((v ↦₆₄ newCapU8 curCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          vecU8Buf A (newCapU8 curCap) p' curBs ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F) := by
      unfold vecU8Buf
      simp only [hnew_ne, ↓reduceIte, hnew_toNat, hcap_eq]
      have hpure : (curBs.length ≤ max (2 * curBs.length) 8 ∧ max (2 * curBs.length) 8 < 2 ^ 63 ∧ p' ≠ 0) =
          (p' ≠ 0) := by
        apply propext; constructor
        · exact fun h => h.2.2
        · intro hp; exact ⟨by omega, by omega, hp⟩
      rw [hpure]
      ac_rfl
    refine SepWPp.weaken_pre ?_ (hnext sm (newCapU8 curCap) p'
      hpcm hrunm hspm htrm'
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.1 hcsm.2.2.2.2.2.1 hcsm.2.2.2.2.2.2.1
      (hcs_s.trans (SpqrEncVarintCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge)
    exact Entails.of_eq (by rw [← hpost_eq]; ac_rfl)

/-! ## Prologue (`0..44`) and Shared Tail (`412..460`) -/

/-- Prologue (`+0x000..+0x028`, offsets `0..44`): allocates `0x50 = 80` byte stack frame,
saves `fp, lr, x25, x24, x23, x22, x21, x20, x19`, loads `origLen` (`x22`), sets `x19 = v`,
`x20 = val`, and branches on `val.ult 128#64` to `+44` or `+64`. -/
theorem step_spqrEncVarint_placed_prologue [LibsignalPlacement] (abs : String → Option (State → State))
    (val v cap ptr sp v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗
      ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (blkPl_326).base + 44#64
      else
        (blkPl_326).base + 64#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x22 = BitVec.ofNat 64 bs.length →
      SpqrEncVarintCalleeSavedPlaced s sm →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 80#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 72#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 64#64) ↦₆₄ s.readReg64 .x25) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
          ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) ret s P Q Qp := by
  subst hP
  apply SepWPp.of_sepWP_cs_placed (mid := if val.ult 128#64 then (blkPl_326).base + 44#64 else (blkPl_326).base + 64#64)
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])

/-- Shared final-byte writer and epilogue (`+0x19c..+0x1c8`, offsets `412..460`). -/
theorem step_spqrEncVarint_placed_tail [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State}
    (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R : SepProp} {P : SepProp}
    (hpc : s.pc = (if curBs.length < curCap.toNat then
      (blkPl_326).base + 420#64
    else
      (blkPl_326).base + 412#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : (s.readReg64 .x20).setWidth 8 = lastVal.setWidth 8)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · simp only [hlt, ↓reduceIte] at hpc
    rcases hcs with ⟨h26, h27, h28, hvregs, _⟩
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (lastVal.setWidth 8) hlt]
    have hinv' := hinv.step (byte := lastVal.setWidth 8) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    rw [hbs] at hinv'
    have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
    refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
    intro hm_f
    rw [hbs] at hm_f
    simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
      vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
      s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
      s0.readReg64 .x20, s0.readReg64 .x19, curCap, curPtr,
      by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
    convert hm_f using 1
    ac_rfl
  · simp only [hlt, ↓reduceIte] at hpc
    have hcap_eq : curCap.toNat = curBs.length := by omega
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow x.v curCap curPtr s0.sp
      ((blkPl_326).base + 420#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m _ _ _ _ hcsm hnew_gt hnew_ge
    rcases hcsm with ⟨h26, h27, h28, hvregs, _⟩
    have hx19m' : sm.readReg64 .x19 = x.v := by simp only [arm64_norm, *]
    have hx20m' : (sm.readReg64 .x20).setWidth 8 = lastVal.setWidth 8 := by
      rw [hx20m]; simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs (lastVal.setWidth 8) hnew_gt]
    have hinv' := hinv.step (nextPtr := p') (byte := lastVal.setWidth 8) hnew_ge (fun h => absurd h hlt)
    rw [hbs] at hinv'
    have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
    refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
    intro hm_f
    rw [hbs] at hm_f
    simp only [spqrEncodeVarintSpecX, spqr_encode_varint_eq, encodeVarintLoop_10_eq,
      vecU8At_eq_header_sep_buf, vecHeader, stackAt_spqrEncodeVarint_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x25, v56,
      s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
      s0.readReg64 .x20, s0.readReg64 .x19, newCap, p',
      by simp only [arm64_norm, *], ⟨hcap_le, hcap_pres⟩, ?_⟩
    convert hm_f using 1
    ac_rfl

/-! ## Exit Blocks (`44..64`, `112..132`, `184..204`, `256..276`, `328..348`, `396..412`, `640..656`) -/

/-- Stage 0 exit (`+44..+64`): sets `x21 = x22`, checks `x22 == curCap`, and
branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit0 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [x.val.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x x.val curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x x.val curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 1 exit (`+112..+132`): shifts `x20 := x20 >>> 7`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit1 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 7).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 7) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 7) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 2 exit (`+184..+204`): shifts `x20 := x20 >>> 14`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit2 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 14).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 14) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 14) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 3 exit (`+256..+276`): shifts `x20 := x20 >>> 21`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit3 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(x.val >>> 21).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 21) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x (x.val >>> 21) curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+328..+348` (used by Stages 4, 6, 8):
moves `w20 := w23`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit_328 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx23 : s.readReg64 .x23 = lastVal)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+396..+412` (used by Stages 5 and 7):
moves `w20 := w24`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit_396 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx24 : s.readReg64 .x24 = lastVal)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x lastVal curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 9 exit (`+640..+656`): checks `x21 == curCap` with `x20 = 1#64`
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit9 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (x : EncodeVarintGhost) (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [(1#64 : BitVec 64).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_326).base + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = 1#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 420#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x 1#64 curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 412#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    exact step_spqrEncVarint_placed_tail A abs hgrow x 1#64 curCap curPtr v56 curBs hinv hbs hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-! ## Continuation-Byte Stages 1..2 -/

/-- Stage 1 (`+64..+112`): appends `varintContByte val` and branches on
`(val >>> 7).ult 128#64` to `+112` (`exit1`) or `+132` (Stage 2). -/
theorem step_spqrEncVarint_placed_s1 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then
        (blkPl_326).base + 112#64
      else
        (blkPl_326).base + 132#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 112#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 132#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 88#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m _ hx22m hx23m _ _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte val := by rw [hx23m]; simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte val) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 112#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 132#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

/-- Stage 2 (`+132..+184`): appends `varintContByte (val >>> 7)` and branches on
`(val >>> 14).ult 128#64` to `+184` (`exit2`) or `+204` (Stage 3). -/
theorem step_spqrEncVarint_placed_s2 [LibsignalPlacement] (A : RustAlloc) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOk s0 A abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (horig : origLen + 1#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then
        (blkPl_326).base + 184#64
      else
        (blkPl_326).base + 204#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x22 = origLen →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 7)) 1#64 2#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 184#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 204#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 619)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    refine step_growOneU8_placed_call A abs hgrow v curCap curPtr sp
      ((blkPl_326).base + 160#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ _ hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
    have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
    have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte (val >>> 7) := by rw [hx23m]; simp only [arm64_norm, *]
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq := grow_frame_reassoc A v newCap p' sp curBs (varintContByte (val >>> 7)) F
    rcases hcond_or with hcond | hcond
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 184#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_326).base + 204#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_step2
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p'
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)

end CryptoVerification.SpqrV1.Top.EncodeVarint
