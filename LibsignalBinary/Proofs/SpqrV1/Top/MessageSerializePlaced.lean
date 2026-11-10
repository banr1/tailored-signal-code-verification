/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Verification of `<Message>::serialize`

Proves `MessageSerializePlacedOkX` for `<spqr::v1::chunked::states::Message>::serialize`
(Block `352`, 110 instructions) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Top.MessageSerialize

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint CryptoVerification.SpqrV1.Alloc
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Top.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `<spqr::v1::chunked::states::Message>::serialize` (Block `352`) meets `withLsCodeLoaded
    lsmpl (messageSerializeSpecX P A)` on `libsignalSessionLib.blockProgram lsmpl 352
    (Rust.withPanics ext)`. -/
def MessageSerializePlacedOkX [LibsignalPlacement] (P : PolyApi) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
    (lsmpl.base 352)
    (withLsCodeLoaded lsmpl (messageSerializeSpecX P A))

/-- Wrap a spec with `⌜StepInvPlaced s0 s⌝` in the precondition. -/
def withStepInvPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜StepInvPlaced s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withStepInvPlaced_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 624 := by decide) (hj : j < 624 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withStepInvPlaced s0 spec) := by
  have htr := ls_subroutine_ok_of_block (callerProg := callerProg) hcallee hi hj hj_unmut
  exact subroutine_ok_mono htr
    (fun _ s _ hp => by
      dsimp only [withStepInvPlaced, withLsCodeLoaded] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0.of_keepsFrozen hp.1.2, hp.2⟩)
    (fun _ _ _ _ hq => hq)

/-- Callee-saved registers `x23..x28`, `calleeSavedVRegs`, + `StepInvPlaced` preserved across
    `<Message>::serialize`. -/
def MsgSerializeCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧ StepInvPlaced s0 s

theorem MsgSerializeCalleeSavedPlaced.refl (s : State) : MsgSerializeCalleeSavedPlaced s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInvPlaced.refl s⟩

theorem MsgSerializeCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h1 : MsgSerializeCalleeSavedPlaced s0 s1) (h2 : MsgSerializeCalleeSavedPlaced s1 s2) :
    MsgSerializeCalleeSavedPlaced s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2⟩

theorem MsgSerializeCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) : MsgSerializeCalleeSavedPlaced s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

/-- Execute a `bl spqr::encode_varint` (`lsmpl.base 326`) call inside `<Message>::serialize`
    (Block `352`). -/
theorem step_call_spqrEncodeVarint_40_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A)))
    (val v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length + 10 ≤ 40)
    {x : MessageSerializeGhost P_api} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 326)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v 40#64 ptr curBs ∗ A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        ((vecU8At A v 40#64 ptr (CryptoVerification.LibsignalSpqrV1.encode_varint val curBs) ∗
          A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine SepWPp.call_cs_placed (x := EncodeVarintGhost.mk val v 40#64 ptr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withStepInvPlaced, spqrEncodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs.2.2.2.2.2.2.2, ⟨hx0, hx1, Or.inl hlen⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInvPlaced, spqrEncodeVarintSpecX, messageSerializeSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInvPlaced, spqrEncodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htrm => SepWPp.pure_elim fun hcap_prop => ?_
    have hloop_le : curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ (40#64 : BitVec 64).toNat := by
      have h1 := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN val
      have hm : MAX_VARINT_BYTES_LEN = 10 := rfl
      change curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ 40; omega
    obtain ⟨hcap_eq, hptr_eq⟩ := hcap_prop.2 hloop_le
    subst hcap_eq; subst hptr_eq
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr)
        hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
        (hcs.trans (MsgSerializeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))

/-- Execute `bl do_reserve_and_handle [local#7]` (`lsmpl.base 320`) inside
    `<Message>::serialize` (Block `352`) when `cap = 40#64`, `curBs.length ≤ 32`, and
    `additional = 32`, growing capacity to `80#64`. -/
theorem step_call_doReserve7_40_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hres7 : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 320) (withStepInvPlaced s0 (doReserveSpec A)))
    (v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length ≤ 32)
    {x : MessageSerializeGhost P_api} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 320)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 32#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v 40#64 ptr curBs ∗ A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        ((vecU8At A v 80#64 ptr' curBs ∗
          A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hres_eq : reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold reserveCap; change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v 40#64 ptr curBs 32)
    (F := memRegion (sp - 80#64 - 16464#64) 12256 ∗ F)
    hres7 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)] at hm
    simp only [withStepInvPlaced, doReserveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs.2.2.2.2.2.2.2, ⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, by rw [hres_eq]; decide⟩,
      by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInvPlaced, doReserveSpec, messageSerializeSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInvPlaced, doReserveSpec, hsp, hres_eq, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm ptr' hpcm hrunm hspm (htrm.trans htr)
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
      (hcs.trans (MsgSerializeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Shared return tail (`+0x168..+0x188`, `360..392`). -/
theorem step_msgSerialize_ret_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (capFinal ptrFinal v80 v56 r0 r1 r2 : BitVec 64) (bsFinal : List (BitVec 8))
    (hser : bsFinal = x.msg.serialize x.index)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 bsFinal.length) (hx19 : s.readReg64 .x19 = x.ret)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (((s0.sp - 72#64) ↦₆₄ capFinal) ∗ ((s0.sp - 64#64) ↦₆₄ ptrFinal) ∗
       ((s0.sp - 56#64) ↦₆₄ v56) ∗ vecU8Buf A capFinal ptrFinal bsFinal ∗
       messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs, _⟩
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩
  intro hm_f
  have hvec_pack :
      (x.ret ↦₆₄ capFinal) ∗ ((x.ret + 8#64) ↦₆₄ ptrFinal) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (x.msg.serialize x.index).length) ∗
      vecU8Buf A capFinal ptrFinal bsFinal =
      vecU8At A x.ret capFinal ptrFinal (x.msg.serialize x.index) := by
    rw [← hser, vecU8At_eq_header_buf]
  simp only [messageSerializeSpecX, vecU8, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v80, capFinal, ptrFinal, v56,
    s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x22, s0.readReg64 .x21,
    s0.readReg64 .x20, s0.readReg64 .x19, capFinal, ptrFinal, by simp only [arm64_norm, *], ?_⟩
  rw [← hvec_pack]; convert hm_f using 1; ac_rfl

/-- Non-chunk epilogue (`+0x15c..+0x188`, `348..392`). -/
theorem step_msgSerialize_epilogue_no_chunk_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (ptr v80 r0 r1 r2 : BitVec 64) (bs2 : List (BitVec 8)) (tag : BitVec 8)
    (hlt40 : bs2.length < (40#64 : BitVec 64).toNat)
    (hser : bs2 ++ [tag] = x.msg.serialize x.index)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length)
    (hx22 : (s.readReg64 .x22).setWidth 8 = tag) (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
       messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  subst hP
  have hlen1 := bv_len_add_one bs2 tag
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs2, vecU8Buf_eq_open_one A 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 360#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  rw [vecU8Buf_snoc_eq A 40#64 ptr bs2 tag hlt40]
  exact step_msgSerialize_ret_placed A ext x 40#64 ptr v80 (BitVec.ofNat 64 bs2.length) r0 r1 r2
    (bs2 ++ [tag]) hser
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩)
    (by ac_rfl)

/-- Chunk 32-byte copy and epilogue (`+0x13c..+0x158` + `+0x168..+0x188`, `316..344` +
    `360..392`). -/
theorem step_msgSerialize_copy_and_epilogue_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (c : P_api.Chunk) (capFinal ptrFinal v80 r0 r1 r2 : BitVec 64)
    (bs4 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hle32 : bs4.length + 32 ≤ capFinal.toNat)
    (hser : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index)
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A (s0.sp - 72#64) capFinal ptrFinal bs4 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  subst hP
  have hdata_len : (P_api.chunkData c).toList.length = 32 := (P_api.chunkData c).property
  obtain ⟨w0, w1, w2, w3, hw⟩ := list_eq_unpack64_4_of_len32 (P_api.chunkData c).toList hdata_len
  have hchunk_unfold :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦₆₄ w0) ∗
        ((x.msgA + 0x12#64) ↦₆₄ w1) ∗
        ((x.msgA + 0x1a#64) ↦₆₄ w2) ∗
        ((x.msgA + 0x22#64) ↦₆₄ w3) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; dsimp only
    rw [hw, pointsToBytes_unpack64_4_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  have hlen32_bv :
      BitVec.ofNat 64 bs4.length + 32#64 =
        BitVec.ofNat 64 (bs4 ++ (P_api.chunkData c).toList).length := by
    simp only [List.length_append, hdata_len, BitVec.ofNat_add]
  rw [hchunk_unfold, vecU8At_sp72_eq A s0.sp capFinal ptrFinal bs4,
    vecU8Buf_eq_open_32 A capFinal ptrFinal bs4 hle32]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 360#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  rw [vecU8Buf_append_32_eq A capFinal ptrFinal bs4 (P_api.chunkData c).toList
    w0 w1 w2 w3 hle32 hw hdata_len]
  exact step_msgSerialize_ret_placed A ext x capFinal ptrFinal v80 (BitVec.ofNat 64 bs4.length) r0 r1 r2
    (bs4 ++ (P_api.chunkData c).toList) hser
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩)
    (by rw [← hmsg_eq, hchunk_unfold]; ac_rfl)

/-- Full chunk branch (`+0x10c..+0x188` & `+0x190..+0x1ac`, `268..392` & `400..428`). -/
theorem step_msgSerialize_chunk_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hres7 : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 320) (withStepInvPlaced s0 (doReserveSpec A)))
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A)))
    (x : MessageSerializeGhost P_api)
    (c : P_api.Chunk) (ptr v80 r0 r1 r2 : BitVec 64)
    (bs2 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hlen21 : bs2.length ≤ 21)
    (hser : encode_chunk c (bs2 ++ [tag]) = x.msg.serialize x.index)
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (blkPl_352).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length) (hx22 : (s.readReg64 .x22).setWidth 8 = tag)
    (hcs : MsgSerializeCalleeSavedPlaced s0 s)
    (hP : P =
      (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  subst hP
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by change bs2.length < 40; omega
  have hlen1 := bv_len_add_one bs2 tag
  have hchunk_idx :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦ₛ (P_api.chunkData c).toList) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hchunk_idx, vecU8At_sp72_eq A s0.sp 40#64 ptr bs2, vecU8Buf_eq_open_one A 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step1
  rw [vecU8Buf_snoc_eq A 40#64 ptr bs2 tag hlt40]
  have hvec_bs3 := (vecU8At_sp72_eq A s0.sp 40#64 ptr (bs2 ++ [tag])).symm
  refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (R := R)
    A ext henc ((P_api.chunkIndex c).zeroExtend 64) (s0.sp - 72#64) ptr s0.sp ((blkPl_352).base + 296#64)
    (bs2 ++ [tag]) (by simp only [List.length_append, List.length_singleton]; omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step1⟩)
    (by rw [hchunk_idx, ← hvec_bs3]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx19m hx20m _ _ _ hcsm
  have hx19m' : sm.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m' : sm.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  let bs4 := CryptoVerification.LibsignalSpqrV1.encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
  have hbs4_len : bs4.length ≤ 32 := by
    have := encode_varint_length_le ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    simp only [List.length_append, List.length_singleton] at this; dsimp only [bs4]; omega
  have hser4 : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index := hser
  change SepWPp _ _ sm ((vecU8At A (s0.sp - 72#64) 40#64 ptr bs4 ∗ _) ∗ _) _ _
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs4]
  by_cases hle32 : bs4.length + 32 ≤ 40
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_le hle32
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 316#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    exact step_msgSerialize_copy_and_epilogue_placed A ext x c 40#64 ptr v80 r0 r1 r2 bs4 tag msgTail
      hle32 hser4 hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]; ac_rfl)
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_gt hle32 (by dsimp only [bs4] at hbs4_len ⊢; omega)
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 320)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    refine step_call_doReserve7_40_placed (P_api := P_api) (x := x) (R := R)
      A ext hres7 (s0.sp - 72#64) ptr s0.sp ((blkPl_352).base + 420#64) bs4 hbs4_len
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]) ?_
    intro sm2 ptr' hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    rw [vecU8At_sp72_eq A s0.sp 80#64 ptr' bs4]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 316#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step3
    have hle80 : bs4.length + 32 ≤ (80#64 : BitVec 64).toNat := by
      change bs4.length + 32 ≤ 80; dsimp only [bs4] at hbs4_len ⊢; omega
    exact step_msgSerialize_copy_and_epilogue_placed A ext x c 80#64 ptr' v80 r0 r1 r2 bs4 tag msgTail
      hle80 hser4 hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step3⟩)
      (by rw [vecU8At_sp72_eq]; ac_rfl)

/-- Entry block (`+0x000..+0x060` & `+0x1ac..+0x1b8`, `0..96` & `428..440`). -/
theorem step_msgSerialize_entry_placed [LibsignalPlacement] {P_api : PolyApi}
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    {s0 : State}
    (henc : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsmpl.base 326) (withStepInvPlaced s0 (spqrEncodeVarintSpecX A)))
    (x : MessageSerializeGhost P_api)
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2 : BitVec 64)
    {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc0 : s0.pc = (blkPl_352).base)
    (hrun0 : s0.status = .Running) (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.msgA) (hx1 : (s0.readReg64 .x1).setWidth 32 = x.index)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hP : P =
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8))
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      let bs1 := CryptoVerification.LibsignalSpqrV1.encode_varint x.msg.epoch [1#8]
      let bs2 := CryptoVerification.LibsignalSpqrV1.encode_varint (x.index.zeroExtend 64) bs1
      sm.pc = (blkPl_352).base + 96#64 →
      sm.status = .Running → sm.sp = s0.sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.msgA →
      MsgSerializeCalleeSavedPlaced s0 sm → bs2.length ≤ 21 →
      SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) sm
        (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
         (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
         (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
         A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hshim_ok : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec := spqr_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := spqr_hook_ok_of_mem halloc
  have hpanic : ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem (sym := spqrHandleErrorSym)).trans h_panic
  subst hP
  rw [stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64)]
  have hpos40 : 0 < 40 := by decide
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbound40 : 40 + 1 ≤ 2 ^ 63 := by decide
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 52#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_step0
  by_cases hoom : sf_1.readReg64 .x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.weaken_pre (P' := ⌜sf_1.trace = sf.trace ++ [allocFailedEvent]⌝ ∗
      (A.pool ∗ stackAt sf.sp allocHookStack ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       memRegion (s0.sp - 16544#64) 12368 ∗
       ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
       ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim fun htrace => ?_)
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [messageSerializeSpecX, sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [hoom, ite_false]
    refine SepWPp.weaken_pre (P' := ⌜(sf_1.readReg64 .x0).toNat % 1 = 0 ∧ sf_1.trace = sf.trace⌝ ∗
      (A.pool ∗ stackAt sf.sp allocHookStack ∗
       A.live (sf_1.readReg64 .x0) 40 1 ∗ memRegion (sf_1.readReg64 .x0) 40 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       memRegion (s0.sp - 16544#64) 12368 ∗
       ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
       ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim fun ⟨_, htrace⟩ => ?_)
    rw [memRegion_40_split_1_39 (sf_1.readReg64 .x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step1
    have hsp_sf : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
    refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (R := R)
      A ext henc x.msg.epoch (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp ((blkPl_352).base + 84#64)
      [1#8] (by decide)
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv_step0.trans hinv_step1⟩ <;> simp only [wp_norm, arm64_norm, *])
      (by
        have hinit := vecU8At_init_40_one A (s0.sp - 72#64) (sf_1.readReg64 .x0) hoom
        simp only [arm64_norm] at hinit
        rw [hsp_sf, ← hinit, stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64),
          show s0.sp - 80#64 - 16464#64 = s0.sp - 16544#64 by bv_omega]
        simp only [arm64_norm]; ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19m1 hx20m1 hx21m1 _ _ hcsm1
    have hx19m1' : sm1.readReg64 .x19 = x.ret := by simp only [wp_norm, arm64_norm, *]
    have hx20m1' : sm1.readReg64 .x20 = x.msgA := by simp only [wp_norm, arm64_norm, *]
    have hx21m1' : (sm1.readReg64 .x21).setWidth 32 = x.index := by rw [hx21m1]; simp only [wp_norm, arm64_norm, *]
    let bs1 := CryptoVerification.LibsignalSpqrV1.encode_varint x.msg.epoch [1#8]
    have hbs1_len : bs1.length ≤ 11 := by
      have := encode_varint_length_le x.msg.epoch [1#8]; simp only [List.length_singleton] at this; omega
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 326)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    refine step_call_spqrEncodeVarint_40_placed (P_api := P_api) (x := x) (R := R)
      A ext henc (x.index.zeroExtend 64) (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp ((blkPl_352).base + 96#64)
      bs1 (by omega)
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    have hbs2_len :
        (CryptoVerification.LibsignalSpqrV1.encode_varint (x.index.zeroExtend 64) bs1).length ≤ 21 := by
      have := encode_varint_length_le (x.index.zeroExtend 64) bs1; omega
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm2 (sf_1.readReg64 .x0) hpcm2 hrunm2 hspm2 htrm2 hx19m2' hx20m2' hcsm2 hbs2_len)

/-- `<spqr::v1::chunked::states::Message>::serialize` (Block `352`, 110 insns) meets
    `withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A)` on `(blkPC_352).rebase
    (blkPl_352).base (Rust.withPanics ext)`. -/
theorem messageSerialize_placed_ok_blk_x [LibsignalPlacement] (P_api : PolyApi) (A : RustAlloc)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hres7 : subroutine_ok ((blkPC_320).rebase (blkPl_320).base (Rust.withPanics ext))
      (blkPl_320).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (henc : SpqrEncodeVarintPlacedOkExt A ext) :
    subroutine_ok ((blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))
      (blkPl_352).base
      (withLsCodeLoaded lsmpl (messageSerializeSpecX P_api A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hres7_s0 := subroutine_ok_withStepInvPlaced_of_block
    (callerProg := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) hcl0 hres7
  have henc_s0 := subroutine_ok_withStepInvPlaced_of_block
    (callerProg := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext)) hcl0 henc
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [messageSerializeSpecX, messageAt, memRegion_24, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, r2, r1, r0, ⟨hx0, hx1, hx8⟩, hpre⟩
  refine ⟨(x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗ ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8),
    R, by convert hpre using 1; ac_rfl,
    step_msgSerialize_entry_placed A ext h_panic hshim halloc henc_s0 x
      v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2
      hpc0 hrun0 halign hx0 hx1 hx8 rfl ?_⟩
  intro sm ptr bs1 bs2 hpcm hrunm hspm htrm hx19m hx20m hcsm hbs2_len
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by
    change bs2.length < 40; dsimp only [bs2, bs1] at hbs2_len ⊢; omega
  have hbeq := len_beq_cap_false hlt40
  change SepWPp _ _ sm
    (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
     (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗ _) _ _
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs2]
  cases hpay : x.msg.payload with
  | none =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 348#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : bs2 ++ [0#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 0#8) ∗ memRegion (x.msgA + 0x09#64) 39 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk_placed A ext x ptr v80 r0 r1 r2 bs2 0#8 hlt40 hser
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq, ← hmsg_eq]; ac_rfl)
  | ct1Ack b_ack =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 348#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : bs2 ++ [4#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 4#8) ∗
        ((x.msgA + 0x09#64) ↦₈ (if b_ack then 1#8 else 0#8)) ∗ memRegion (x.msgA + 0x0a#64) 38 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk_placed A ext x ptr v80 r0 r1 r2 bs2 4#8 hlt40 hser
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq, ← hmsg_eq]; ac_rfl)
  | hdr c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [1#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 1#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A ext hres7_s0 henc_s0 x c ptr v80 r0 r1 r2 bs2 1#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ek c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [2#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 2#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A ext hres7_s0 henc_s0 x c ptr v80 r0 r1 r2 bs2 2#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ekCt1Ack c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [3#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 3#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A ext hres7_s0 henc_s0 x c ptr v80 r0 r1 r2 bs2 3#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ct1 c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [5#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 5#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A ext hres7_s0 henc_s0 x c ptr v80 r0 r1 r2 bs2 5#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ct2 c =>
    simp only [messagePayloadAt]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_352).base + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step
    have hser : encode_chunk c (bs2 ++ [6#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 6#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk_placed A ext hres7_s0 henc_s0 x c ptr v80 r0 r1 r2 bs2 6#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSavedPlaced, arm64_norm, *, and_self])) (by rw [vecU8At_sp72_eq]; ac_rfl)

/-- Relocatable `<Message>::serialize` (Block `352`) correctness theorem on `blockProgram lsmpl
    352`. -/
theorem messageSerialize_placed_ok_x [LibsignalPlacement] (P_api : PolyApi) (A : RustAlloc)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hres7 : subroutine_ok ((blkPC_320).rebase (blkPl_320).base (Rust.withPanics ext))
      (blkPl_320).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (henc : SpqrEncodeVarintPlacedOkExt A ext) :
    MessageSerializePlacedOkX P_api A ext := by
  unfold MessageSerializePlacedOkX
  rw [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_352).rebase (blkPl_352).base (Rust.withPanics ext))]
  exact messageSerialize_placed_ok_blk_x P_api A ext h_panic hshim halloc hres7 henc

end CryptoVerification.SpqrV1.Top.MessageSerialize
