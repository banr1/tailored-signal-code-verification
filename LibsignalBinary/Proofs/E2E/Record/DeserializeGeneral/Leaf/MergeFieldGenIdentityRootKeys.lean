/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeIdentityRootKeys
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Tags 2–4 Leaf (`mergeFieldGenIdentityRootKeys_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenIdentityRootKeys_ok` for `local_identity_public` (tag `2`, `@0`),
`remote_identity_public` (tag `3`, `@0x18`), and `root_key` (tag `4`, `@0x30`) via `bytes::merge`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys
  calleeSavedVRegs_setPC_pre_identityRootKeys
  calleeSavedVRegs_setMem_setPC_pre_identityRootKeys

/-! ## Tag 2/3/4 Field Helpers and `prostSSGAt` Decomposition -/

theorem genField_tag_234_cases {fl : GenField}
    (hP : fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) (hok : fl.Ok) :
    (∃ b, fl = .lik b ∧ b.length = 33) ∨
    (∃ b, fl = .rik b ∧ b.length = 33) ∨
    (∃ b, fl = .root b ∧ b.length = 32) := by
  cases fl <;> simp [GenField.tag, GenField.Ok] at hP hok ⊢ <;> exact hok

def prostSSGRest_identityRootKeys (ss : BitVec 64) (v : SSG) : SepProp :=
  vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) v.recv ∗
    vecU8 A0 (ss + 0x60#64) [] ∗ vecU8 A0 (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A0 (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_eq_split_identityRootKeys (ss : BitVec 64) (v : SSG) :
    prostSSGAt A0 ss v =
      vecU8 A0 ss v.lik ∗ vecU8 A0 (ss + 0x18#64) v.rik ∗ vecU8 A0 (ss + 0x30#64) v.root ∗
        prostSSGRest_identityRootKeys ss v := by
  unfold prostSSGAt prostSSGRest_identityRootKeys
  ac_rfl

theorem finish_post_identityRootKeys_gen (P : GenField → Prop) (x : MergeFieldGenGhost)
    (valPtr w56 : BitVec 64) (b : List (BitVec 8))
    {s0 sf : State} {F_ss R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGAt A0 x.ss (x.v.apply x.fld))
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          vecU8 A0 valPtr b ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))) ∗ R) :
    sf.mem ⊨ (mergeFieldGenSpec P).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_identityRootKeys ∗
      ((mfUnusedStack_identityRootKeys s0.sp ∗ stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        ((vecU8 A0 valPtr b ∗ F_ss) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys s0.sp s0 w56)) h2
  rw [hss, ← hpay] at h3
  dsimp only [mergeFieldGenSpec]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

theorem step_call_and_ret_identityRootKeys_gen (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (P : GenField → Prop)
    (hbytes : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (x : MergeFieldGenGhost) (retOff valPtr w56 : BitVec 64)
    (valBs b : List (BitVec 8))
    {s0 sm : State} {F_ss R : SepProp}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpcm : sm.pc = mfEntry_identityRootKeys + bv% (2 ^ 64 - 12436))
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hFm : sessionImg0.FrozenLoaded sm)
    (hsymm : sm.symtab = sessionImg0.symtab)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = mfEntry_identityRootKeys + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = valPtr)
    (hx2m : sm.readReg64 .x2 = x.bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hb_lt : b.length < 128)
    (htail_lt : ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 32)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGAt A0 x.ss (x.v.apply x.fld)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) sm
      (vecU8 A0 valPtr valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenSpec P).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      (mfEntry_identityRootKeys + bv% (2 ^ 64 - 12436)) (Prost.bytesMergeSpec A0 sessionImg0) := by
    rw [bytesMerge_fnAddr_eq_identityRootKeys C ctl]
    exact hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim (fun cap0 => SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, valBs, x.bufRef, x.slot, x.ptr,
     [BitVec.ofNat 8 b.length] ++ b ++ x.tail⟩
  refine SepWPp.call (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
    hcall hpcm hrunm hspm_align hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, A0, g]
    have hp1 : sessionImg0.FrozenLoaded sm ∧ sm.symtab = sessionImg0.symtab := ⟨hFm, hsymm⟩
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = valPtr ∧ sm.readReg64 .x2 = x.bufRef ∧
        ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 63 ∧
        Prost.BytesMergeCapOk cap0 ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length :=
      ⟨hx0m, hx1m, hx2m, Nat.lt_of_lt_of_le htail_lt (by decide),
        Prost.bytesMergeCapOk_of_len_lt32 htail_lt⟩
    rw [hspm, pure_true_emp_identityRootKeys hp1, pure_true_emp_identityRootKeys hp2, emp_sepConj, emp_sepConj]
    convert hm using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 hcs2
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, g]
    rw [mergeBytes_lengthDelimited_of_lt_128_identityRootKeys hb_lt]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜Prost.BytesMergeCapOk cap' x.tail.length⌝ ∗ vecU8At A0 valPtr cap' ptr' b) ⊢
        vecU8 A0 valPtr b :=
      Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
        Entails.pure_left fun _ =>
          Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))) ?_
    refine step_cbz_epilogue_identityRootKeys C ctl retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        vecU8 A0 valPtr b ∗
        Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
      hret hpc2 hrun2 (by reg_chain) halign (by reg_chain) hx0_2
      (by reg_chain) (by reg_chain) (by reg_chain)
      (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_identityRootKeys_gen P x valPtr w56 b htrf hx0f hpay hss, hspf, hcsf⟩

theorem mergeFieldGenIdentityRootKeys_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) abs := by
  let P234 : GenField → Prop := fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4
  unfold MergeFieldGenOk Serialization.OkAt
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [mergeFieldGenSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hP, hok, _, hlen, hF, hsym⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_identityRootKeys ∗ prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt s0.sp mergeFieldStack) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_intro_identityRootKeys hF.roData (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_identityRootKeys ∗ prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s0.sp mergeFieldStack,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys s0.sp, prostSSGAt_eq_split_identityRootKeys x.ss x.v]
  unfold mfRoBytes_identityRootKeys
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim (fun w80 => SepWPp.exists_elim (fun w72 =>
    SepWPp.exists_elim (fun w64 => SepWPp.exists_elim (fun w56 =>
      SepWPp.exists_elim (fun w48 => SepWPp.exists_elim (fun w40 =>
        SepWPp.exists_elim (fun w32 => SepWPp.exists_elim (fun w24 =>
          SepWPp.exists_elim (fun w16 => SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  mf234_fetches sessionImg0.base H
  dsimp only [tripleRatchetProgAt] at hpc
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  rcases genField_tag_234_cases hP hok with ⟨b, hfl_eq, hb⟩ | ⟨b, hfl_eq, hb⟩ | ⟨b, hfl_eq, hb⟩
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 2 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 - 12436)) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys_gen C ctl P234 hC.2.2.1 x 600#64 x.ss w56 x.v.lik b
        (F_ss := vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 3 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 - 12436)) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys_gen C ctl P234 hC.2.2.1 x 556#64 (x.ss + 0x18#64) w56 x.v.rik b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inl rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; dsimp only [SSG.apply, prostSSGRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 4 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 - 12436)) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys_gen C ctl P234 hC.2.2.1 x 460#64 (x.ss + 0x30#64) w56 x.v.root b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inr rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; dsimp only [SSG.apply, prostSSGRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
