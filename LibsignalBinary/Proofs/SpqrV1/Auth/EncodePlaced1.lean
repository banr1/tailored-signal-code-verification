/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import ProofLib.SepLogic.WPp

/-!
# Relocatable Proof of `encode<Authenticator> [local#1]` (Block 151)

Proves shared `[LibsignalPlacement]` step lemmas for blocks 151 and 314 together with
subroutine contracts for `prost::encoding::message::encode::<Authenticator, Vec<u8>> [local#1]`
(block 151).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)
open CryptoVerification.SpqrV1.Prost.MessageEncode

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_target_norm (base off target : BitVec 64) :
    (base + off) + (target - base - off) = target := by bv_omega

@[local arm64_norm] private theorem bv_bl_entry_norm (base target : BitVec 64) :
    base + (target - base - 0#64) = target := by bv_omega

/-! ## Shared Placed Step Lemmas (Blocks 151 and 314) -/

/-- Entry predicate for placed `encode<Authenticator> [local#1]` (block 151) or `[local#2]` (block 314). -/
def IsAuthEncodePlacedEntry [LibsignalPlacement] (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ H, prog = lsProg_151 H ∧ entry = (blkPl_151).base) ∨
  (∃ H, prog = lsProg_314 H ∧ entry = (blkPl_314).base)

/-- Shared header-tag push (`+44..+72`) on block 151 or 314. -/
theorem step_auth_push_hdr_placed [LibsignalPlacement] (A : RustAlloc)
    {prog : Program} {entry : BitVec 64} (hfn : IsAuthEncodePlacedEntry prog entry)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 44#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = authA)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 72#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; rw [vecU8At_open_one A v curCap curPtr curBs hlt, authPBElemsAt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 72#64)
  rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
    wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt, authPBElemsAt]; exact Entails.of_eq (by ac_rfl)
  }

/-- Shared payload-length computation (`+72..+144`, `+380..+396`) on block 151 or 314. -/
theorem step_auth_len_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} (hfn : IsAuthEncodePlacedEntry prog entry)
    (v authA sp : BitVec 64) (auth : AuthenticatorPB)
    (hrk_lt : auth.rootKey.length < 2 ^ 63) (hmk_lt : auth.macKey.length < 2 ^ 63)
    (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 72#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 144#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (authenticatorPBEncodedLen auth) → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length → sm.readReg64 .x21 = authA →
      sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  obtain ⟨hrk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.rootKey) (by omega)
  obtain ⟨hmk_beq, hmk_bne⟩ := ofNat_length_beq_zero_of_lt (bs := auth.macKey) (by omega)
  cases hrk : auth.rootKey.isEmpty <;> cases hmk : auth.macKey.isEmpty
  · have hrk_val := bv_bytesField_nonempty hrk; have hmk_val := bv_bytesField_nonempty hmk
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen auth.macKey)
        (b := bytesFieldEncodedLen auth.rootKey) (c := authenticatorPBEncodedLen auth) rfl hlen_fit
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 144#64)
    rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
      wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) }
  · have hrk_val := bv_bytesField_nonempty hrk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.rootKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hmk]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 144#64)
    rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
      wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by rw [htot_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) }
  · have hmk_val := bv_bytesField_nonempty hmk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.macKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 144#64)
    rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
      wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by rw [htot_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) }
  · have htot_eq : authenticatorPBEncodedLen auth = 0 := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk, hmk]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 144#64)
    rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
      wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by rw [htot_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv) }

/-- Shared `root_key` tag push (`+176..+204`) on block 151 or 314. -/
theorem step_auth_push_rk_tag_placed [LibsignalPlacement] (A : RustAlloc)
    {prog : Program} {entry : BitVec 64} (hfn : IsAuthEncodePlacedEntry prog entry)
    (v curCap curPtr authA rkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = rkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 204#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.rootKey.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      sm.readReg64 .x23 = rkPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x0a#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 204#64)
  rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
    wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x0a#8 hlt]; exact Entails.of_eq (by ac_rfl) }

/-- Shared `mac_key` tag push (`+280..+308`) on block 151 or 314. -/
theorem step_auth_push_mk_tag_placed [LibsignalPlacement] (A : RustAlloc)
    {prog : Program} {entry : BitVec 64} (hfn : IsAuthEncodePlacedEntry prog entry)
    (v curCap curPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 280#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = mkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 308#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.macKey.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = mkPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 308#64)
  rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
    wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre ?_
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
    rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by ac_rfl) }

/-- Shared epilogue (`+360..+380`) on block 151 or 314. -/
theorem step_auth_epilogue_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} (hfn : IsAuthEncodePlacedEntry prog entry) (sp : BitVec 64)
    {s0 s : State} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 360#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInvPlaced s0 sf → Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  rcases hfn with ⟨H, rfl, rfl⟩ | ⟨H, rfl, rfl⟩ <;> {
    apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre ?_
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by epochEncLen_cc_close) (hinv0.trans hinv1)))
    rw [stackAt_authEncode hres sp]; refine sepConj_mono_left (sepConj_mono_right ?_)
    exact Entails.sepExists_right (s0.readReg64 .fp) (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24) (Entails.sepExists_right (s0.readReg64 .x23)
        (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
          (Entails.sepExists_right (s0.readReg64 .x20)
            (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _)))))))) }

/-- Lifts a pinned `withLsCodeLoaded` contract to `authEncodeSpecOf`. -/
theorem authEncode_unpinned_of_pinned_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodeSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [authEncodeSpecOf] at hpre
  rw [authenticatorPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A)).pre
      ⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre⟩
  refine hpinned.mono_outcome ⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, authEncode_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## Block 151 Stage Lemmas -/

private theorem step_hdr_from_44_1_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64) (bs0 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hlt : bs0.length < curCap.toNat) (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hmk_lt : auth.macKey.length < 2 ^ 63) (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    (hfit : bs0.length + (authHeaderBytes auth).length ≤ curCap.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62)
    {s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = authA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs0 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_151).base + 152#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap1.toNat →
      (bs0.length + (authHeaderBytes auth).length ≤ curCap.toNat → cap1 = curCap ∧ ptr1 = curPtr) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap1 ptr1 (bs0 ++ authHeaderBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn1 : IsAuthEncodePlacedEntry (lsProg_151 H) (blkPl_151).base := Or.inl ⟨H, rfl, rfl⟩
  refine step_auth_push_hdr_placed A hfn1 v curCap curPtr authA rkPtr mkPtr sp bs0 auth hlt
    (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx21 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  refine step_auth_len_placed hfn1 v authA sp auth hrk_lt hmk_lt hlen_fit
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
  apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 148)); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  have hhdr_eq : (bs0 ++ [0x12#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint
        (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length =
      bs0.length + (authHeaderBytes auth).length := by
    simp only [authHeaderBytes, List.length_append, List.length_singleton]; omega
  have hvarint_fit : (bs0 ++ [0x12#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint
        (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length ≤ curCap.toNat ∨
      (bs0 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
    rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit
  refine step_ed_encode_varint_call_placed A henc
    (BitVec.ofNat 64 (authenticatorPBEncodedLen auth)) v curCap curPtr sp ((blkPl_151).base + 152#64)
    (bs0 ++ [0x12#8]) hvarint_fit (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2) (by ac_rfl) ?_
  intro s3 cap1 ptr1 hpc3 hrun3 hsp3 htr3 hcs23 hcs3 hge1 hpres1
  rw [hhdr_eq] at hpres1
  refine SepWPp.weaken_pre (by rw [bs0_append_authHeaderBytes bs0 auth]; exact Entails.of_eq (by ac_rfl))
    (hnext s3 cap1 ptr1 hpc3 hrun3 hsp3 htr3
      (by rw [hcs23.1]; simp only [arm64_norm, *]) (by rw [hcs23.2.1]; simp only [arm64_norm, *])
      (by rw [hcs23.2.2.1]; simp only [arm64_norm, *]) (by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *])
      hcs3 hge1 hpres1)

/-- Header-encoding stage (`+0..+152`) on block 151. -/
theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157)
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (v cap0 ptr0 authA rkPtr mkPtr sp : BitVec 64) (bs0 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hcap_le : bs0.length ≤ cap0.toNat) (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hmk_lt : auth.macKey.length < 2 ^ 63) (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    (hfit : bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat ∨
      bs0.length + (authHeaderBytes auth).length + 10 < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = authA) (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A v cap0 ptr0 bs0 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt sp (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_151).base + 152#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap1 ptr1 (bs0 ++ authHeaderBytes auth) ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
          A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗
          ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep44 := step_hdr_from_44_1_placed A H henc
  subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := authHeaderBytes_len_bounds auth
  let S := ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
    ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
    ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)
  rw [stackAt_authEncode hres sp, vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0, vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 157)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : cap0.toNat = bs0.length :=
      cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (authHeaderBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := reserveCap_one_bounds hcap_eq (by omega)
    refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap0 ptr0 sp
      ((blkPl_151).base + 420#64) bs0 1 hbound1 (F := authPBElemsAt authA rkPtr mkPtr auth ∗ S ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
      (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs0, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 44#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    exact hstep44 v newCap1 newPtr1 authA rkPtr mkPtr sp bs0 auth
      hlt1 hrk_lt hmk_lt hlen_fit (Or.inr (by omega)) (F := S ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 _ =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm
            (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega))))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat :=
      lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit44 : bs0.length + (authHeaderBytes auth).length ≤ cap0.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 44#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    exact hstep44 v cap0 ptr0 authA rkPtr mkPtr sp bs0 auth
      hlt0 hrk_lt hmk_lt hlen_fit hfit44 (F := S ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
      (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 hpres1 =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge1 hpres1))

private theorem step_rk_from_228_1_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hrk_ne : auth.rootKey.isEmpty = false) (hle : bs2.length + auth.rootKey.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length) (hx23 : s.readReg64 .x23 = rkPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_151).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ auth.rootKey) ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hrk_ne_nil : auth.rootKey ≠ [] := List.isEmpty_eq_false_iff.mp hrk_ne
  have hrk_pos : 0 < auth.rootKey.length := List.length_pos_of_ne_nil hrk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 auth.rootKey.length hle hcap_lt hptr_ne hrk_pos, authPBElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsMemcpySym); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_ed_memcpy_call_placed hmemcpy
    (curPtr + BitVec.ofNat 64 bs2.length) rkPtr sp ((blkPl_151).base + 248#64) auth.rootKey
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 auth.rootKey.length)
        (curCap.toNat - bs2.length - auth.rootKey.length) ∗
      ((authA + 8#64) ↦₆₄ rkPtr) ∗ ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((authA + 32#64) ↦₆₄ mkPtr) ∗ ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      (mkPtr ↦ₛ auth.macKey) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = authA := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 256#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 auth.rootKey hle hcap_lt hptr_ne hrk_ne_nil, authPBElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_rk_from_176_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157)
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hrk_ne : auth.rootKey.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat ∨
      bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 176#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = rkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_151).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ authRootKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep228 := step_rk_from_228_1_placed A H hmemcpy
  have hfn1 : IsAuthEncodePlacedEntry (lsProg_151 H) (blkPl_151).base := Or.inl ⟨H, rfl, rfl⟩
  have hrk_len := authRootKeyBytes_len_of_ne_empty auth hrk_ne
  refine step_auth_push_rk_tag_placed A hfn1 v curCap curPtr authA rkPtr sp bs1 auth hlt
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 148)); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hvarint_fit : (bs1 ++ [0x0a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (BitVec.ofNat 64 auth.rootKey.length) v curCap curPtr sp ((blkPl_151).base + 208#64)
    (bs1 ++ [0x0a#8]) hvarint_fit (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x0a#8]) ++
    CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.rootKey.length)
  have hbs2_len : bs2.length + auth.rootKey.length = bs1.length + (authRootKeyBytes auth).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hrk_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = authA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  have hx23_2 : s2.readReg64 .x23 = rkPtr := by rw [hcs12.2.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ authPBElemsAt authA rkPtr mkPtr auth ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hrk_lt63 : auth.rootKey.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + auth.rootKey.length
  · have hfit_rk : bs2.length + auth.rootKey.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.rootKey.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hrk_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_rk⟩ := elem_len_after_reserve_not_ult hfit_rk hneed
    apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 157)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
      ((blkPl_151).base + 464#64) bs2 auth.rootKey.length hbound_rk (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length auth.rootKey.length)
    change (BitVec.ofNat 64 auth.rootKey.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = authA := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_3 : s3.readReg64 .x23 = rkPtr := by rw [hcs23.2.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 228#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    exact hstep228 v cap3 ptr3 authA rkPtr mkPtr sp bs2 auth hrk_ne hle3
      (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_authRootKeyBytes_of_ne_empty bs1 auth hrk_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + auth.rootKey.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.rootKey.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hrk_lt63).mp h)
    have hpres_all : bs1.length + (authRootKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 228#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    exact hstep228 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth hrk_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_authRootKeyBytes_of_ne_empty bs1 auth hrk_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres_all))

/-- `root_key` field stage (`+152..+256`) on block 151. -/
theorem step_rk_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157)
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v cap1 ptr1 authA rkPtr mkPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (auth : AuthenticatorPB) (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hfit : bs1.length + (authRootKeyBytes auth).length ≤ cap1.toNat ∨
      bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_151).base + 256#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA → AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (authRootKeyBytes auth).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ authRootKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep176 := step_rk_from_176_1_placed hres A H henc hdoReserve hmemcpy
  subst hP
  have ⟨hrk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.rootKey) (by omega)
  cases hrk : auth.rootKey.isEmpty
  · have hrk_len := authRootKeyBytes_len_of_ne_empty auth hrk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader, authPBElemsAt]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 157)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap1.toNat = bs1.length :=
        cap_toNat_eq_of_beq hcap1 (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit2 : bs1.length + (authRootKeyBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap1 ptr1 sp
        ((blkPl_151).base + 440#64) bs1 1 hbound1 (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 176#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep176 v newCap1 newPtr1 authA rkPtr mkPtr sp bs1 auth hrk hlt1 (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 _ =>
          hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        lt_cap_toNat_of_beq_false hcap1_f hcap1_le (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 176#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep176 v cap1 ptr1 authA rkPtr mkPtr sp bs1 auth hrk hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 256#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_authRootKeyBytes_of_empty bs1 auth hrk]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_mk_from_332_1_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hmk_ne : auth.macKey.isEmpty = false) (hle : bs2.length + auth.macKey.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 332#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length) (hx21 : s.readReg64 .x21 = mkPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_151).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ auth.macKey) ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hmk_ne_nil : auth.macKey ≠ [] := List.isEmpty_eq_false_iff.mp hmk_ne
  have hmk_pos : 0 < auth.macKey.length := List.length_pos_of_ne_nil hmk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 auth.macKey.length hle hcap_lt hptr_ne hmk_pos, authPBElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsMemcpySym); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_ed_memcpy_call_placed hmemcpy
    (curPtr + BitVec.ofNat 64 bs2.length) mkPtr sp ((blkPl_151).base + 352#64) auth.macKey
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 auth.macKey.length)
        (curCap.toNat - bs2.length - auth.macKey.length) ∗
      ((authA + 8#64) ↦₆₄ rkPtr) ∗ ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      (rkPtr ↦ₛ auth.rootKey) ∗ ((authA + 32#64) ↦₆₄ mkPtr) ∗
      ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 360#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 auth.macKey hle hcap_lt hptr_ne hmk_ne_nil, authPBElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_mk_from_280_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157)
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hmk_ne : auth.macKey.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat ∨
      bs1.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 280#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = mkPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_151).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap3.toNat →
      (bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat → cap3 = curCap ∧ ptr3 = curPtr) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap3 ptr3 (bs1 ++ authMacKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep332 := step_mk_from_332_1_placed A H hmemcpy
  have hfn1 : IsAuthEncodePlacedEntry (lsProg_151 H) (blkPl_151).base := Or.inl ⟨H, rfl, rfl⟩
  have hmk_len := authMacKeyBytes_len_of_ne_empty auth hmk_ne
  refine step_auth_push_mk_tag_placed A hfn1 v curCap curPtr mkPtr sp bs1 auth hlt
    (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 148)); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hvarint_fit : (bs1 ++ [0x12#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (BitVec.ofNat 64 auth.macKey.length) v curCap curPtr sp ((blkPl_151).base + 312#64)
    (bs1 ++ [0x12#8]) hvarint_fit (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x12#8]) ++
    CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.macKey.length)
  have hbs2_len : bs2.length + auth.macKey.length = bs1.length + (authMacKeyBytes auth).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hmk_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = mkPtr := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ authPBElemsAt authA rkPtr mkPtr auth ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hmk_lt63 : auth.macKey.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + auth.macKey.length
  · have hfit_mk : bs2.length + auth.macKey.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.macKey.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hmk_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_mk⟩ := elem_len_after_reserve_not_ult hfit_mk hneed
    apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 157)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
      ((blkPl_151).base + 544#64) bs2 auth.macKey.length hbound_mk (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length auth.macKey.length)
    change (BitVec.ofNat 64 auth.macKey.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = mkPtr := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 332#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    exact hstep332 v cap3 ptr3 authA rkPtr mkPtr sp bs2 auth hmk_ne hle3
      (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs2]; rw [bs_append_authMacKeyBytes_of_ne_empty bs1 auth hmk_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + auth.macKey.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 auth.macKey.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hmk_lt63).mp h)
    have hpres_all : bs1.length + (authMacKeyBytes auth).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 332#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    exact hstep332 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth hmk_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs2]; rw [bs_append_authMacKeyBytes_of_ne_empty bs1 auth hmk_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hcsm hge2 hpres_all))

/-- `mac_key` field stage (`+256..+360`) on block 151. -/
theorem step_mk_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148)
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157)
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (v cap2 ptr2 authA rkPtr mkPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hmk_lt : auth.macKey.length < 2 ^ 63)
    (hfit : bs2.length + (authMacKeyBytes auth).length ≤ cap2.toNat ∨
      bs2.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_151).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗ authPBElemsAt authA rkPtr mkPtr auth ∗
      A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_151).base + 360#64 →
      sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (authMacKeyBytes auth).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      SepWPp (lsProg_151 H) ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ authMacKeyBytes auth) ∗
          authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_151 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep280 := step_mk_from_280_1_placed hres A H henc hdoReserve hmemcpy
  subst hP
  have ⟨hmk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.macKey) (by omega)
  cases hmk : auth.macKey.isEmpty
  · have hmk_len := authMacKeyBytes_len_of_ne_empty auth hmk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := authPBElemsAt authA rkPtr mkPtr auth ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by ac_rfl) fun hcap2_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader, authPBElemsAt]
    by_cases hcap2 : cap2 == BitVec.ofNat 64 bs2.length
    · apply SepWPp.of_sepWP_cs_placed (mid := (lsmpl.base 157)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap2.toNat = bs2.length :=
        cap_toNat_eq_of_beq hcap2 (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2))
      have hfit2 : bs2.length + (authMacKeyBytes auth).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
        ((blkPl_151).base + 520#64) bs2 1 hbound1 (F := authPBElemsAt authA rkPtr mkPtr auth ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs2, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 280#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep280 v newCap1 newPtr1 authA rkPtr mkPtr sp bs2 auth hmk hlt1 (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 _ =>
          hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hlt1 : bs2.length < cap2.toNat :=
        lt_cap_toNat_of_beq_false (Bool.eq_false_iff.mpr hcap2) hcap2_le
          (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2))
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 280#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep280 v cap2 ptr2 authA rkPtr mkPtr sp bs2 auth hmk hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, authPBElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_151).base + 360#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by rw [bs_append_authMacKeyBytes_of_empty bs2 auth hmk]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## Top-Level Contracts (Block 151) -/

/-- `SepWPp` correctness for placed `encode<Authenticator> [local#1]` (block 151). -/
theorem authEncode1_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {A : RustAlloc} {H : String → Option (State → State)} {x : AuthEncodePinnedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_151 H) (lsmpl.base 148) (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_151 H) (lsmpl.base 157) (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_151 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (blkPl_151).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (authEncodePinnedSpecOf resStack A).pre x s0 ∗ R) (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (lsProg_151 H) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (authEncodePinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s' ∧ StepInvPlaced s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have hfn1 : IsAuthEncodePlacedEntry (lsProg_151 H) (blkPl_151).base := Or.inl ⟨H, rfl, rfl⟩
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre; dsimp only [authEncodePinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure; obtain ⟨⟨hx0, hx1, hlen_fit⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hrk_lt, hmk_lt, hrk_cap0, hmk_cap0⟩ :=
    authenticatorPBPinnedAt_bounds_of_satisfies (A := A) (g := x.g) (authA := x.authA) (auth := x.auth)
      (F := vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  obtain ⟨hcap_le, hcap_lt, _⟩ :=
    vecU8At_bounds_of_satisfies (A := A) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := authenticatorPBPinnedAt A x.g x.authA x.auth ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A x.v x.cap x.ptr x.bs ∗
      authPBElemsAt x.authA x.g.rootKey.ptr x.g.macKey.ptr x.auth ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)) ∗ authPBRestAt A x.g x.authA x.auth) ∗ R := by
    rw [authenticatorPBPinnedAt_eq_elems A x.g x.authA x.auth hrk_cap0 hmk_cap0] at hpre_mem
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have htot_split := encodeAuthMsg_len_split x.auth; have htot_len := authenticatorPBEncodedLen_eq_fields_len x.auth
  have hlen_pb_lt : authenticatorPBEncodedLen x.auth < 2 ^ 64 := by
    rw [htot_len]; change (authRootKeyBytes x.auth).length + (authMacKeyBytes x.auth).length < 2 ^ 64
    rcases hlen_fit with h | h <;> omega
  have hfit_hdr : x.bs.length + (authHeaderBytes x.auth).length ≤ x.cap.toNat ∨
      x.bs.length + (authHeaderBytes x.auth).length + 10 < 2 ^ 62 := by
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  let Ssaved := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    authPBRestAt A x.g x.authA x.auth
  refine step_hdr_1_placed hres A H henc hdoReserve x.v x.cap x.ptr x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp x.bs x.auth hcap_le hrk_lt hmk_lt hlen_pb_lt hfit_hdr (F := authPBRestAt A x.g x.authA x.auth)
    hpc hrun rfl halign rfl hx0 hx1 (AuthEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hge1 hpres1
  have hfit_rk : (x.bs ++ authHeaderBytes x.auth).length + (authRootKeyBytes x.auth).length ≤ cap1.toNat ∨
      (x.bs ++ authHeaderBytes x.auth).length + (authRootKeyBytes x.auth).length + 10 < 2 ^ 62 := by
    rw [List.length_append]; rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_rk_1_placed hres A H henc hdoReserve hmemcpy x.v cap1 ptr1 x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp (x.bs ++ authHeaderBytes x.auth) x.auth hrk_lt hfit_rk (F := Ssaved)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 (by dsimp [Ssaved]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs2 hge2 hpres2
  have hfit_mk : ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length +
      (authMacKeyBytes x.auth).length ≤ cap2.toNat ∨
      ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth).length +
        (authMacKeyBytes x.auth).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_append]; rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_mk_1_placed hres A H henc hdoReserve hmemcpy x.v cap2 ptr2 x.authA x.g.rootKey.ptr x.g.macKey.ptr
    s0.sp ((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth) x.auth hmk_lt hfit_mk (F := Ssaved)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hcs2 (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hcs3 hge3 hpres3
  refine step_auth_epilogue_placed hres hfn1 s0.sp
    (F := vecU8At A x.v cap3 ptr3 (((x.bs ++ authHeaderBytes x.auth) ++ authRootKeyBytes x.auth) ++ authMacKeyBytes x.auth) ∗
      authPBElemsAt x.authA x.g.rootKey.ptr x.g.macKey.ptr x.auth ∗ A.pool ∗ authPBRestAt A x.g x.authA x.auth)
    hpc3 hrun3 hsp3 halign htr3 hcs3 (by dsimp [Ssaved]; ac_rfl) ?_
  intro sf _ _ hspf htrf hcc hinvf; refine ⟨fun hm => ?_, hspf, hcc, hinvf⟩
  have hge_all : x.cap.toNat ≤ cap3.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 hge3)
  have hpres_all : x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap3 = x.cap ∧ ptr3 = x.ptr := by
    intro hfit_cap; obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by rw [hc1, List.length_append]; omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by rw [hc2, hc1, List.length_append, List.length_append]; omega)
    exact ⟨hc3.trans (hc2.trans hc1), hp3.trans (hp2.trans hp1)⟩
  dsimp only [authEncodePinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]; refine ⟨cap3, ptr3, ?_⟩
  have hpure : (x.cap.toNat ≤ cap3.toNat ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap3 = x.cap ∧ ptr3 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj, authenticatorPBPinnedAt_eq_elems A x.g x.authA x.auth hrk_cap0 hmk_cap0,
    ← bs0_append_encodeAuthMsg x.bs x.auth]
  convert hm using 1; ac_rfl

def AuthEncode1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base (withLsCodeLoaded lsmpl (authEncodePinnedSpec A))

def AuthEncode1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base (withLsCodeLoaded lsmpl (authEncodeSpec A))

def AuthEncode1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base (withLsCodeLoaded lsmpl (authEncodePinnedSpecX A))

def AuthEncode1PlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base (withLsCodeLoaded lsmpl (authEncodeSpecX A))

theorem auth_encode_1_pinned_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) : AuthEncode1PinnedPlacedOkExt A H := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp; dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := authEncode1_gen_placed_ok (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_151 H) s0 hcl0 (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_151 H) s0 hcl0 (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem auth_encode_1_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) : AuthEncode1PlacedOkExt A H :=
  authEncode_unpinned_of_pinned_placed (auth_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem auth_encode_1_pinned_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) : AuthEncode1PinnedPlacedOkX A H := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp; dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := authEncode1_gen_placed_ok (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_151 H) s0 hcl0 (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk (callerProg := lsProg_151 H) s0 hcl0 (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem auth_encode_1_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) : AuthEncode1PlacedOkX A H :=
  authEncode_unpinned_of_pinned_placed (auth_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end CryptoVerification.SpqrV1.Auth
