/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply

/-!
# Multi-Step Reachability & Callee Contracts for Segment S0 (`IdentityKeys`)

Composes the Segment S0 instruction steps across `local_identity_key`, `remote_identity_key`, and
`is_same_account`, and proves relocatable `[LibsignalPlacement]` contracts for `is_same_account`
(block `17`), `PublicKey::try_from` (block `211`), and `local_identity_key` (block `28`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem identityKeys_step1_reaches {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hlocal : LocalIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (F : SepProp) (s0 : State)
    (h_pc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA) (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA) (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hm : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ F) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt img.base ext) (entry + bv% (84)) s0
      (fun s1 => s1.sp = sp ∧ s1.spAligned = true ∧
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = sp + 320#64 ∧
        s1.readReg64 .x21 = x.ss ∧ s1.readReg64 .x22 = x.msgA ∧
        s1.readReg64 .x23 = sp + 1280#64 ∧ (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s1.readReg64 .x25 = x.locA ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.mem ⊨ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
          vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, hm1⟩ :=
    identityKeys_prologue_extract hm
  have hm_pre : s0.mem ⊨
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff img ∗ stackAt sp localIdentityKeyStack) ∗
      (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ F) := by
    dsimp only [sp] at hm1 ⊢; convert hm1 using 1; sep_ac_rfl
  have hwp := identityKeys_prologue_wp hlocal x s0 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48
    h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s1 _ _ ⟨P_f, hm_s1, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, hPf⟩
  refine ⟨hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s1
  have h48 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40 ⊢ memRegion sp 48 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion sp 0#64)) ?_
    rw [← memRegion_split sp 8 40 (by decide)]; exact Entails.refl _
  have hm3 : s1.mem ⊨
      ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40) ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp localIdentityKeyStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) ∗
       tryDecryptSavedRegs s0.sp s0 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp localIdentityKeyStack (by decide)] at hm3
  have hm4 := Satisfies.mono (sepConj_mono_left h48) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step2_reaches {b : BitVec 64}
    {ext : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s1 : State)
    (h_pc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 84#64)
    (h_run : s1.status = .Running) (h_sp : s1.sp = s0.sp - 1504#64) (h_sp_align : s1.spAligned = true)
    (htr : s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx19 : s1.readReg64 .x19 = x.ret) (hx20 : s1.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s1.readReg64 .x21 = x.ss) (hx22 : s1.readReg64 .x22 = x.msgA)
    (hx23 : s1.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s1.readReg64 .x25 = x.locA) (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hm : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ F) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt b ext) (entry + bv% (156)) s1
      (fun s2 => s2.sp = sp ∧ s2.spAligned = true ∧
        (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.readReg64 .x0 = x.ss ∧ s2.readReg64 .x8 = sp + 400#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = sp + 320#64 ∧
        s2.readReg64 .x21 = x.ss ∧ s2.readReg64 .x22 = x.msgA ∧
        s2.readReg64 .x23 = sp + 1280#64 ∧ (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s2.readReg64 .x25 = x.locA ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        (s2.mem ⊨ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          memRegion (sp + 1312#64) 96 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hx29' : s1.readReg64 .x29 = sp + 1408#64 := by rw [hx29]; dsimp only [sp]; bv_omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, hloc_eq⟩ :=
    exists_localGroupA_of_length_32 (List.Vector.toList_length x.st.localIdentity.publicKey.bytes)
  have hm_433 : s1.mem ⊨ memRegion (sp + 433#64) 975 ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, hm_ext⟩ :=
    identityKeys_step2_extract hm_433
  unfold localIdentityOkAt at hm_ext
  rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, hloc_eq (sp + 401#64)] at hm_ext
  have hm_pre : s1.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112)) ∗
      (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hwp := identityKeys_copy_local_ik_wp x s0 s1 b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31
    d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 u1104 u1112
    h_pc h_run h_sp h_sp_align hx20 hx21 hx23 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s2 _ _ ⟨P_f, hm_s2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hPf⟩
  refine ⟨hsp2, halign2, by reg_chain, hx0_2, hx8_2, by reg_chain, hx20_2, hx21_2,
    by reg_chain, hx23_2, by reg_chain, by reg_chain, by rw [hx29_2]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s2
  rw [← localGroupA_eq_localGroupB, ← localGroupA_eq_localGroupB,
      ← hloc_eq (sp + 401#64), ← hloc_eq (sp + 1280#64)] at hm2
  have hm3 : s2.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ∗
      (memRegion (sp + 56#64) 344 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  have hm4 := Satisfies.mono (sepConj_mono_left (identityKeys_step2_recombine sp x.st.localIdentity w2 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step3_reaches {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hrem : RemoteIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (F : SepProp) (s0 s2 : State)
    (h_pc : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 156#64)
    (h_run : s2.status = .Running) (h_sp : s2.sp = s0.sp - 1504#64) (h_sp_align : s2.spAligned = true)
    (htr : s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx0 : s2.readReg64 .x0 = x.ss) (hx8 : s2.readReg64 .x8 = (s0.sp - 1504#64) + 400#64)
    (hx19 : s2.readReg64 .x19 = x.ret) (hx20 : s2.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s2.readReg64 .x21 = x.ss) (hx22 : s2.readReg64 .x22 = x.msgA)
    (hx23 : s2.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s2.readReg64 .x25 = x.locA) (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hm : s2.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt img.base ext) (entry + bv% (160)) s2
      (fun s3 => s3.sp = sp ∧ s3.spAligned = true ∧
        (s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) ∧
        s3.readReg64 .x19 = x.ret ∧ s3.readReg64 .x20 = sp + 320#64 ∧
        s3.readReg64 .x21 = x.ss ∧ s3.readReg64 .x22 = x.msgA ∧
        s3.readReg64 .x23 = sp + 1280#64 ∧ (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s3.readReg64 .x25 = x.locA ∧ s3.readReg64 .x29 = s0.sp - 96#64 ∧
        (s3.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗ logOff img ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)] at hm
  have hm_pre : s2.mem ⊨
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s2.sp + 400#64) 34 ∗
       logOff img ∗ stackAt s2.sp remoteIdentityKeyStack) ∗
      (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - remoteIdentityKeyStack) ∗ F) := by
    rw [h_sp]; convert hm using 1; sep_ac_rfl
  have hx8' : s2.readReg64 .x8 = s2.sp + 400#64 := by rw [h_sp]; exact hx8
  have hwp := identityKeys_call_remote_ik_wp hrem x s2 h_pc h_run h_sp_align hx0 hx8' hdeser_rem
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s3 _ _ ⟨P_f, hm_s3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hPf⟩
  refine ⟨by reg_chain, halign3, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s3; rw [h_sp] at hm2
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)]
  convert hm2 using 1; sep_ac_rfl

theorem identityKeys_step4_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗ R) :
    ∃ (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8),
      m ⊨ (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
           ((sp + 976#64) ↦₃₂ u976) ∗ ((sp + 980#64) ↦₈ u980) ∗ ((sp + 981#64) ↦₈ u981)) ∗
          (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
           memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R) := by
  rw [memRegion_split (sp + 56#64) 296 48 (by decide),
      show sp + 56#64 + 296#64 = sp + 352#64 by bv_omega,
      memRegion_split (sp + 352#64) 8 40 (by decide),
      show sp + 352#64 + 8#64 = sp + 360#64 by bv_omega,
      memRegion_split (sp + 360#64) 1 39 (by decide),
      show sp + 360#64 + 1#64 = sp + 361#64 by bv_omega,
      memRegion_split (sp + 434#64) 542 304 (by decide),
      show sp + 434#64 + 542#64 = sp + 976#64 by bv_omega,
      memRegion_split (sp + 976#64) 4 300 (by decide),
      show sp + 976#64 + 4#64 = sp + 980#64 by bv_omega,
      memRegion_split (sp + 980#64) 1 299 (by decide),
      show sp + 980#64 + 1#64 = sp + 981#64 by bv_omega,
      memRegion_split (sp + 981#64) 1 298 (by decide),
      show sp + 981#64 + 1#64 = sp + 982#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 352#64) 8 ∗
      (memRegion (sp + 360#64) 1 ∗ memRegion (sp + 976#64) 4 ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨u352, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 360#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ memRegion (sp + 976#64) 4 ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u360, hm2⟩ := exists_word8_of_memRegion_1 hm2
  have hm3 : m ⊨ memRegion (sp + 976#64) 4 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       memRegion (sp + 980#64) 1 ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u976, hm3⟩ := exists_word32_of_memRegion_4 hm3
  have hm4 : m ⊨ memRegion (sp + 980#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       ((sp + 976#64) ↦₃₂ u976) ∗ memRegion (sp + 981#64) 1 ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm3 using 1; sep_ac_rfl
  obtain ⟨u980, hm4⟩ := exists_word8_of_memRegion_1 hm4
  have hm5 : m ⊨ memRegion (sp + 981#64) 1 ∗
      (((sp + 352#64) ↦₆₄ u352) ∗ ((sp + 360#64) ↦₈ u360) ∗
       ((sp + 976#64) ↦₃₂ u976) ∗ ((sp + 980#64) ↦₈ u980) ∗
       (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ R)) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨u981, hm5⟩ := exists_word8_of_memRegion_1 hm5
  refine ⟨u352, u360, u976, u980, u981, ?_⟩
  convert hm5 using 1; sep_ac_rfl

theorem identityKeys_step4_reaches {b : BitVec 64}
    {ext : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (tag : BitVec 8) (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 160#64)
    (h_run : s3.status = .Running) (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hent_402 : remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
      memRegion ((s0.sp - 1504#64) + 402#64) 32)
    (hm : s3.mem ⊨ ((s0.sp - 1504#64 + 400#64) ↦₈ 0#8) ∗ ((s0.sp - 1504#64 + 401#64) ↦₈ tag) ∗
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ F) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt b ext) (entry + bv% (384)) s3
      (fun s4 => s4.sp = sp ∧ s4.spAligned = true ∧
        (s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) ∧
        s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        s4.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧ s4.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        s4.readReg64 .x19 = x.ret ∧ s4.readReg64 .x20 = sp + 320#64 ∧
        s4.readReg64 .x21 = x.ss ∧ s4.readReg64 .x22 = x.msgA ∧
        s4.readReg64 .x23 = sp + 1280#64 ∧ (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s4.readReg64 .x25 = x.locA ∧ s4.readReg64 .x29 = s0.sp - 96#64 ∧
        (s4.mem ⊨ memRegion (sp + 400#64) 34 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
          ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
          memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
          memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hm_sub : s3.mem ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u352, u360, u976, u980, u981, hm_ext⟩ := identityKeys_step4_extract hm_sub
  have hm_pre : s3.mem ⊨
      (((s3.sp + 400#64) ↦₈ 0#8) ∗ ((s3.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s3.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s3.sp + 352#64) ↦₆₄ u352) ∗ ((s3.sp + 360#64) ↦₈ u360) ∗
       ((s3.sp + 976#64) ↦₃₂ u976) ∗ ((s3.sp + 980#64) ↦₈ u980) ∗ ((s3.sp + 981#64) ↦₈ u981)) ∗
      (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s3.readReg64 .x20 = s3.sp + 320#64 := by rw [h_sp]; exact hx20
  have hwp := identityKeys_remote_ik_common_wp s3 tag w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u352 u360 u976 u980 u981 h_pc h_run h_sp_align hx20'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s4 _ _ ⟨P_f, hm_s4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hPf⟩
  refine ⟨by reg_chain, halign4, by reg_chain, hx8_4, hx9_4, hx10_4, hx11_4,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s4; rw [h_sp] at hm2
  have h400_34 :
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 401#64) tag) hent_402)) ?_
    rw [show sp + 402#64 = (sp + 401#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 1 32 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]; exact Entails.refl _
  have hm3 : s4.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ∗
      (((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  exact Satisfies.mono (sepConj_mono_left h400_34) hm3

theorem identityKeys_step4_to_memRegion_1352 (sp : BitVec 64) (ik : IdentityKey)
    (w0 : BitVec 32) (b4 b5 : BitVec 8) (w3 : BitVec 64) (b31 : BitVec 8) :
    (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
     memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
     ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
     memRegion (sp + 982#64) 298 ∗ ((sp + 1280#64) ↦ₛ ik.publicKey.bytes.toList) ∗
     memRegion (sp + 1312#64) 96) ⊢
    memRegion (sp + 56#64) 1352 := by
  have hlen : ik.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion (sp + 352#64) w3)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 360#64) b31)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 976#64) w0)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 980#64) b4)
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 981#64) b5)
    (sepConj_mono_right (sepConj_mono_left (hlen ▸ pointsToBytes_entails_memRegion (sp + 1280#64) _)))))))))))) ?_
  rw [show sp + 1312#64 = (sp + 1280#64) + 32#64 by bv_omega,
      ← memRegion_split (sp + 1280#64) 32 96 (by decide),
      show sp + 1280#64 = (sp + 982#64) + 298#64 by bv_omega,
      ← memRegion_split (sp + 982#64) 298 128 (by decide),
      show sp + 982#64 = (sp + 981#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 981#64) 1 426 (by decide),
      show sp + 981#64 = (sp + 980#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 980#64) 1 427 (by decide),
      show sp + 980#64 = (sp + 976#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 976#64) 4 428 (by decide),
      show sp + 976#64 = (sp + 434#64) + 542#64 by bv_omega,
      ← memRegion_split (sp + 434#64) 542 432 (by decide),
      show sp + 434#64 = (sp + 400#64) + 34#64 by bv_omega,
      ← memRegion_split (sp + 400#64) 34 974 (by decide),
      show sp + 400#64 = (sp + 361#64) + 39#64 by bv_omega,
      ← memRegion_split (sp + 361#64) 39 1008 (by decide),
      show sp + 361#64 = (sp + 360#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 360#64) 1 1047 (by decide),
      show sp + 360#64 = (sp + 352#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 352#64) 8 1048 (by decide),
      show sp + 352#64 = (sp + 56#64) + 296#64 by bv_omega,
      ← memRegion_split (sp + 56#64) 296 1056 (by decide)]
  exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Blocks `17`, `43`, `44`) -/

open Arm64.Obj CryptoVerification CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex

namespace IdentityBitVecFacts

theorem le_of_eq32 {n k : Nat} (h : n = 32) (hk : k ≤ 32) : k ≤ n := h ▸ hk

theorem extractLsb'_append_lo {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : s + k ≤ w2) :
    (hi ++ lo).extractLsb' s k = lo.extractLsb' s k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; have hlt : s + i < w2 := by omega
  simp [BitVec.getLsbD_append, hi', hlt]

theorem extractLsb'_append_hi {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : w2 ≤ s) :
    (hi ++ lo).extractLsb' s k = hi.extractLsb' (s - w2) k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  have hnot : ¬(s + i < w2) := by omega
  have hsub : s - w2 + i = s + i - w2 := by omega
  simp [BitVec.getLsbD_append, hi', hnot, hsub]

theorem sub_add_ofNat_eq_sub (sp a b : BitVec 64) (n : Nat)
    (h : 0#64 - b = 0#64 - a + BitVec.ofNat 64 n) :
    sp - b = sp - a + BitVec.ofNat 64 n := by
  have h0 : ∀ x : BitVec 64, 0#64 - x = -x := BitVec.zero_sub
  rw [h0, h0] at h; rw [BitVec.sub_eq_add_neg, h, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]

theorem add_add_ofNat_eq_add (ret a b : BitVec 64) (n : Nat)
    (h : b = a + BitVec.ofNat 64 n) : ret + b = ret + a + BitVec.ofNat 64 n := by
  rw [h, BitVec.add_assoc]

theorem add_ofNat_eq_add (ret b : BitVec 64) (n : Nat)
    (h : b = BitVec.ofNat 64 n) : ret + b = ret + BitVec.ofNat 64 n := by rw [h]

theorem sub_add_eq_sub (sp a b k : BitVec 64) (h : 0#64 - a + k = 0#64 - b) :
    sp - a + k = sp - b := by
  have h0 : ∀ x : BitVec 64, 0#64 - x = -x := BitVec.zero_sub
  rw [h0, h0] at h; rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, h, ← BitVec.sub_eq_add_neg]

theorem add_add_eq_add (ret a b k : BitVec 64) (h : a + k = b) : ret + a + k = ret + b := by
  rw [BitVec.add_assoc, h]

end IdentityBitVecFacts

theorem deserialize_length_ge_33 {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 33 ≤ bs.length := by
  rcases bs with _ | ⟨t, rest⟩
  · simp [PublicKey.deserialize] at h
  · dsimp only [PublicKey.deserialize] at h; split at h
    · contradiction
    · split at h
      · simp only [List.length_cons]; omega
      · contradiction

set_option maxHeartbeats 1600000 in
theorem vecGhostAt_eq_of_pos (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) := by
  unfold vecGhostAt vecU8At vecHeader
  have h1 : ((a ↦₆₄ g.cap ∗ (a + 8#64) ↦₆₄ g.ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      if g.cap = 0 then emp else A.live g.ptr g.cap.toNat 1 ∗ g.ptr ↦ₛ g.bytes ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ⊢
      (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        a ↦₆₄ g.cap ∗ (a + 8#64) ↦₆₄ g.ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length ∗
        g.ptr ↦ₛ g.bytes ∗ A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    rw [sepConj_pure_left_comm]; apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : g.cap ≠ 0 := by intro h0; rw [h0] at hlen; change g.bytes.length ≤ 0 at hlen; omega
    simp only [hne, ↓reduceIte]; apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    have hcomm : (((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
      (A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗ memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) =
      ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
        (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗ memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by ac_rfl
    rw [hcomm]; exact Entails.refl _
  have h2 : (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        a ↦₆₄ g.cap ∗ (a + 8#64) ↦₆₄ g.ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length ∗
        g.ptr ↦ₛ g.bytes ∗ A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ⊢
      ((a ↦₆₄ g.cap ∗ (a + 8#64) ↦₆₄ g.ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        if g.cap = 0 then emp else A.live g.ptr g.cap.toNat 1 ∗ g.ptr ↦ₛ g.bytes ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : g.cap ≠ 0 := by intro h0; rw [h0] at hlen; change g.bytes.length ≤ 0 at hlen; omega
    rw [sepConj_pure_left_comm]; apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩; simp only [hne, ↓reduceIte]
    have hcomm : ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗ memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      (((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        (A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗ memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) := by ac_rfl
    rw [hcomm]; exact Entails.refl _
  exact ProofLib.Entails.antisymm h1 h2

def localKeyChunks (a : BitVec 64) (v0 : BitVec 64) (v8 : BitVec 8) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₈ v8) ∗ ((a + 9#64) ↦₃₂ v9) ∗
  ((a + 13#64) ↦₁₆ v13) ∗ ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

def remoteKeyChunks (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) = (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by simp [List.length_take, List.length_drop]; omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

theorem exists_localKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 64) (v8 : BitVec 8) (v9 : BitVec 32) (v13 : BitVec 16) (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = localKeyChunks a v0 v8 v9 v13 v15 v23 v31 := by
  refine ⟨pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
      (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8),
    bs.getD 8 0#8, pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 8 1 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (IdentityBitVecFacts.le_of_eq32 h (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      show BitVec.ofNat 64 8 = 8#64 from rfl, show BitVec.ofNat 64 1 = 1#64 from rfl,
      show BitVec.ofNat 64 4 = 4#64 from rfl, show BitVec.ofNat 64 2 = 2#64 from rfl]
  simp only [localKeyChunks, BitVec.add_assoc, BitVec.reduceAdd]

def sessionStateRest (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_split_upk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧ G.pending.isSome = st.pendingPreKey ∧
        G.regIds.length = 8 ∧ G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
      optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗ optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      sessionStateRest A ss G st := by
  unfold sessionStateAt sessionStateRest; ac_rfl

theorem sessionStateAt_of_cleared_upk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8)))
    (hloc : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hrem : match st.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hchains : G.chains.length = st.receiverChains.length) (hreg : G.regIds.length = 8)
    (hlik_len : G.localIk.bytes.length = 33) (hrik_len : st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :
    (optTailVecAt A 48 (ss + 0xf8#64) none ∗ optTailVecAt A 32 (ss + 0x128#64) none ∗ sessionStateRest A ss G st) ⊢
      sessionStateAt A ss { G with pending := none, kyber := none } st.clearUnacknowledgedPreKeyMessage := by
  rw [sessionStateAt_split_upk]
  dsimp only [SessionState.clearUnacknowledgedPreKeyMessage, sessionStateRest]
  exact Entails.pure_right ⟨hloc, hrem, hchains, rfl, hreg, hlik_len, hrik_len⟩ (Entails.refl _)

theorem optTailVecAt_none_of_cleared (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a ptr : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16)) ⊢ optTailVecAt A size a none := by
  unfold optTailVecAt; apply sepConj_mono_right
  have hsplit : size - 8 = 8 + (size - 16) := by omega
  rw [hsplit, ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16) (b' := a + 16#64) rfl (by bv_omega) (by omega)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) ptr)

theorem sessionStateAt_cleared_upk_intro (A : RustAlloc) (ss ptr1 ptr2 : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hloc : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hrem : match st.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hchains : G.chains.length = st.receiverChains.length) (hreg : G.regIds.length = 8)
    (hlik_len : G.localIk.bytes.length = 33) (hrik_len : st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :
    ((ss + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗ (ss + 256#64) ↦₆₄ ptr1 ∗ memRegion (ss + 264#64) 32 ∗
      (ss + 296#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗ (ss + 304#64) ↦₆₄ ptr2 ∗ memRegion (ss + 312#64) 16 ∗
      sessionStateRest A ss G st) ⊢
      sessionStateAt A ss { G with pending := none, kyber := none } st.clearUnacknowledgedPreKeyMessage := by
  have h1 := optTailVecAt_none_of_cleared A 48 (by decide) (by decide) (ss + 0xf8#64) ptr1
  have h2 := optTailVecAt_none_of_cleared A 32 (by decide) (by decide) (ss + 0x128#64) ptr2
  have h3 := sessionStateAt_of_cleared_upk A ss G st hloc hrem hchains hreg hlik_len hrik_len
  rw [show ss + 0xf8#64 + 8#64 = ss + 256#64 by bv_omega, show ss + 0xf8#64 + 16#64 = ss + 264#64 by bv_omega] at h1
  rw [show ss + 0x128#64 + 8#64 = ss + 304#64 by bv_omega, show ss + 0x128#64 + 16#64 = ss + 312#64 by bv_omega] at h2
  have hassoc :
      ((ss + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗ (ss + 256#64) ↦₆₄ ptr1 ∗ memRegion (ss + 264#64) 32 ∗
        (ss + 296#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗ (ss + 304#64) ↦₆₄ ptr2 ∗ memRegion (ss + 312#64) 16 ∗
        sessionStateRest A ss G st) =
      (((ss + 0xf8#64) ↦₆₄ noneCap ∗ (ss + 256#64) ↦₆₄ ptr1 ∗ memRegion (ss + 264#64) (48 - 16)) ∗
        ((ss + 0x128#64) ↦₆₄ noneCap ∗ (ss + 304#64) ↦₆₄ ptr2 ∗ memRegion (ss + 312#64) (32 - 16)) ∗
        sessionStateRest A ss G st) := by dsimp only [noneCap]; ac_rfl
  rw [hassoc]; exact Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) h3

theorem clearUpk_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {traceProp rest : State → Prop} (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

def clearUpkSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec ClearUpkGhost where
  pre := fun x s => ⌜s.readReg64 .x0 = x.ss⌝ ∗ sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp (32 + hookStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A x.ss { x.G with pending := none, kyber := none } x.st.clearUnacknowledgedPreKeyMessage ∗
      A.pool ∗ stackAt s0.sp (32 + hookStack)

private theorem publicKey_beq_false_of_ne_ik {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; apply h; cases ik1; cases ik2; cases heq; rfl

private theorem stackAt_isSameAccount_split_placed (sp : BitVec 64) :
    stackAt sp isSameAccountStack =
      memRegion (sp - 80#64 - 16#64) 16 ∗ memRegion (sp - 80#64 - 16#64 - 48#64) 48 ∗
      memRegion (sp - 80#64) 32 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountStack]
  rw [show sp - 80#64 - 16#64 - 48#64 = sp - 144#64 by bv_omega,
      show sp - 80#64 - 16#64 = sp - 96#64 by bv_omega,
      show (80 + 64 : Nat) = 144 from rfl, show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 96) (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 16) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) : memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  ac_rfl

/-- Block `17` (`<libsignal_protocol::identity_key::IdentityKey>::is_same_account`)
meets `isSameAccountSpec` under `[LibsignalPlacement]`. -/
theorem is_same_account_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl isSameAccountSpec) := by
  simp only [withLsCodeLoaded, isSameAccountSpec]
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec) :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMem_placed_ok h_bb
  have heq := ls_subroutine_ok_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) heq0
  simp only [withLsCodeLoaded, CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec] at heq
  wp_init x s0; obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x; dsimp only at *; subst h_2 h_3
  rw [stackAt_isSameAccount_split_placed s0.sp]; cells_unfold; wp_pull_exists
  have hne := publicKey_beq_false_of_ne_ik h_1
  apply sepWP_seq_lscl h (mid := lsmpl.base 212); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_apply; simp only [hne, Bool.false_eq_true, ↓reduceIte] at *; wp_steps; wp_done

/-- Block `211` (`<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from`)
meets `deserializePlacedSpec` under `[LibsignalPlacement]`. -/
theorem pkTryFrom_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base deserializePlacedSpec := by
  simp only [deserializePlacedSpec]; wp_init g s0
  obtain ⟨ptr, bs, pk, sret, tag0, out32⟩ := g; dsimp only at *; subst h_1 h_3
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h_5
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ := exists_unpack64_of_length_32 (bs := out32) h
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) h_5,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64), hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; wp_steps; wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      h_2, decide_eq_true_eq] at hcs; omega
  · wp_step; wp_if hcbz9
    · wp_steps; rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; wp_done
    · wp_steps; rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; wp_done

/-- Block `211` (`PublicKey::try_from`) meets `deserializeMemPlacedSpec` under `[LibsignalPlacement]`. -/
theorem pkTryFromMem_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base deserializeMemPlacedSpec := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeMemPlacedSpec, memRegion_33_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists] at hpre
  rcases hpre with ⟨tag0, out32, hpre⟩
  rw [satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1, hx8, hlt, hdeser⟩, hpre⟩
  rw [sepConj_pure_left_comm (ptr ↦ₛ bs), satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hout32, hpre⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, fun _ hpost => hpost⟩
  dsimp only [deserializePlacedSpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx8, hlt, hdeser, hout32⟩, hpre⟩

private theorem memRegion_33_localKeyChunks_placed (ret : BitVec 64) :
    memRegion ret 33 =
      (∃∗ b0 : BitVec 8, ret ↦₈ b0) ∗ (∃∗ v0 : BitVec 64, (ret + 1#64) ↦₆₄ v0) ∗
      (∃∗ v8 : BitVec 8, (ret + 9#64) ↦₈ v8) ∗ (∃∗ v9 : BitVec 32, (ret + 10#64) ↦₃₂ v9) ∗
      (∃∗ v13 : BitVec 16, (ret + 14#64) ↦₁₆ v13) ∗ (∃∗ v15 : BitVec 64, (ret + 16#64) ↦₆₄ v15) ∗
      (∃∗ v23 : BitVec 64, (ret + 24#64) ↦₆₄ v23) ∗ (∃∗ v31 : BitVec 8, (ret + 32#64) ↦₈ v31) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 1) (k := 32) (b' := ret + 1#64) rfl (IdentityBitVecFacts.add_ofNat_eq_add ret 1#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 1#64) (n := 8) (k := 24) (b' := ret + 9#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 1#64 9#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 9#64) (n := 1) (k := 23) (b' := ret + 10#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 9#64 10#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 10#64) (n := 4) (k := 19) (b' := ret + 14#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 10#64 14#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 2) (k := 17) (b' := ret + 16#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 14#64 16#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 9) (b' := ret + 24#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 16#64 24#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 1) (b' := ret + 32#64) rfl (IdentityBitVecFacts.add_add_ofNat_eq_add ret 24#64 32#64 8 rfl) (by decide),
      memRegion_one ret, memRegion_eight (ret + 1#64), memRegion_one (ret + 9#64),
      memRegion_four (ret + 10#64), memRegion_two (ret + 14#64),
      memRegion_eight (ret + 16#64), memRegion_eight (ret + 24#64), memRegion_one (ret + 32#64)]

private theorem stackAt_localIdentityKey_split_placed (sp : BitVec 64) :
    stackAt sp localIdentityKeyStack =
      memRegion (sp - 80#64) 33 ∗ memRegion (sp - 47#64) 15 ∗ cells (sp - 32#64) 3 ∗
      (∃∗ w : BitVec 32, (sp - 8#64) ↦₃₂ w) ∗ (∃∗ h : BitVec 16, (sp - 4#64) ↦₁₆ h) ∗ memRegion (sp - 2#64) 2 := by
  simp only [stackAt, localIdentityKeyStack]
  rw [show BitVec.ofNat 64 80 = 80#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 33) (k := 47) (b' := sp - 47#64) rfl (IdentityBitVecFacts.sub_add_ofNat_eq_sub sp 80#64 47#64 33 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 47#64) (n := 15) (k := 32) (b' := sp - 32#64) rfl (IdentityBitVecFacts.sub_add_ofNat_eq_sub sp 47#64 32#64 15 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8) (b' := sp - 8#64) rfl (IdentityBitVecFacts.sub_add_ofNat_eq_sub sp 32#64 8#64 24 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4) (b' := sp - 4#64) rfl (IdentityBitVecFacts.sub_add_ofNat_eq_sub sp 8#64 4#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2) (b' := sp - 2#64) rfl (IdentityBitVecFacts.sub_add_ofNat_eq_sub sp 4#64 2#64 2 rfl) (by decide),
      (memRegion_cells (sp - 32#64) 3 (by decide) : memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem stackAt_localIdentityKey_post_split (sp : BitVec 64) :
    stackAt sp localIdentityKeyStack =
      (∃∗ b0 : BitVec 8, (sp - 80#64) ↦₈ b0) ∗ (∃∗ v0 : BitVec 64, (sp - 79#64) ↦₆₄ v0) ∗
      (∃∗ v8 : BitVec 8, (sp - 71#64) ↦₈ v8) ∗ (∃∗ v9 : BitVec 32, (sp - 70#64) ↦₃₂ v9) ∗
      (∃∗ v13 : BitVec 16, (sp - 66#64) ↦₁₆ v13) ∗ (∃∗ v15 : BitVec 64, (sp - 64#64) ↦₆₄ v15) ∗
      (∃∗ v23 : BitVec 64, (sp - 56#64) ↦₆₄ v23) ∗ (∃∗ v31 : BitVec 8, (sp - 48#64) ↦₈ v31) ∗
      memRegion (sp - 47#64) 15 ∗ cells (sp - 32#64) 3 ∗
      (∃∗ w : BitVec 32, (sp - 8#64) ↦₃₂ w) ∗ (∃∗ h : BitVec 16, (sp - 4#64) ↦₁₆ h) ∗ memRegion (sp - 2#64) 2 := by
  rw [stackAt_localIdentityKey_split_placed sp, memRegion_33_localKeyChunks_placed (sp - 80#64),
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 79#64 1#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 71#64 9#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 70#64 10#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 66#64 14#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 64#64 16#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 56#64 24#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 80#64 48#64 32#64 rfl]
  simp only [sepConj_assoc]

/-- Block `28` (`<libsignal_protocol::state::session::SessionState>::local_identity_key`)
meets `localIdentityKeyPlacedSpec A` under `[LibsignalPlacement]`. -/
theorem local_identity_key_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_28).rebase (blkPl_28).base H) (blkPl_28).base
      (withLsCodeLoaded lsmpl (localIdentityKeyPlacedSpec A)) := by
  simp only [withLsCodeLoaded, localIdentityKeyPlacedSpec]
  have htry0 : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (lsmpl.base 211)
      deserializeMemPlacedSpec := pkTryFromMem_placed_ok H
  have htry := ls_subroutine_ok_of_block (callerProg := (blkPC_28).rebase (blkPl_28).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain htry0)
  simp only [withLsCodeLoaded, deserializeMemPlacedSpec] at htry
  wp_init x s0; obtain ⟨ss, g, ik, ret⟩ := x; dsimp only at *; subst h_2 h_3
  have hge33 := deserialize_length_ge_33 h_1
  have hpos : 0 < g.bytes.length := by omega
  have hbs32 : ik.publicKey.bytes.toList.length = 32 := by simp
  obtain ⟨v0, v8, v9, v13, v15, v23, v31, hchunks⟩ := exists_localKeyChunks_of_length_32 hbs32
  rw [vecGhostAt_eq_of_pos A g (s0.readReg64 (Reg.gpr 0#5)) hpos,
      memRegion_33_localKeyChunks_placed (s0.readReg64 (Reg.gpr 8#5)),
      localIdentityOkAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  nth_rw 1 [stackAt_localIdentityKey_split_placed s0.sp]
  rw [stackAt_localIdentityKey_post_split s0.sp]
  dsimp only [localKeyChunks]; cells_unfold; wp_pull_exists
  refine SepWP.pure_elim ?_; rintro ⟨hlen_cap, hcap_lt, hptr_ne⟩
  have hlen_lt : g.bytes.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_apply; rw [hchunks (s0.sp - 79#64)]; dsimp only [localKeyChunks]
  rw [IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 71#64 8#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 70#64 9#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 66#64 13#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 64#64 15#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 56#64 23#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub s0.sp 79#64 48#64 31#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 9#64 8#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 10#64 9#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 14#64 13#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 16#64 15#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 24#64 23#64 rfl,
      IdentityBitVecFacts.add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 32#64 31#64 rfl]
  wp_steps; wp_done

theorem identityKeys_step1_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (h_pc : s0.pc = (blkPl_131).base)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA) (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA) (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hm : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 84#64) s0
      (fun s1 => s1.sp = sp ∧ s1.spAligned = true ∧
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = sp + 320#64 ∧
        s1.readReg64 .x21 = x.ss ∧ s1.readReg64 .x22 = x.msgA ∧
        s1.readReg64 .x23 = sp + 1280#64 ∧ (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s1.readReg64 .x25 = x.locA ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.mem ⊨ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
          vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, hm1⟩ := identityKeys_prologue_extract hm
  have hm_pre : s0.mem ⊨
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack) ∗
      (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ F) := by
    dsimp only [sp] at hm1 ⊢; convert hm1 using 1; sep_ac_rfl
  have hlocal := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (local_identity_key_placed_ok A H)
  have hwp := identityKeys_prologue_wp_placed hlocal x s0 hcl r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48
    h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s1 _ _ ⟨P_f, hm_s1, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, hPf⟩
  refine ⟨hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s1
  have h48 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40 ⊢ memRegion sp 48 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion sp 0#64)) ?_
    rw [← memRegion_split sp 8 40 (by decide)]; exact Entails.refl _
  have hm3 : s1.mem ⊨
      ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40) ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp localIdentityKeyStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) ∗
       tryDecryptSavedRegs s0.sp s0 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp localIdentityKeyStack (by decide)] at hm3
  have hm4 := Satisfies.mono (sepConj_mono_left h48) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step2_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s1 : State)
    (h_pc : s1.pc = (blkPl_131).base + 84#64) (h_run : s1.status = .Running)
    (h_sp : s1.sp = s0.sp - 1504#64) (h_sp_align : s1.spAligned = true)
    (htr : s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx19 : s1.readReg64 .x19 = x.ret) (hx20 : s1.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s1.readReg64 .x21 = x.ss) (hx22 : s1.readReg64 .x22 = x.msgA)
    (hx23 : s1.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s1.readReg64 .x25 = x.locA) (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hm : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 156#64) s1
      (fun s2 => s2.sp = sp ∧ s2.spAligned = true ∧
        (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.readReg64 .x0 = x.ss ∧ s2.readReg64 .x8 = sp + 400#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = sp + 320#64 ∧
        s2.readReg64 .x21 = x.ss ∧ s2.readReg64 .x22 = x.msgA ∧
        s2.readReg64 .x23 = sp + 1280#64 ∧ (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s2.readReg64 .x25 = x.locA ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        (s2.mem ⊨ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          memRegion (sp + 1312#64) 96 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hx29' : s1.readReg64 .x29 = sp + 1408#64 := by rw [hx29]; dsimp only [sp]; bv_omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, hloc_eq⟩ :=
    exists_localGroupA_of_length_32 (List.Vector.toList_length x.st.localIdentity.publicKey.bytes)
  have hm_433 : s1.mem ⊨ memRegion (sp + 433#64) 975 ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, hm_ext⟩ := identityKeys_step2_extract hm_433
  unfold localIdentityOkAt at hm_ext
  rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, hloc_eq (sp + 401#64)] at hm_ext
  have hm_pre : s1.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112)) ∗
      (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hwp := identityKeys_copy_local_ik_wp_placed (H := H) x s0 s1 b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31
    d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 u1104 u1112 h_pc h_run h_sp h_sp_align hx20 hx21 hx23 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s2 _ _ ⟨P_f, hm_s2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hPf⟩
  refine ⟨hsp2, halign2, by reg_chain, hx0_2, hx8_2, by reg_chain, hx20_2, hx21_2,
    by reg_chain, hx23_2, by reg_chain, by reg_chain, by rw [hx29_2]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s2
  rw [← localGroupA_eq_localGroupB, ← localGroupA_eq_localGroupB,
      ← hloc_eq (sp + 401#64), ← hloc_eq (sp + 1280#64)] at hm2
  have hm3 : s2.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ∗
      (memRegion (sp + 56#64) 344 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  have hm4 := Satisfies.mono (sepConj_mono_left (identityKeys_step2_recombine sp x.st.localIdentity w2 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step3_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrem : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 29)
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (F : SepProp) (s0 s2 : State)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (h_pc : s2.pc = (blkPl_131).base + 156#64) (h_run : s2.status = .Running)
    (h_sp : s2.sp = s0.sp - 1504#64) (h_sp_align : s2.spAligned = true)
    (htr : s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx0 : s2.readReg64 .x0 = x.ss) (hx8 : s2.readReg64 .x8 = (s0.sp - 1504#64) + 400#64)
    (hx19 : s2.readReg64 .x19 = x.ret) (hx20 : s2.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s2.readReg64 .x21 = x.ss) (hx22 : s2.readReg64 .x22 = x.msgA)
    (hx23 : s2.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s2.readReg64 .x25 = x.locA) (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hdeser_rem : match x.st.remoteIdentity with | none => x.G.remoteIk.bytes = [] | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hm : s2.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 160#64) s2
      (fun s3 => s3.sp = sp ∧ s3.spAligned = true ∧
        (s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) ∧
        s3.readReg64 .x19 = x.ret ∧ s3.readReg64 .x20 = sp + 320#64 ∧
        s3.readReg64 .x21 = x.ss ∧ s3.readReg64 .x22 = x.msgA ∧
        s3.readReg64 .x23 = sp + 1280#64 ∧ (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s3.readReg64 .x25 = x.locA ∧ s3.readReg64 .x29 = s0.sp - 96#64 ∧
        (s3.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)] at hm
  have hm_pre : s2.mem ⊨
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s2.sp + 400#64) 34 ∗
       logOff tryDecryptDummyImg ∗ stackAt s2.sp remoteIdentityKeyStack) ∗
      (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - remoteIdentityKeyStack) ∗ F) := by
    rw [h_sp]; convert hm using 1; sep_ac_rfl
  have hx8' : s2.readReg64 .x8 = s2.sp + 400#64 := by rw [h_sp]; exact hx8
  have hwp := identityKeys_call_remote_ik_wp_placed hrem x s2 hcl h_pc h_run h_sp_align hx0 hx8' hdeser_rem
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s3 _ _ ⟨P_f, hm_s3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hPf⟩
  refine ⟨by reg_chain, halign3, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s3; rw [h_sp] at hm2
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)]
  convert hm2 using 1; sep_ac_rfl

theorem identityKeys_step4_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (tag : BitVec 8) (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s3.pc = (blkPl_131).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hent_402 : remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
      memRegion ((s0.sp - 1504#64) + 402#64) 32)
    (hm : s3.mem ⊨ ((s0.sp - 1504#64 + 400#64) ↦₈ 0#8) ∗ ((s0.sp - 1504#64 + 401#64) ↦₈ tag) ∗
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 384#64) s3
      (fun s4 => s4.sp = sp ∧ s4.spAligned = true ∧
        (s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) ∧
        s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        s4.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧ s4.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        s4.readReg64 .x19 = x.ret ∧ s4.readReg64 .x20 = sp + 320#64 ∧
        s4.readReg64 .x21 = x.ss ∧ s4.readReg64 .x22 = x.msgA ∧
        s4.readReg64 .x23 = sp + 1280#64 ∧ (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s4.readReg64 .x25 = x.locA ∧ s4.readReg64 .x29 = s0.sp - 96#64 ∧
        (s4.mem ⊨ memRegion (sp + 400#64) 34 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
          ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
          memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
          memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hm_sub : s3.mem ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u352, u360, u976, u980, u981, hm_ext⟩ := identityKeys_step4_extract hm_sub
  have hm_pre : s3.mem ⊨
      (((s3.sp + 400#64) ↦₈ 0#8) ∗ ((s3.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s3.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s3.sp + 352#64) ↦₆₄ u352) ∗ ((s3.sp + 360#64) ↦₈ u360) ∗
       ((s3.sp + 976#64) ↦₃₂ u976) ∗ ((s3.sp + 980#64) ↦₈ u980) ∗ ((s3.sp + 981#64) ↦₈ u981)) ∗
      (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s3.readReg64 .x20 = s3.sp + 320#64 := by rw [h_sp]; exact hx20
  have hwp := identityKeys_remote_ik_common_wp_placed (H := H) s3 tag w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u352 u360 u976 u980 u981 h_pc h_run h_sp_align hx20'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s4 _ _ ⟨P_f, hm_s4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hPf⟩
  refine ⟨by reg_chain, halign4, by reg_chain, hx8_4, hx9_4, hx10_4, hx11_4,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s4; rw [h_sp] at hm2
  have h400_34 :
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 401#64) tag) hent_402)) ?_
    rw [show sp + 402#64 = (sp + 401#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 1 32 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]; exact Entails.refl _
  have hm3 : s4.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ∗
      (((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  exact Satisfies.mono (sepConj_mono_left h400_34) hm3

theorem identityKeys_step5_none_reaches {img : Obj.Image}
    {ext : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (F : SepProp) (s0 s4 : State)
    (h_pc : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 384#64)
    (h_run : s4.status = .Running) (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx11 : s4.readReg64 .x11 = 0#64) (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA) (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hm : s4.mem ⊨ memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff img ∗ F) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt img.base ext) (entry + bv% (472)) s4
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ memRegion (sp + 56#64) 1352 ∗ logOff img ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [memRegion_split (sp + 56#64) 968 384 (by decide), show sp + 56#64 + 968#64 = sp + 1024#64 by bv_omega,
      memRegion_split (sp + 1024#64) 8 376 (by decide), show sp + 1024#64 + 8#64 = sp + 1032#64 by bv_omega,
      memRegion_split (sp + 1032#64) 8 368 (by decide), show sp + 1032#64 + 8#64 = sp + 1040#64 by bv_omega,
      memRegion_split (sp + 1040#64) 240 128 (by decide), show sp + 1040#64 + 240#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 8 120 (by decide), show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm
  have hm1 : s4.mem ⊨ memRegion (sp + 1024#64) 8 ∗
      (memRegion (sp + 1032#64) 8 ∗ memRegion (sp + 1280#64) 8 ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u1024, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : s4.mem ⊨ memRegion (sp + 1032#64) 8 ∗
      (((sp + 1024#64) ↦₆₄ u1024) ∗ memRegion (sp + 1280#64) 8 ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1032, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : s4.mem ⊨ memRegion (sp + 1280#64) 8 ∗
      (((sp + 1024#64) ↦₆₄ u1024) ∗ ((sp + 1032#64) ↦₆₄ u1032) ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1280, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm_pre : s4.mem ⊨
      (((s4.sp + 1024#64) ↦₆₄ u1024) ∗ ((s4.sp + 1032#64) ↦₆₄ u1032) ∗
       ((s4.sp + 1280#64) ↦₆₄ u1280) ∗ logOff img) ∗
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm3 ⊢; convert hm3 using 1; sep_ac_rfl
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hwp := identityKeys_remote_none_wp himg s4 u1024 u1032 u1280 h_pc h_run h_sp_align hx11 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm4 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm4
  have hm5 : s5.mem ⊨
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1024#64) 16 ∗ memRegion (sp + 1040#64) 240 ∗
       memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 120) ∗ (logOff img ∗ F) := by
    dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
  rw [show sp + 1288#64 = (sp + 1280#64) + 8#64 by bv_omega, ← memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 = (sp + 1040#64) + 240#64 by bv_omega, ← memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 = (sp + 1024#64) + 16#64 by bv_omega, ← memRegion_split (sp + 1024#64) 16 368 (by decide),
      show sp + 1024#64 = (sp + 56#64) + 968#64 by bv_omega, ← memRegion_split (sp + 56#64) 968 384 (by decide)] at hm5
  exact hm5

theorem identityKeys_step5_some_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗ R) :
    ∃ (u400 : BitVec 64) (u408 : BitVec 8) (dw0 : BitVec 32)
      (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
      (dw3 : BitVec 64) (db31 : BitVec 8),
      m ⊨ (((sp + 400#64) ↦₆₄ u400) ∗ ((sp + 408#64) ↦₈ u408) ∗
           remoteGroupD (sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31) ∗
          (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R) := by
  rw [memRegion_split (sp + 400#64) 8 26 (by decide), show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega,
      memRegion_split (sp + 408#64) 1 25 (by decide), show sp + 408#64 + 1#64 = sp + 409#64 by bv_omega,
      memRegion_split (sp + 56#64) 32 264 (by decide), show sp + 56#64 + 32#64 = sp + 88#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 400#64) 8 ∗ (memRegion (sp + 408#64) 1 ∗ memRegion (sp + 56#64) 32 ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by convert hm using 1; sep_ac_rfl
  obtain ⟨u400, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 408#64) 1 ∗ (((sp + 400#64) ↦₆₄ u400) ∗ memRegion (sp + 56#64) 32 ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by convert hm1 using 1; sep_ac_rfl
  obtain ⟨u408, hm2⟩ := exists_word8_of_memRegion_1 hm2
  have hm3 : m ⊨ memRegion (sp + 56#64) 32 ∗ (((sp + 400#64) ↦₆₄ u400) ∗ ((sp + 408#64) ↦₈ u408) ∗
       (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ R)) := by convert hm2 using 1; sep_ac_rfl
  obtain ⟨dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16, db17, db18, db19, db20, db21, db22, dw3, db31, _, hm3⟩ :=
    exists_remoteGroupC_of_memRegion_32 hm3
  rw [remoteGroupC_eq_remoteGroupD] at hm3
  refine ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16, db17, db18, db19, db20, db21, db22, dw3, db31, ?_⟩
  convert hm3 using 1; sep_ac_rfl

theorem identityKeys_step5_some_recombine (sp : BitVec 64) (locIk remIk : IdentityKey)
    (w0 : BitVec 32) (b4 b5 b6 : BitVec 8) (w401 w3 : BitVec 64) (b31 : BitVec 8) :
    (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ∗
     ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ memRegion (sp + 361#64) 39 ∗
     ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ w401) ∗ memRegion (sp + 409#64) 25 ∗
     memRegion (sp + 434#64) 542 ∗ ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗
     ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 982#64) 298 ∗
     ((sp + 1280#64) ↦ₛ locIk.publicKey.bytes.toList) ∗ memRegion (sp + 1312#64) 96) ⊢
    memRegion (sp + 56#64) 1352 := by
  have hrem_len : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have h56 : ((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ⊢
      memRegion (sp + 56#64) 296 := by
    refine Entails.trans (sepConj_mono_left (hrem_len ▸ pointsToBytes_entails_memRegion (sp + 56#64) _)) ?_
    rw [show sp + 88#64 = (sp + 56#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 56#64) 32 264 (by decide)]; exact Entails.refl _
  have h400 : ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ w401) ∗ memRegion (sp + 409#64) 25 ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) b6)
        (sepConj_mono_left (pointsTo64_entails_memRegion (sp + 401#64) w401))) ?_
    rw [show sp + 409#64 = (sp + 401#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 8 25 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]; exact Entails.refl _
  rw [← sepConj_assoc ((sp + 56#64) ↦ₛ _), ← sepConj_assoc ((sp + 401#64) ↦₆₄ _),
      ← sepConj_assoc ((sp + 400#64) ↦₈ _)]
  refine Entails.trans
    (sepConj_mono h56 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h400))))) ?_
  exact identityKeys_step4_to_memRegion_1352 sp locIk w0 b4 b5 w3 b31

theorem identityKeys_step5_none_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s4 : State)
    (h_pc : s4.pc = (blkPl_131).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx11 : s4.readReg64 .x11 = 0#64) (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA) (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hm : s4.mem ⊨ memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s4
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ memRegion (sp + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [memRegion_split (sp + 56#64) 968 384 (by decide), show sp + 56#64 + 968#64 = sp + 1024#64 by bv_omega,
      memRegion_split (sp + 1024#64) 8 376 (by decide), show sp + 1024#64 + 8#64 = sp + 1032#64 by bv_omega,
      memRegion_split (sp + 1032#64) 8 368 (by decide), show sp + 1032#64 + 8#64 = sp + 1040#64 by bv_omega,
      memRegion_split (sp + 1040#64) 240 128 (by decide), show sp + 1040#64 + 240#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 8 120 (by decide), show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm
  have hm1 : s4.mem ⊨ memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 8 ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u1024, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : s4.mem ⊨ memRegion (sp + 1032#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1032, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : s4.mem ⊨ memRegion (sp + 1280#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ ((sp + 1032#64) ↦₆₄ u1032) ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1280, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm_pre : s4.mem ⊨
      (((s4.sp + 1024#64) ↦₆₄ u1024) ∗ ((s4.sp + 1032#64) ↦₆₄ u1032) ∗ ((s4.sp + 1280#64) ↦₆₄ u1280) ∗ logOff tryDecryptDummyImg) ∗
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm3 ⊢; convert hm3 using 1; sep_ac_rfl
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hwp := identityKeys_remote_none_wp_placed (H := H) s4 u1024 u1032 u1280 h_pc h_run h_sp_align hx11 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm4 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm4
  have hm5 : s5.mem ⊨
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1024#64) 16 ∗ memRegion (sp + 1040#64) 240 ∗
       memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 120) ∗ (logOff tryDecryptDummyImg ∗ F) := by
    dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
  rw [show sp + 1288#64 = (sp + 1280#64) + 8#64 by bv_omega, ← memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 = (sp + 1040#64) + 240#64 by bv_omega, ← memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 = (sp + 1024#64) + 16#64 by bv_omega, ← memRegion_split (sp + 1024#64) 16 368 (by decide),
      show sp + 1024#64 = (sp + 56#64) + 968#64 by bv_omega, ← memRegion_split (sp + 56#64) 968 384 (by decide)] at hm5
  exact hm5

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
