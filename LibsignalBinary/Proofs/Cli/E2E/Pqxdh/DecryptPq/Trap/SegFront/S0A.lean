/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0Sym
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0A
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG Segment S0 Steps 1–4

Entry prologue, version checks, and `reaches_pc` steps (`+0x000 → +0x180`) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step1_reaches_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hlocal : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap img C A abs)
    (x : TryDecryptGhost) (F : SepProp) (s0 : State)
    (h_pc : s0.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret)
    (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA)
    (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hm : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ F) :
    let entry := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt img.base C abs) (entry + 84#64) s0
      (fun s1 =>
        s1.sp = sp ∧
        s1.spAligned = true ∧
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x20 = sp + 320#64 ∧
        s1.readReg64 .x21 = x.ss ∧
        s1.readReg64 .x22 = x.msgA ∧
        s1.readReg64 .x23 = sp + 1280#64 ∧
        (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s1.readReg64 .x25 = x.locA ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.mem ⊨
          localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 433#64) 975 ∗
          vecGhostAt A x.G.localIk x.ss ∗
          logOff img ∗
          memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, hm1⟩ :=
    s0_prologue_extract hm
  have hm_pre : s0.mem ⊨
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗
       words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗
       ((sp + 48#64) ↦₆₄ w_sp48) ∗
       vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗
       logOff img ∗
       stackAt sp localIdentityKeyStack) ∗
      (memRegion (sp + 8#64) 40 ∗
       memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ F) := by
    dsimp only [sp] at hm1 ⊢; convert hm1 using 1; sep_ac_rfl
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_prologue_wp_trap hlocal x s0 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48
    h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s1 _ _ ⟨P_f, hm_s1, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, hPf⟩
  refine ⟨hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s1
  have h48 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40 ⊢ memRegion sp 48 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion sp 0#64)) ?_
    rw [← memRegion_split sp 8 40 (by decide)]
    exact Entails.refl _
  have hm3 : s1.mem ⊨
      ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40) ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
       memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗
       vecGhostAt A x.G.localIk x.ss ∗
       logOff img ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp localIdentityKeyStack ∗
        memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) ∗
       tryDecryptSavedRegs s0.sp s0 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp localIdentityKeyStack (by decide)] at hm3
  have hm4 := Satisfies.mono (sepConj_mono_left h48) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step2_reaches_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (x : TryDecryptGhost) (F : SepProp) (s0 s1 : State)
    (h_pc : s1.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 84#64)
    (h_run : s1.status = .Running)
    (h_sp : s1.sp = s0.sp - 1504#64)
    (h_sp_align : s1.spAligned = true)
    (htr : s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx19 : s1.readReg64 .x19 = x.ret)
    (hx20 : s1.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s1.readReg64 .x21 = x.ss)
    (hx22 : s1.readReg64 .x22 = x.msgA)
    (hx23 : s1.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s1.readReg64 .x25 = x.locA)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hm : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ F) :
    let entry := (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt b C abs) (entry + 156#64) s1
      (fun s2 =>
        s2.sp = sp ∧
        s2.spAligned = true ∧
        (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.readReg64 .x0 = x.ss ∧
        s2.readReg64 .x8 = sp + 400#64 ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x20 = sp + 320#64 ∧
        s2.readReg64 .x21 = x.ss ∧
        s2.readReg64 .x22 = x.msgA ∧
        s2.readReg64 .x23 = sp + 1280#64 ∧
        (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s2.readReg64 .x25 = x.locA ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        (s2.mem ⊨
          memRegion (sp + 400#64) 34 ∗
          memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 434#64) 846 ∗
          ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          memRegion (sp + 1312#64) 96 ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hx29' : s1.readReg64 .x29 = sp + 1408#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, hloc_eq⟩ :=
    exists_localGroupA_of_length_32 (List.Vector.toList_length x.st.localIdentity.publicKey.bytes)
  have hm_433 : s1.mem ⊨ memRegion (sp + 433#64) 975 ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, hm_ext⟩ :=
    s0_step2_extract hm_433
  unfold localIdentityOkAt at hm_ext
  rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, hloc_eq (sp + 401#64)] at hm_ext
  have hm_pre : s1.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗
       localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗
       ((sp + 1112#64) ↦₈ u1112)) ∗
      (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗
       memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_copy_local_ik_wp_trap x s0 s1 b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31
    d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 u1104 u1112
    h_pc h_run h_sp h_sp_align hx20 hx21 hx23 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s2 _ _ ⟨P_f, hm_s2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2,
      hx23_2, hx24_2, hx25_2, hx29_2, hPf⟩
  refine ⟨hsp2, halign2, ⟨htr2.1.trans htr.1, htr2.2.trans htr.2⟩, hx0_2, hx8_2,
    hx19_2.trans hx19, hx20_2, hx21_2,
    hx22_2.trans hx22, hx23_2,
    by change (s2.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_2]; exact hx24,
    hx25_2.trans hx25, by rw [hx29_2]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s2
  rw [← localGroupA_eq_localGroupB, ← localGroupA_eq_localGroupB,
      ← hloc_eq (sp + 401#64), ← hloc_eq (sp + 1280#64)] at hm2
  have hm3 : s2.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ∗
      (memRegion (sp + 56#64) 344 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  have hm4 := Satisfies.mono (sepConj_mono_left (s0_step2_recombine sp x.st.localIdentity w2 b31))
      hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step3_reaches_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hrem : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap img C A abs)
    (x : TryDecryptGhost) (F : SepProp) (s0 s2 : State)
    (h_pc : s2.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 156#64)
    (h_run : s2.status = .Running)
    (h_sp : s2.sp = s0.sp - 1504#64)
    (h_sp_align : s2.spAligned = true)
    (htr : s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx0 : s2.readReg64 .x0 = x.ss)
    (hx8 : s2.readReg64 .x8 = (s0.sp - 1504#64) + 400#64)
    (hx19 : s2.readReg64 .x19 = x.ret)
    (hx20 : s2.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s2.readReg64 .x21 = x.ss)
    (hx22 : s2.readReg64 .x22 = x.msgA)
    (hx23 : s2.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s2.readReg64 .x25 = x.locA)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hm : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt img.base C abs) (entry + 160#64) s2
      (fun s3 =>
        s3.sp = sp ∧
        s3.spAligned = true ∧
        (s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = sp + 320#64 ∧
        s3.readReg64 .x21 = x.ss ∧
        s3.readReg64 .x22 = x.msgA ∧
        s3.readReg64 .x23 = sp + 1280#64 ∧
        (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s3.readReg64 .x25 = x.locA ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        (s3.mem ⊨
          vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)] at hm
  have hm_pre : s2.mem ⊨
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s2.sp + 400#64) 34 ∗
       logOff img ∗
       stackAt s2.sp remoteIdentityKeyStack) ∗
      (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - remoteIdentityKeyStack) ∗ F) := by
    rw [h_sp]; convert hm using 1; sep_ac_rfl
  have hx8' : s2.readReg64 .x8 = s2.sp + 400#64 := by rw [h_sp]; exact hx8
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_call_remote_ik_wp_trap hrem x s2 h_pc h_run h_sp_align hx0 hx8' hdeser_rem
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s3 _ _ ⟨P_f, hm_s3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
      hx25_3, hx29_3, hPf⟩
  refine ⟨hsp3.trans h_sp, halign3, ⟨htr3.1.trans htr.1, htr3.2.trans htr.2⟩, hx19_3.trans hx19,
    hx20_3.trans hx20,
    hx21_3.trans hx21, hx22_3.trans hx22, hx23_3.trans hx23,
    by change (s3.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_3]; exact hx24,
    hx25_3.trans hx25, hx29_3.trans hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s3
  rw [h_sp] at hm2
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)]
  convert hm2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step4_reaches_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (tag : BitVec 8)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s3.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 160#64)
    (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64)
    (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret)
    (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss)
    (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA)
    (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hent_402 :
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
        b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion ((s0.sp - 1504#64) + 402#64) 32)
    (hm : s3.mem ⊨
      ((s0.sp - 1504#64 + 400#64) ↦₈ 0#8) ∗
      ((s0.sp - 1504#64 + 401#64) ↦₈ tag) ∗
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
        b17 b18 b19 b20 b21 b22 w3 b31 ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ F) :
    let entry := (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt b C abs) (entry + 384#64) s3
      (fun s4 =>
        s4.sp = sp ∧
        s4.spAligned = true ∧
        (s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) ∧
        s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        s4.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧
        s4.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        s4.readReg64 .x19 = x.ret ∧
        s4.readReg64 .x20 = sp + 320#64 ∧
        s4.readReg64 .x21 = x.ss ∧
        s4.readReg64 .x22 = x.msgA ∧
        s4.readReg64 .x23 = sp + 1280#64 ∧
        (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s4.readReg64 .x25 = x.locA ∧
        s4.readReg64 .x29 = s0.sp - 96#64 ∧
        (s4.mem ⊨
          memRegion (sp + 400#64) 34 ∗
          ((sp + 352#64) ↦₆₄ w3) ∗
          ((sp + 360#64) ↦₈ b31) ∗
          ((sp + 976#64) ↦₃₂ w0) ∗
          ((sp + 980#64) ↦₈ b4) ∗
          ((sp + 981#64) ↦₈ b5) ∗
          memRegion (sp + 56#64) 296 ∗
          memRegion (sp + 361#64) 39 ∗
          memRegion (sp + 434#64) 542 ∗
          memRegion (sp + 982#64) 298 ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hm_sub : s3.mem ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
         b21 b22 w3 b31 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u352, u360, u976, u980, u981, hm_ext⟩ := s0_step4_extract hm_sub
  have hm_pre : s3.mem ⊨
      (((s3.sp + 400#64) ↦₈ 0#8) ∗
       ((s3.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s3.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
         b20 b21 b22 w3 b31 ∗
       ((s3.sp + 352#64) ↦₆₄ u352) ∗
       ((s3.sp + 360#64) ↦₈ u360) ∗
       ((s3.sp + 976#64) ↦₃₂ u976) ∗
       ((s3.sp + 980#64) ↦₈ u980) ∗
       ((s3.sp + 981#64) ↦₈ u981)) ∗
      (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s3.readReg64 .x20 = s3.sp + 320#64 := by rw [h_sp]; exact hx20
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_remote_ik_common_wp_trap s3 tag w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17
      b18 b19 b20 b21 b22
    w3 b31 u352 u360 u976 u980 u981 h_pc h_run h_sp_align hx20'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s4 _ _ ⟨P_f, hm_s4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4,
      hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hPf⟩
  refine ⟨hsp4.trans h_sp, halign4, ⟨htr4.1.trans htr.1, htr4.2.trans htr.2⟩, hx8_4, hx9_4,
    hx10_4, hx11_4,
    hx19_4.trans hx19, by rw [hx20_4, h_sp], hx21_4.trans hx21, hx22_4.trans hx22,
    hx23_4.trans hx23,
    by change (s4.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_4]; exact hx24,
    hx25_4.trans hx25, hx29_4.trans hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s4
  rw [h_sp] at hm2
  have h400_34 :
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
         b21 b22 w3 b31) ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
        (sepConj_mono (pointsTo8_entails_memRegion (sp + 401#64) tag) hent_402)) ?_
    rw [show sp + 402#64 = (sp + 401#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 1 32 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]
    exact Entails.refl _
  have hm3 : s4.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
         b21 b22 w3 b31) ∗
      (((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  exact Satisfies.mono (sepConj_mono_left h400_34) hm3

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
