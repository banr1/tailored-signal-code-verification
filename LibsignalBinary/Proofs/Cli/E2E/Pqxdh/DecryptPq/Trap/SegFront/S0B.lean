/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0A
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0Sym
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0A
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0B
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG Segment S0 Step 5 & `s0_ok_trap`

Remote-identity `is_same_account` check (`+0x180 → +0x1d8`) and `s0_ok_trap : S0Spec_trap`
on `trTrapProgAt`.
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

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tapeAfter_zero_trap (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step5_none_reaches_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (F : SepProp) (s0 s4 : State)
    (h_pc : s4.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64)
    (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64)
    (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx11 : s4.readReg64 .x11 = 0#64)
    (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hm : s4.mem ⊨ memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff img ∗ F) :
    let entry := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt img.base C abs) (entry + 472#64) s4
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ memRegion (sp + 56#64) 1352 ∗ logOff img ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [memRegion_split (sp + 56#64) 968 384 (by decide),
      show sp + 56#64 + 968#64 = sp + 1024#64 by bv_omega,
      memRegion_split (sp + 1024#64) 8 376 (by decide),
      show sp + 1024#64 + 8#64 = sp + 1032#64 by bv_omega,
      memRegion_split (sp + 1032#64) 8 368 (by decide),
      show sp + 1032#64 + 8#64 = sp + 1040#64 by bv_omega,
      memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 + 240#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm
  have hm1 : s4.mem ⊨ memRegion (sp + 1024#64) 8 ∗
      (memRegion (sp + 1032#64) 8 ∗ memRegion (sp + 1280#64) 8 ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗
        memRegion (sp + 1288#64) 120 ∗ F)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u1024, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : s4.mem ⊨ memRegion (sp + 1032#64) 8 ∗
      (((sp + 1024#64) ↦₆₄ u1024) ∗ memRegion (sp + 1280#64) 8 ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗
        memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1032, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : s4.mem ⊨ memRegion (sp + 1280#64) 8 ∗
      (((sp + 1024#64) ↦₆₄ u1024) ∗ ((sp + 1032#64) ↦₆₄ u1032) ∗ logOff img ∗
       (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗
        memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1280, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm_pre : s4.mem ⊨
      (((s4.sp + 1024#64) ↦₆₄ u1024) ∗
       ((s4.sp + 1032#64) ↦₆₄ u1032) ∗
       ((s4.sp + 1280#64) ↦₆₄ u1280) ∗
       logOff img) ∗
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗
       memRegion (sp + 1288#64) 120 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm3 ⊢; convert hm3 using 1; sep_ac_rfl
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by
    rw [hx29, h_sp]; bv_omega
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_remote_none_wp_trap himg s4 u1024 u1032 u1280 h_pc h_run h_sp_align hx11 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
      hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hsp5.trans h_sp, halign5, ⟨htr5.1.trans htr.1, htr5.2.trans htr.2⟩, hx1_5,
    hx19_5.trans hx19,
    hx20_5.trans hx20, hx21_5.trans hx21, hx22_5.trans hx22, hx23_5.trans hx23,
    by change (s5.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_5]; exact hx24,
    hx25_5.trans hx25, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm4 := Satisfies.mono (sepConj_mono_left hPf) hm_s5
  rw [h_sp] at hm4
  have hm5 : s5.mem ⊨
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1024#64) 16 ∗
       memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1280#64) 8 ∗
       memRegion (sp + 1288#64) 120) ∗ (logOff img ∗ F) := by
    dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
  rw [show sp + 1288#64 = (sp + 1280#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 = (sp + 1040#64) + 240#64 by bv_omega,
      ← memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 = (sp + 1024#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 1024#64) 16 368 (by decide),
      show sp + 1024#64 = (sp + 56#64) + 968#64 by bv_omega,
      ← memRegion_split (sp + 56#64) 968 384 (by decide)] at hm5
  exact hm5

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step5_some_reaches_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hsame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap b C abs)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64)
    (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64)
    (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3
          b31)
    (hdiff : x.st.localIdentity ≠ remIk)
    (hm : s4.mem ⊨
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗
      ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗
      ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt b C abs) (entry + 472#64) s4
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ stackAt sp isSameAccountStack ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
      db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    s0_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s4.sp + 400#64) ↦₆₄ u400) ∗
       ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗
       ((s4.sp + 360#64) ↦₈ b31) ∗
       ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗
       ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       stackAt s4.sp isSameAccountStack) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by
    rw [hx29, h_sp]; bv_omega
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_remote_some_wp_trap hsame x remIk s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
      b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
      db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
      hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hsp5.trans h_sp, halign5, ⟨htr5.1.trans htr.1, htr5.2.trans htr.2⟩, hx1_5,
    hx19_5.trans hx19,
    by rw [hx20_5, h_sp], hx21_5.trans hx21, hx22_5.trans hx22, hx23_5.trans hx23,
    by change (s5.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_5]; exact hx24,
    hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s5
  rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
       memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗
       ((sp + 360#64) ↦₈ b31) ∗
       memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗
       ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗
       memRegion (sp + 434#64) 542 ∗
       ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗
       ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp isSameAccountStack ∗
        memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack)) ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)] at hm3
  have hm4 := Satisfies.mono
    (sepConj_mono_left
      (s0_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
        (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step45_reaches_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hsame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap img.base C abs)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (h_pc : s3.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 160#64)
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
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity)
    (hm : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (trTrapProgAt img.base C abs) (entry + 472#64) s3
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    have hm_402 : s3.mem ⊨ memRegion (sp + 402#64) 32 ∗
        (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
         memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
         ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
        b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 hm_402
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm_402 ⊢; convert hm_402 using 1; sep_ac_rfl
    refine reaches_pc_seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step4_reaches_trap x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
        b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp
          + 402#64)) hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4,
        hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_re : s4.mem ⊨
        (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
         memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
         ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
         memRegion (sp + 982#64) 298 ∗
         ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96) ∗
        (logOff img ∗ (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    have hm4_1352 :=
        Satisfies.mono (sepConj_mono_left (s0_step4_to_memRegion_1352 sp x.st.localIdentity w0 b4
        b5 w3 b31)) hm4_re
    refine reaches_pc_mono
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step5_none_reaches_trap himg x (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4
          hx29_4 hm4_1352) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
        hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5,
        hx29_5, ?_⟩
    dsimp only [sp] at hm5; convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
        b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 :
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ⊢
          memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList
      rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step4_reaches_trap x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
        b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402
          hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4,
        hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hrem_d : ∀ a : BitVec 64,
        (a ↦ₛ remIk.publicKey.bytes.toList) =
          remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
            w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12
        b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk := by
      intro heq; apply hnot_self; rw [hrem_opt, heq]
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
        ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
        memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗ stackAt sp tryDecryptSubStack ∗
        (logOff img ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step5_some_reaches_trap hsame x remIk (logOff img ∗ F) s0 s4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
          hx24_4 hx25_4 hx29_4
        hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
        hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5,
        hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec_trap img C A ctl uuidTryParse S abs := by
  intro himg hlocal hremote hsame x R s0 h_pc h_run h_sp_align hpre
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗
      vecGhostAt A x.G.localIk x.ss ∗
      logOff img ∗
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab :=
    ⟨hfrozen0, hsym0⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have h_pc' : s0.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img =
      (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC
    rw [hentry]
  rw [h_segS1]
  refine reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step1_reaches_trap hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
      hm_s1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        logOff img ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step2_reaches_trap x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
      hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
      hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
       memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
       ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
       vecGhostAt A x.G.localIk x.ss ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step3_reaches_trap hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2
      hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (reaches_pc_callInv hinv3
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step45_reaches_trap himg hsame x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3 hx21_3
        hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
      hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
      (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Satisfies.mono (sepConj_mono_left (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tapeAfter_zero_trap img.base x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
