/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `PreKeySignalMessage::new` Input Clones and Key Serialization

Stepping lemmas for the first half of the `PreKeySignalMessage::new` prologue (`+0x000..+0x1ac`):
frame setup and register spills, optional Kyber ciphertext clone, `PublicKey::serialize` calls on
`base_key` and `identity_key`, and `message.serialized` clone.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open ProofLib.ProgramReflection

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem sp_sub_96_add_96 (a : BitVec 64) : a - 96#64 + 96#64 = a := by bv_lin

@[local simp, local arm64_norm]
theorem noneCap_eq : noneCap = 18446744073709551615#64 := rfl

theorem getLsbD_63_ofNat_lt {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hn]
  exact Nat.testBit_lt_two_pow h

theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  exact SepWPp.weaken_pre h hwp

/-! ## `optKyberAt` Word-0 Decomposition -/

def optKyberRestAt (A : RustAlloc) (a ptr : BitVec 64) (kp : Option KyberPayload) : SepProp :=
  match kp with
  | none => memRegion (a + 8#64) 16
  | some k =>
    ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
      boxU8Buf A ptr k.ciphertext ∗ ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗
      memRegion (a + 0x14#64) 4

theorem optKyberAt_eq_word0_and_rest (A : RustAlloc) (a ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberAt A a ptr kp =
      (a ↦₆₄ (if kp.isSome then ptr else 0#64)) ∗ optKyberRestAt A a ptr kp := by
  cases kp with
  | none => rfl
  | some k =>
    simp only [Option.isSome_some, ↓reduceIte, optKyberRestAt, optKyberAt_some_eq]

theorem optKyberRestAt_some_eq (A : RustAlloc) (a ptr : BitVec 64) (k : KyberPayload) :
    optKyberRestAt A a ptr (some k) =
      ⌜ptr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
        ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        (if k.ciphertext = [] then emp else A.live ptr k.ciphertext.length 1 ∗ (ptr ↦ₛ k.ciphertext)) ∗
        ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗
        memRegion (a + 0x14#64) 4 := by
  unfold optKyberRestAt boxU8Buf
  ac_rfl

theorem optKyberAt_some_eq' (A : RustAlloc) (a ptr : BitVec 64) (k : KyberPayload)
    (hptr : ptr ≠ 0#64) (hlt : k.ciphertext.length < 2 ^ 63) :
    optKyberAt A a ptr (some k) =
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        (if k.ciphertext = [] then emp else A.live ptr k.ciphertext.length 1 ∗ (ptr ↦ₛ k.ciphertext)) ∗
        ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗
        memRegion (a + 0x14#64) 4 := by
  rw [optKyberAt_some_eq]
  unfold boxU8Buf
  have hp : (ptr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63) = True := eq_true ⟨hptr, hlt⟩
  rw [hp, pure_true, emp_sepConj]

theorem optKyberCopyBuf_some_eq' (A : RustAlloc) (ptr : BitVec 64) (k : KyberPayload)
    (hptr : ptr ≠ 0#64) (hlt : k.ciphertext.length < 2 ^ 63) :
    optKyberCopyBuf A ptr (some k) =
      (if k.ciphertext = [] then emp else A.live ptr k.ciphertext.length 1 ∗ (ptr ↦ₛ k.ciphertext)) := by
  dsimp only [optKyberCopyBuf, boxU8Buf]
  have hp : (ptr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63) = True := eq_true ⟨hptr, hlt⟩
  rw [hp, pure_true, emp_sepConj]

theorem pull_pure_second (P1 R : SepProp) (φ : Prop) :
    P1 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ R) := by ac_rfl

def kyberIdOf (kp : Option KyberPayload) (default : BitVec 32) : BitVec 32 :=
  match kp with | none => default | some k => k.preKeyId

/-! ## Frame Setup and Argument Spills (`+0x000..+0x04c`) -/

theorem preKeyMsg_entry_to_04c_wp_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 w304 w288 w280 : BitVec 64) (w292 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = x.regId)
    (hx2 : (s0.readReg64 .x2).setWidth 32 = if x.preKeyId.isSome then 1#32 else 0#32)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = x.spk)
    (hx5 : s0.readReg64 .x5 = x.kyA)
    (hx6 : s0.readReg64 .x6 = x.bkA)
    (hx7 : s0.readReg64 .x7 = x.ikA)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 76#64) s0
      ((sp0 ↦₆₄ x.msgA) ∗
       (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       ((sp0 - 304#64) ↦₆₄ w304) ∗
       ((sp0 - 292#64) ↦₃₂ w292) ∗
       ((sp0 - 288#64) ↦₆₄ w288) ∗
       ((sp0 - 280#64) ↦₆₄ w280) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 368#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x6 = x.bkA ∧
         s1.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64) ∧
         s1.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         s1.readReg64 .x22 = x.ikA ∧
         s1.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         s1.readReg64 .x25 = ((s0.readReg64 .x3).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x26 = ((s0.readReg64 .x0).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         s1.trace = s0.trace ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.msgA) ∗
          (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          preKeyMsgSavedRegs sp0 s0)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold preKeyMsgSavedRegs
  cells_unfold
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x00 0x48
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [← hx1, ← hx4]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_entry_to_04c_wp_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 w304 w288 w280 : BitVec 64) (w292 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = x.regId)
    (hx2 : (s0.readReg64 .x2).setWidth 32 = if x.preKeyId.isSome then 1#32 else 0#32)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = x.spk)
    (hx5 : s0.readReg64 .x5 = x.kyA)
    (hx6 : s0.readReg64 .x6 = x.bkA)
    (hx7 : s0.readReg64 .x7 = x.ikA)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 76#64) s0
      ((sp0 ↦₆₄ x.msgA) ∗
       (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       ((sp0 - 304#64) ↦₆₄ w304) ∗
       ((sp0 - 292#64) ↦₃₂ w292) ∗
       ((sp0 - 288#64) ↦₆₄ w288) ∗
       ((sp0 - 280#64) ↦₆₄ w280) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 368#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x6 = x.bkA ∧
         s1.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64) ∧
         s1.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         s1.readReg64 .x22 = x.ikA ∧
         s1.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         s1.readReg64 .x25 = ((s0.readReg64 .x3).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x26 = ((s0.readReg64 .x0).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         s1.trace = s0.trace ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.msgA) ∗
          (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          preKeyMsgSavedRegs sp0 s0)) :=
  preKeyMsg_entry_to_04c_wp_ext x sp0 w304 w288 w280 w292 s0 hpc hrun hsp hsp_align
    hx1 hx2 hx4 hx5 hx6 hx7 hx8

theorem preKeyMsg_entry_to_04c_wp {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (sp0 w304 w288 w280 : BitVec 64) (w292 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = x.regId)
    (hx2 : (s0.readReg64 .x2).setWidth 32 = if x.preKeyId.isSome then 1#32 else 0#32)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = x.spk)
    (hx5 : s0.readReg64 .x5 = x.kyA)
    (hx6 : s0.readReg64 .x6 = x.bkA)
    (hx7 : s0.readReg64 .x7 = x.ikA)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 76#64) s0
      ((sp0 ↦₆₄ x.msgA) ∗
       (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       ((sp0 - 304#64) ↦₆₄ w304) ∗
       ((sp0 - 292#64) ↦₃₂ w292) ∗
       ((sp0 - 288#64) ↦₆₄ w288) ∗
       ((sp0 - 280#64) ↦₆₄ w280) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 368#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x6 = x.bkA ∧
         s1.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64) ∧
         s1.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         s1.readReg64 .x22 = x.ikA ∧
         s1.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         s1.readReg64 .x25 = ((s0.readReg64 .x3).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x26 = ((s0.readReg64 .x0).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         s1.trace = s0.trace ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.msgA) ∗
          (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          preKeyMsgSavedRegs sp0 s0)) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWP_kit_of_trTrap (preKeyMsg_entry_to_04c_wp_trap x sp0 w304 w288 w280 w292 s0 hpc hrun hsp hsp_align hx1 hx2 hx4 hx5 hx6 hx7 hx8)

/-! ## Optional Kyber Ciphertext Clone (`+0x04c..+0x0e0`) -/

theorem preKeyMsg_kyber_clone_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (hSh : HookSat ext shimName sessionShimSpec)
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA)
    (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 224#64)
      s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
            ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗
            optKyberAt A x.kyA x.kyPtr x.kp ∗
            ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗
            ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
            ((sp0 - 312#64) ↦₆₄ w312') ∗
            ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
            ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
            optKyberCopyBuf A kyberCopyPtr x.kp ∗
            A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29
  cases hkp : x.kp with
  | none =>
    simp only [hkp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, kyberIdOf] at hx20 ⊢
    preKeyMsg_fetches_range b (Rust.withPanics ext) 0x4c 0x4c
    preKeyMsg_fetches_range b (Rust.withPanics ext) 0x6c 0x74
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right w320 (Entails.sepExists_right w312 ?_)
      refine Entails.pure_right (fun h => by cases h) ?_
      simp only [optKyberAt, optKyberRestAt, optKyberCopyBuf]
      exact entails_of_sep_focus (by sep_focus)
  | some k =>
    simp only [hkp, Option.isSome_some, ↓reduceIte, kyberIdOf,
      optKyberRestAt_some_eq, sepConj_assoc] at hx20 ⊢
    rw [pull_pure_second]
    refine SepWPp.pure_elim fun ⟨hky_ne, hct_lt⟩ => ?_
    simp only [← sepConj_assoc]
    have hky_beq : (x.kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hky_ne
    have hct_msb : (BitVec.ofNat 64 k.ciphertext.length).getLsbD 63 = false :=
      getLsbD_63_ofNat_lt hct_lt
    have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hct0 : BitVec.ofNat 64 k.ciphertext.length = 0#64
    · have hct_nil : k.ciphertext = [] := by
        have ht := congrArg BitVec.toNat hct0
        rw [hct_toNat, BitVec.toNat_zero] at ht
        exact List.eq_nil_of_length_eq_zero ht
      simp only [hct_nil, ↓reduceIte]
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0x4c 0x58
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0x78 0x84
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0xd0 0xdc
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
      examples_hide_fetches
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, List.length_nil, wp_norm, arm64_norm, *]
      · refine Entails.sepExists_right 1#64 (Entails.sepExists_right w312 ?_)
        have h1_ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
        simp only [sepConj_assoc]
        refine Entails.pure_right (fun _ => h1_ne) ?_
        rw [optKyberAt_some_eq' A x.kyA x.kyPtr k hky_ne hct_lt,
            optKyberCopyBuf_some_eq' A 1#64 k h1_ne hct_lt]
        simp only [hct_nil, List.length_nil, ↓reduceIte, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)
    · have hct_beq : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hct0
      have hct_pos : 0 < k.ciphertext.length := by
        by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
      have hct_ne_nil : k.ciphertext ≠ [] := List.ne_nil_of_length_pos hct_pos
      simp only [hct_ne_nil, ↓reduceIte]
      have hshim := preKeyMsg_shim_ok_ext (b := b) hSh
      have halloc := preKeyMsg_alloc_ok_ext (A := A) (b := b) hA
      have hmemcpy := preKeyMsg_memcpy_ok_ext (b := b) hMc
      have ho060 := @preKeyMsg_oom_at_060_ext b ext
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0x4c 0x58
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0x78 0xcc
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0xdc 0xdc
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ()) (F :=
          (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗
          ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗
          memRegion (x.kyA + 0x14#64) 4 ∗
          ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗
          ((sp0 - 320#64) ↦₆₄ w320) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 296#64) ↦₃₂ w296) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
        hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
        exact satisfies_of_sep_focus hm (by sep_focus)
      intro sf1 hpc1 hrun1 hsp1 hcs1
      rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
      simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
      simp only [noAllocShimSpec]
      refine SepWPp.pure_elim fun htr1 => ?_
      simp only [wp_norm, arm64_norm] at htr1
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := (k.ciphertext.length, 1))
        (F := (x.kyA ↦₆₄ x.kyPtr) ∗
              ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
              (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗
              ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗
              memRegion (x.kyA + 0x14#64) 4 ∗
              ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗
              ((sp0 - 320#64) ↦₆₄ w320) ∗
              ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
              ((sp0 - 296#64) ↦₃₂ w296) ∗
              ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
              memRegion (sp0 - 368#64 - 7824#64) 3728)
        halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
        simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
        refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
        exact satisfies_of_sep_focus hm (by sep_focus)
      intro sf2 hpc2 hrun2 hsp2 hcs2
      rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
      simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
      by_cases hoom : sf2.readReg64 .x0 = 0#64
      · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
        simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
        refine SepWPp.pure_elim fun htr2 => ?_
        simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
        apply SepWPp.of_sepWP (mid := entry + 96#64)
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        exact ho060 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
      · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
        simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
        refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
        have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
        simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - 0x15130))
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.kyPtr, k.ciphertext⟩)
          (F := (x.kyA ↦₆₄ x.kyPtr) ∗
                ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
                A.live x.kyPtr k.ciphertext.length 1 ∗
                ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗
                memRegion (x.kyA + 0x14#64) 4 ∗
                ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗
                ((sp0 - 320#64) ↦₆₄ sf2.readReg64 .x0) ∗
                ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
                ((sp0 - 296#64) ↦₃₂ w296) ∗
                ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
                A.live (sf2.readReg64 .x0) k.ciphertext.length 1 ∗
                A.pool ∗
                memRegion (sp0 - 368#64 - 7824#64) 3728)
          hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
          (by simp only [arm64_norm]; rfl) ?_
          (fun _ _ _ _ he => not_satisfies_false_sepConj he)
          (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
        · intro R' hm
          simp only [withStack, framelessMemcpySpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
          exact satisfies_of_sep_focus hm (by sep_focus)
        intro sf3 hpc3 hrun3 hsp3 hcs3
        rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
        simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
        simp only [withStack, framelessMemcpySpec, sepConj_assoc]
        refine SepWPp.pure_elim fun htr3 => ?_
        simp only [wp_norm, arm64_norm, htr2] at htr3
        apply SepWPp.of_sepWP_ret
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
        · simp only [State.spAligned, wp_norm, arm64_norm, *]
        · refine Entails.sepExists_right (sf2.readReg64 .x0) (Entails.sepExists_right x.bkA ?_)
          refine Entails.pure_right (fun _ => hoom) ?_
          rw [optKyberAt_some_eq' A x.kyA x.kyPtr k hky_ne hct_lt,
              optKyberCopyBuf_some_eq' A (sf2.readReg64 .x0) k hoom hct_lt,
              stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
          simp only [hct_ne_nil, ↓reduceIte, hsp2, wp_norm, arm64_norm]
          exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_kyber_clone_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA)
    (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 224#64)
      s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
            ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗
            optKyberAt A x.kyA x.kyPtr x.kp ∗
            ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗
            ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
            ((sp0 - 312#64) ↦₆₄ w312') ∗
            ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
            ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
            optKyberCopyBuf A kyberCopyPtr x.kp ∗
            A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_kyber_clone_wpp_ext (trTrap_allocHooks hA) trTrap_shim_hookSat trTrap_memcpy_hookSat
    x sp0 w320 w312 w324 w296 ver32 pkId32 s hpc hrun hsp hsp_align
    hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29

theorem preKeyMsg_kyber_clone_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA)
    (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 224#64)
      s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       optKyberRestAt A x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 =
           (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
            ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗
            optKyberAt A x.kyA x.kyPtr x.kp ∗
            ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗
            ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
            ((sp0 - 312#64) ↦₆₄ w312') ∗
            ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
            ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
            optKyberCopyBuf A kyberCopyPtr x.kp ∗
            A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWPp_kit_of_trTrap (preKeyMsg_kyber_clone_wpp_trap hA x sp0 w320 w312 w324 w296 ver32 pkId32 s hpc hrun hsp hsp_align hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29)

/-! ## `PublicKey::serialize` Calls (`+0x0e0..+0x0fc`) -/

theorem preKeyMsg_pk_serialize_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) (hSh : HookSat ext shimName sessionShimSpec)
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 252#64)
      s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hpk := preKeyMsg_publicKeySerialize_ok_ext (b := b) hA hSh
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0xe0 0xf8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 168340#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call
    (x := ⟨x.bkA, x.baseKey⟩)
    (F := (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ R' hm => by
      simpa only [publicKeySerializeSpec, allocFailedIn, State.trace_setPC,
        State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)] at hm
    simp only [publicKeySerializeSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [publicKeySerializeSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx1_1 htr1
  apply SepWPp.of_sepWP (mid := entry + 168340#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call
    (x := ⟨x.ikA, x.ik.publicKey⟩)
    (F := (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          boxU8Buf A (sf1.readReg64 .x0) x.baseKey.serialize ∗
          memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ R' hm => by
      simpa only [publicKeySerializeSpec, htr1, allocFailedIn, State.trace_setPC,
        State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    simp only [publicKeySerializeSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [publicKeySerializeSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
  apply SepWPp.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm, *]
  · rw [stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)]
    simp only [IdentityKey.serialize, hsp1, h28_2, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_pk_serialize_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32) (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 252#64) s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_pk_serialize_wpp_ext (trTrap_allocHooks hA) trTrap_shim_hookSat x sp0 kyberCap
    ver32 pkId32 s hpc hrun hsp hsp_align hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29

theorem preKeyMsg_pk_serialize_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 252#64)
      s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = x.bkA ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A (sm.readReg64 .x28) x.baseKey.serialize ∗
          boxU8Buf A (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWPp_kit_of_trTrap (preKeyMsg_pk_serialize_wpp_trap hA x sp0 kyberCap ver32 pkId32 s hpc hrun hsp hsp_align hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29)

/-! ## `SignalMessage.serialized` Clone (`+0x0fc..+0x1ac`) -/

def signalMessageRestBodyAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_expose_ser (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ⌜g.serPtr ≠ 0#64 ∧ m.serialized.length < 2 ^ 63⌝ ∗
      ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
        m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      ((a + 0x28#64) ↦₆₄ g.serPtr) ∗
      ((a + 0x30#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      (if m.serialized = [] then emp else A.live g.serPtr m.serialized.length 1 ∗ (g.serPtr ↦ₛ m.serialized)) ∗
      signalMessageRestBodyAt A g a m := by
  rw [signalMessageAt_eq_ser_and_rest]
  unfold boxU8Buf signalMessageRestAt signalMessageRestBodyAt
  ac_rfl

theorem preKeyMsg_msg_clone_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) (hSh : HookSat ext shimName sessionShimSpec)
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 428#64)
      s
      (signalMessageAt A x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₃₂ w328) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧
         9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧
         sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢
          signalMessageAt A x.msgG x.msgA x.msg ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29
  conv => arg 4; rw [signalMessageAt_expose_ser A x.msgG x.msgA x.msg]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt63⟩ => ?_
  refine SepWPp.pure_elim fun hser_wf => ?_
  simp only [← sepConj_assoc]
  have hser9 : 9 ≤ x.msg.serialized.length := by
    have := hser_wf.1
    change 8 + 1 ≤ x.msg.serialized.length at this
    omega
  have hser_lt40 : x.msg.serialized.length < 2 ^ 40 := hser_wf.2.1
  have hser_pos : 0 < x.msg.serialized.length := by omega
  have hser_ne_nil : x.msg.serialized ≠ [] := List.ne_nil_of_length_pos hser_pos
  have hser_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [hser_toNat, BitVec.toNat_zero] at ht
    omega
  have hser_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hser0
  have hser_msb : (BitVec.ofNat 64 x.msg.serialized.length).getLsbD 63 = false :=
    getLsbD_63_ofNat_lt hser_lt63
  simp only [hser_ne_nil, ↓reduceIte]
  have hshim := preKeyMsg_shim_ok_ext (b := b) hSh
  have halloc := preKeyMsg_alloc_ok_ext (b := b) hA
  have hmemcpy := preKeyMsg_memcpy_ok_ext (b := b) hMc
  have ho10c := @preKeyMsg_oom_at_10c_ext b ext
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0xfc 0x104
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x118 0x1a4
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ()) (F :=
      ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
      signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗
      ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
      ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗
      ((sp0 - 328#64) ↦₃₂ x.spk) ∗
      ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
      ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
      A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
    hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [noAllocShimSpec]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (x.msg.serialized.length, 1))
    (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
          ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
          (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
          signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
    simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  by_cases hoom : sf2.readReg64 .x0 = 0#64
  · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
    apply SepWPp.of_sepWP (mid := entry + 268#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact ho10c (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
  · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - 0x15130))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.msgG.serPtr, x.msg.serialized⟩)
      (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
            ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
            A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
            signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗
            ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
            ((sp0 - 344#64) ↦₆₄ 33#64) ∗
            ((sp0 - 332#64) ↦₃₂ ver32) ∗
            ((sp0 - 328#64) ↦₃₂ x.spk) ∗
            ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
            ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
            A.live (sf2.readReg64 .x0) x.msg.serialized.length 1 ∗
            A.pool ∗
            memRegion (sp0 - 368#64 - 7824#64) 3728)
      hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [withStack, framelessMemcpySpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hpc3 hrun3 hsp3 hcs3
    rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [withStack, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
      exact ⟨hser_lt40, hoom⟩
    · rw [signalMessageAt_expose_ser A x.msgG x.msgA x.msg,
          stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
      have hp_msg1 : (x.msgG.serPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63) = True :=
        eq_true ⟨hser_ne, hser_lt63⟩
      have hp_msg2 :
          (macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 ∧
            x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
            (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)) = True :=
        eq_true hser_wf
      rw [hp_msg1, hp_msg2, pure_true, emp_sepConj, emp_sepConj]
      simp only [wp_norm, arm64_norm, hsp2, hser_ne_nil, ↓reduceIte]
      unfold boxU8Buf
      have hp_copy : (sf2.readReg64 (Reg.gpr 0#5) ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63) = True :=
        eq_true ⟨hoom, hser_lt63⟩
      rw [hp_copy, pure_true, emp_sepConj]
      simp only [hser_ne_nil, ↓reduceIte, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_msg_clone_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32) (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 428#64) s
      (signalMessageAt A x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₃₂ w328) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x22 = 33#64 ∧ sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
         9 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 ∧
         sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢ signalMessageAt A x.msgG x.msgA x.msg ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_msg_clone_wpp_ext (trTrap_allocHooks hA) trTrap_shim_hookSat trTrap_memcpy_hookSat
    x sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 w332 w328 ver32 pkId32 s hpc hrun hsp hsp_align
    hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29

theorem preKeyMsg_msg_clone_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 428#64)
      s
      (signalMessageAt A x.msgG x.msgA x.msg ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₃₂ w328) ∗
       ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧
         9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧
         sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢
          signalMessageAt A x.msgG x.msgA x.msg ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗
          ((sp0 - 332#64) ↦₃₂ ver32) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A (sm.readReg64 .x26) x.msg.serialized ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWPp_kit_of_trTrap (preKeyMsg_msg_clone_wpp_trap hA x sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 w332 w328 ver32 pkId32 s hpc hrun hsp hsp_align hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29)

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

theorem preKeyMsg_entry_to_04c_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (sp0 w304 w288 w280 : BitVec 64) (w292 : BitVec 32) (s0 : State)
    (hpc : s0.pc = (blkPl_41).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = x.regId)
    (hx2 : (s0.readReg64 .x2).setWidth 32 = if x.preKeyId.isSome then 1#32 else 0#32)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = x.spk)
    (hx5 : s0.readReg64 .x5 = x.kyA) (hx6 : s0.readReg64 .x6 = x.bkA)
    (hx7 : s0.readReg64 .x7 = x.ikA) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (lsProg_41 H) ((blkPl_41).base + 76#64) s0
      ((sp0 ↦₆₄ x.msgA) ∗ (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
       ((sp0 - 304#64) ↦₆₄ w304) ∗ ((sp0 - 292#64) ↦₃₂ w292) ∗
       ((sp0 - 288#64) ↦₆₄ w288) ∗ ((sp0 - 280#64) ↦₆₄ w280) ∗ cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 368#64 ∧ s1.spAligned = true ∧ s1.readReg64 .x6 = x.bkA ∧
         s1.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64) ∧
         s1.readReg64 .x21 = x.spk.zeroExtend 64 ∧ s1.readReg64 .x22 = x.ikA ∧
         s1.readReg64 .x23 = x.regId.zeroExtend 64 ∧
         s1.readReg64 .x25 = ((s0.readReg64 .x3).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x26 = ((s0.readReg64 .x0).setWidth 32).zeroExtend 64 ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧ s1.trace = s0.trace ∧
         calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        (P1 ⊢ (sp0 ↦₆₄ x.msgA) ∗ (x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗ ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ preKeyMsgSavedRegs sp0 s0)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold preKeyMsgSavedRegs; cells_unfold
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [← hx1, ← hx4]; simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [arm64_norm]; exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_kyber_clone_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (sp0 w320 w312 : BitVec 64) (w324 w296 ver32 pkId32 : BitVec 32) (s : State)
    (hpc : s.pc = (blkPl_41).base + 76#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx20 : s.readReg64 .x20 = (if x.kp.isSome then x.kyPtr else 0#64))
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 224#64) s
      ((x.kyA ↦₆₄ (if x.kp.isSome then x.kyPtr else 0#64)) ∗ optKyberRestAt A x.kyA x.kyPtr x.kp ∗
       ((sp0 - 324#64) ↦₃₂ w324) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x6 = x.bkA ∧
         sm.readReg64 .x19 = (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = x.ikA ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x26 = ver32.zeroExtend 64 ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ kyberCopyPtr : BitVec 64, ∃∗ w312' : BitVec 64,
          ⌜x.kp.isSome → kyberCopyPtr ≠ 0#64⌝ ∗ optKyberAt A x.kyA x.kyPtr x.kp ∗
          ((sp0 - 324#64) ↦₃₂ kyberIdOf x.kp w324) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 312#64) ↦₆₄ w312') ∗ ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ optKyberCopyBuf A kyberCopyPtr x.kp ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx20 hx21 hx22 hx23 hx25 hx26 hx29
  cases hkp : x.kp with
  | none =>
    simp only [hkp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, kyberIdOf] at hx20 ⊢
    apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · refine Entails.sepExists_right w320 (Entails.sepExists_right w312 (Entails.pure_right (fun h => by cases h) ?_))
      simp only [optKyberAt, optKyberRestAt, optKyberCopyBuf]; exact entails_of_sep_focus (by sep_focus)
  | some k =>
    simp only [hkp, Option.isSome_some, ↓reduceIte, kyberIdOf, optKyberRestAt_some_eq, sepConj_assoc] at hx20 ⊢
    rw [pull_pure_second]; refine SepWPp.pure_elim fun ⟨hky_ne, hct_lt⟩ => ?_
    simp only [← sepConj_assoc]
    have hky_beq : (x.kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hky_ne
    have hct_msb : (BitVec.ofNat 64 k.ciphertext.length).getLsbD 63 = false := getLsbD_63_ofNat_lt hct_lt
    have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hct0 : BitVec.ofNat 64 k.ciphertext.length = 0#64
    · have hct_nil : k.ciphertext = [] := by
        have ht := congrArg BitVec.toNat hct0; rw [hct_toNat, BitVec.toNat_zero] at ht
        exact List.eq_nil_of_length_eq_zero ht
      simp only [hct_nil, ↓reduceIte]; apply SepWPp.of_sepWP_ret; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, List.length_nil, wp_norm, arm64_norm, *]
      · refine Entails.sepExists_right 1#64 (Entails.sepExists_right w312 ?_)
        have h1_ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
        simp only [sepConj_assoc]; refine Entails.pure_right (fun _ => h1_ne) ?_
        rw [optKyberAt_some_eq' A x.kyA x.kyPtr k hky_ne hct_lt, optKyberCopyBuf_some_eq' A 1#64 k h1_ne hct_lt]
        simp only [hct_nil, List.length_nil, ↓reduceIte, arm64_norm]; exact entails_of_sep_focus (by sep_focus)
    · have hct_beq : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false := beq_eq_false_iff_ne.mpr hct0
      have hct_pos : 0 < k.ciphertext.length := by
        by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
      have hct_ne_nil : k.ciphertext ≠ [] := List.ne_nil_of_length_pos hct_pos
      simp only [hct_ne_nil, ↓reduceIte]
      have h_shim := preKeyMsg_shim_placed_ok hshim
      have h_alloc := preKeyMsg_alloc_placed_ok halloc
      have h_memcpy := preKeyMsg_memcpy_placed_ok hmemcpy
      apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym); wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ()) (F := (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗ ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗
          memRegion (x.kyA + 0x14#64) 4 ∗ ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
        h_shim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [arm64_norm]; rfl)
        (fun R' hm => by simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢; exact satisfies_of_sep_focus hm (by sep_focus))
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
      simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
      simp only [noAllocShimSpec]; refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1
      apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym); wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := (k.ciphertext.length, 1)) (F := (x.kyA ↦₆₄ x.kyPtr) ∗
          ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
          (A.live x.kyPtr k.ciphertext.length 1 ∗ (x.kyPtr ↦ₛ k.ciphertext)) ∗ ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗
          memRegion (x.kyA + 0x14#64) 4 ∗ ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗ ((sp0 - 320#64) ↦₆₄ w320) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗ ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
        h_alloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [arm64_norm]; rfl)
        (fun R' hm => by
          rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
          simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
          exact ⟨⟨⟨0, rfl⟩, by omega⟩, satisfies_of_sep_focus hm (by sep_focus)⟩)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
      simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
      by_cases hoom : sf2.readReg64 .x0 = 0#64
      · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
        simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
        refine SepWPp.pure_elim fun htr2 => ?_; simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
        apply SepWPp.of_sepWP (mid := (blkPl_41).base + 96#64); wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        exact preKeyMsg_oom_at_060_placed hpanic (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
        simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
        refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
        have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
        simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
        apply SepWPp.of_sepWP (mid := lsρ "memcpy"); wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.kyPtr, k.ciphertext⟩) (F := (x.kyA ↦₆₄ x.kyPtr) ∗
            ((x.kyA + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗ A.live x.kyPtr k.ciphertext.length 1 ∗
            ((x.kyA + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (x.kyA + 0x14#64) 4 ∗ ((sp0 - 324#64) ↦₃₂ k.preKeyId) ∗
            ((sp0 - 320#64) ↦₆₄ sf2.readReg64 .x0) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 296#64) ↦₃₂ w296) ∗
            ((sp0 - 280#64) ↦₆₄ x.kyA) ∗ A.live (sf2.readReg64 .x0) k.ciphertext.length 1 ∗ A.pool ∗
            stackAt sf2.sp allocHookStack ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
          h_memcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [arm64_norm]; rfl)
          (fun R' hm => by simp only [framelessMemcpySpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢; exact satisfies_of_sep_focus hm (by sep_focus))
          (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
        intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
        simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
        simp only [framelessMemcpySpec, sepConj_assoc]; refine SepWPp.pure_elim fun htr3 => ?_
        simp only [wp_norm, arm64_norm, htr2] at htr3; apply SepWPp.of_sepWP_ret; wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
        · simp only [State.spAligned, wp_norm, arm64_norm, *]
        · refine Entails.sepExists_right (sf2.readReg64 .x0) (Entails.sepExists_right x.bkA (Entails.pure_right (fun _ => hoom) ?_))
          rw [optKyberAt_some_eq' A x.kyA x.kyPtr k hky_ne hct_lt,
              optKyberCopyBuf_some_eq' A (sf2.readReg64 .x0) k hoom hct_lt,
              stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
          simp only [hct_ne_nil, ↓reduceIte, hsp2, arm64_norm]; exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_pk_serialize_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (sp0 kyberCap : BitVec 64) (ver32 pkId32 : BitVec 32) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = x.bkA) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 252#64) s
      ((x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x1 = 33#64 ∧
         sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x20 = x.bkA ∧ sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧
         sm.readReg64 .x22 = x.ikA ∧ sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = ver32.zeroExtend 64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          boxU8Buf A (sm.readReg64 .x28) x.baseKey.serialize ∗ boxU8Buf A (sm.readReg64 .x0) x.ik.serialize ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hpk := preKeyMsg_publicKeySerialize_placed_ok (A := A) hshim halloc hpanic
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx6 hx19 hx21 hx22 hx23 hx25 hx26 hx29
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_205).base); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
  intro hcl0
  refine SepWPp.call (x := ⟨x.bkA, x.baseKey⟩)
    (F := (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗ memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [withLsCl, publicKeySerializeSpec, allocFailedIn, State.trace_setPC,
        State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)] at hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [publicKeySerializeSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  dsimp only [withLsCl]; simp only [publicKeySerializeSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl1 => ?_
  refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx1_1 htr1
  apply SepWPp.of_sepWP_lscl hcl1 (mid := (blkPl_205).base); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
  intro hcl1'
  refine SepWPp.call (x := ⟨x.ikA, x.ik.publicKey⟩)
    (F := (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗ boxU8Buf A (sf1.readReg64 .x0) x.baseKey.serialize ∗
          memRegion (sp0 - 368#64 - 7824#64) 3696)
    hpk (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [withLsCl, publicKeySerializeSpec, htr1, allocFailedIn, State.trace_setPC,
        State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    dsimp only [withLsCl]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1', ?_⟩
    simp only [publicKeySerializeSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  dsimp only [withLsCl]; simp only [publicKeySerializeSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun _hcl2 => ?_
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
  apply SepWPp.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [State.spAligned, wp_norm, arm64_norm, *], ?_⟩
  rw [stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp0 - 368#64)]
  simp only [IdentityKey.serialize, hsp1, h28_2, arm64_norm]; exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_msg_clone_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (sp0 kyberCap bkSerPtr ikSerPtr w360 w344 w312 : BitVec 64)
    (w332 w328 ver32 pkId32 : BitVec 32) (s : State)
    (hpc : s.pc = (blkPl_41).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx20 : s.readReg64 .x20 = x.bkA)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ikA)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = ver32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 428#64) s
      (signalMessageAt A x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₃₂ w328) ∗ ((sp0 - 312#64) ↦₆₄ w312) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = ikSerPtr ∧
         sm.readReg64 .x8 = 1#64 ∧ sm.readReg64 .x19 = kyberCap ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s ∧ 9 ≤ x.msg.serialized.length ∧
         x.msg.serialized.length < 2 ^ 40 ∧ sm.readReg64 .x26 ≠ 0#64) ∧
        (Pm ⊢ signalMessageAt A x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₆₄ 33#64) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
          ((sp0 - 312#64) ↦₆₄ x.bkA) ∗ ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          boxU8Buf A (sm.readReg64 .x26) x.msg.serialized ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29
  conv => arg 4; rw [signalMessageAt_expose_ser A x.msgG x.msgA x.msg]
  simp only [sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt63⟩ => SepWPp.pure_elim fun hser_wf => ?_
  simp only [← sepConj_assoc]
  have hser9 : 9 ≤ x.msg.serialized.length := by have := hser_wf.1; change 8 + 1 ≤ x.msg.serialized.length at this; omega
  have hser_lt40 : x.msg.serialized.length < 2 ^ 40 := hser_wf.2.1
  have hser_pos : 0 < x.msg.serialized.length := by omega
  have hser_ne_nil : x.msg.serialized ≠ [] := List.ne_nil_of_length_pos hser_pos
  have hser_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h; have ht := congrArg BitVec.toNat h; rw [hser_toNat, BitVec.toNat_zero] at ht; omega
  have hser_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false := beq_eq_false_iff_ne.mpr hser0
  have hser_msb : (BitVec.ofNat 64 x.msg.serialized.length).getLsbD 63 = false := getLsbD_63_ofNat_lt hser_lt63
  simp only [hser_ne_nil, ↓reduceIte]
  have h_shim := preKeyMsg_shim_placed_ok hshim
  have h_alloc := preKeyMsg_alloc_placed_ok halloc
  have h_memcpy := preKeyMsg_memcpy_placed_ok hmemcpy
  apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := ()) (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
      signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
      ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
    h_shim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [arm64_norm]; rfl)
    (fun R' hm => by simp only [noAllocShimSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢; exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [noAllocShimSpec]; refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1
  apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (x.msg.serialized.length, 1)) (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
      ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
      (A.live x.msgG.serPtr x.msg.serialized.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized)) ∗
      signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
      ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
      ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_alloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)] at hm
      simp only [rustAllocSpec, LayoutOk, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact ⟨⟨⟨0, rfl⟩, by omega⟩, satisfies_of_sep_focus hm (by sep_focus)⟩)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  by_cases hoom : sf2.readReg64 .x0 = 0#64
  · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_; simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
    apply SepWPp.of_sepWP (mid := (blkPl_41).base + 268#64); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact preKeyMsg_oom_at_10c_placed hpanic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    apply SepWPp.of_sepWP (mid := lsρ "memcpy"); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.msgG.serPtr, x.msg.serialized⟩) (F := ((x.msgA + 0x28#64) ↦₆₄ x.msgG.serPtr) ∗
        ((x.msgA + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗ A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
        signalMessageRestBodyAt A x.msgG x.msgA x.msg ∗ ((sp0 - 360#64) ↦₆₄ x.ikA) ∗ ((sp0 - 344#64) ↦₆₄ 33#64) ∗
        ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
        ((sp0 - 288#64) ↦₆₄ x.msgA) ∗ A.live (sf2.readReg64 .x0) x.msg.serialized.length 1 ∗ A.pool ∗
        stackAt sf2.sp allocHookStack ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
      h_memcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [arm64_norm]; rfl)
      (fun R' hm => by simp only [framelessMemcpySpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢; exact satisfies_of_sep_focus hm (by sep_focus))
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [framelessMemcpySpec, sepConj_assoc]; refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]; exact ⟨hser_lt40, hoom⟩
    · rw [signalMessageAt_expose_ser A x.msgG x.msgA x.msg, stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64)]
      have hp_msg1 : (x.msgG.serPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63) = True := eq_true ⟨hser_ne, hser_lt63⟩
      have hp_msg2 : (macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 ∧
          x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
          (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)) = True := eq_true hser_wf
      rw [hp_msg1, hp_msg2, pure_true, emp_sepConj, emp_sepConj]
      simp only [wp_norm, arm64_norm, hsp2, hser_ne_nil, ↓reduceIte]
      unfold boxU8Buf
      have hp_copy : (sf2.readReg64 (Reg.gpr 0#5) ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63) = True :=
        eq_true ⟨hoom, hser_lt63⟩
      rw [hp_copy, pure_true, emp_sepConj]; simp only [hser_ne_nil, ↓reduceIte, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
