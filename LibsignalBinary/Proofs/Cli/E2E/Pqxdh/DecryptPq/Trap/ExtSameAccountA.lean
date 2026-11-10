/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0B
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed `SameAccount` Callee Wrappers & `S0` Step 5 (`DistinctSid`)

Discharges `IsSameAccountDistinctOk_ext` (`IsSameAccountDistinctOkExt32`) and proves
`s0_remote_some_wp_pq_distinct_ext` and `s0_step5_some_reaches_pq_distinct_ext` (`+0x180 → +0x1d8`,
`remIk = some` under `DistinctSid`) on `tripleRatchetProgAtExt`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (TryDecryptGhost tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Getters (isSameAccountName)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
  (bytes9_64_8_eq_8_64 remoteGroupD s0_step5_some_extract s0_step5_some_recombine
   sepWP_to_reaches_pc stackAt_tryDecryptSubStack_sub)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)
open CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq
  (IsSameAccountDistinctOk_ext isSameAccountDistinctStackExt isSameAccountEqDistinct_ok_ext32
   isSameAccountEqDistinct_ok_of_pkEq)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSameAccountA

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `IsSameAccountDistinctOk_ext` Contract-Backed Constructors -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountEqDistinct_ok_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hbb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    IsSameAccountDistinctOk_ext b A ext :=
  isSameAccountEqDistinct_ok_ext32 b A ext hbb

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinct_ok_of_pkEq_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hEq : CryptoVerification.LibsignalTripleRatchet.Getters.PublicKeyEqOkExt32 b ext) :
    IsSameAccountDistinctOk_ext b A ext :=
  isSameAccountEqDistinct_ok_of_pkEq b A ext hEq

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinct_ok_on
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (b : BitVec 64)
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext)
    (hAg : AgreeOnCliHooks ext ext') :
    IsSameAccountDistinctOk_ext b A ext' :=
  isSameAccountEqDistinct_ok_ext32 b A ext' (hAg.hookSat (by decide) hOk.blackBox)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinct_ok_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (b : BitVec 64)
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    IsSameAccountDistinctOk_ext b A (CryptoVerification.SignalSession.cliExternsWith ext) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinct_ok_on b hOk
    (AgreeOnCliHooks.cliExternsWith ext)

/-! ## 2. `S0` Step-5 `remIk = some` Symbolic Execution (`DistinctSid`, `tripleRatchetProgAtExt`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_remote_some_wp_pq_distinct_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : IsSameAccountDistinctOk_ext b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32)
    (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 :
      BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3
          b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨ DistinctSid uuidTryParse x.loc.name.bytes
      x.rem.name.bytes) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    SepWP (tripleRatchetProgAtExt b ext) (entry + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s.sp + 400#64) ↦₆₄ u400) ∗
       ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗
       ((s.sp + 360#64) ↦₈ b31) ∗
       ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗
       ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s.sp isSameAccountDistinctStackExt)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          ((s.sp + 48#64) ↦₆₄ x.remA) ∗
          ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt s.sp isSameAccountDistinctStackExt)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hsame_fn := (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
  have hsame_addr : (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.fnAddr_tryDecrypt_rel64_ext
      hsame_fn (by decide)
  unfold IsSameAccountDistinctOk_ext
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32 at hsame
  rw [hsame_addr] at hsame
  dec_fetches_cli b ext hfn 0x180 92
  clear hfn hsame_fn hsame_addr
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
  examples_hide_fetches
  unfold remoteGroupD
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by
    clear * -; unfold pack64; bv_slice
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗
       (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗
       (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  wp_steps
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by
    clear * -; unfold pack64; bv_slice
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>>
        8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by
    clear * -; unfold pack64; bv_slice
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗
       (s.sp + 60#64) ↦₈ b4 ∗
       (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗
       (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗
       (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc,
        BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb6, hb15_22, hrem56]
  wp_call hsame ⟨s.sp + 1280#64, x.st.localIdentity, x.locA, x.loc,
    s.sp + 56#64, remIk, x.remA, x.rem⟩
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. `S0` Step-5 `reaches_pc` Wrapper (`DistinctSid`, `tryDecryptSubStack`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step5_some_reaches_pq_distinct_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : IsSameAccountDistinctOk_ext b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (w0 : BitVec 32)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64)
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
    (hdiff : x.st.localIdentity ≠ remIk ∨ DistinctSid uuidTryParse x.loc.name.bytes
      x.rem.name.bytes)
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
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      F) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt b ext) (entry + 472#64) s4
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
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗
          F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStackExt (by decide)] at hm
  have hm_sub : s4.mem ⊨
      (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       ((sp + 352#64) ↦₆₄ w3) ∗
       ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗
       ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗
       memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt sp isSameAccountDistinctStackExt ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStackExt) ∗
       F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
    db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ := s0_step5_some_extract hm_sub
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
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s4.sp isSameAccountDistinctStackExt) ∗
      (memRegion (sp + 409#64) 25 ∗
       memRegion (sp + 88#64) 264 ∗
       memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗
       memRegion (sp + 982#64) 298 ∗
       memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStackExt) ∗
       F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by
    rw [hx29, h_sp]; bv_omega
  have hwp :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_remote_some_wp_pq_distinct_ext
      hsame x remIk s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18
      db19 db20 db21 db22 dw3 db31 h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29'
      hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hsp5.trans h_sp, halign5, ⟨htr5.1.trans htr.1, htr5.2.trans htr.2⟩, hx1_5,
    hx19_5.trans hx19, by rw [hx20_5, h_sp], hx21_5.trans hx21, hx22_5.trans hx22,
    hx23_5.trans hx23,
    by change (s5.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_5]; exact hx24,
    hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hPf) hm_s5
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
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       (stackAt sp isSameAccountDistinctStackExt ∗
        memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStackExt)) ∗
       F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStackExt (by decide)] at hm3
  have hm4 := Arm64.Satisfies.mono
    (sepConj_mono_left (s0_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
        (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSameAccountA
