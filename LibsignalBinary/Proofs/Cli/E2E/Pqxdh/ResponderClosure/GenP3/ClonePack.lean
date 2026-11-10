/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Stmts
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Segment 5: Pack & Version Dispatch

Proves `clonePack_ok : ClonePackStmt` (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4 → genP3Post`),
storing all cloned `SessionState` fields into `sp + 0xa90..0xbe8` and branching on
`st.version = msgVer`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subsPState32 (x y : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 x y) = (x == y) := by
  unfold subsPState32
  exact conditionHolds_eq_subs32 x y

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subsPState32 (x y : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 x y) = (x != y) := by
  unfold subsPState32
  exact conditionHolds_ne_subs32 x y

/-- Spill + call-arg stack cells accessed during `+0x1bac .. +0x1cd0`. -/
def packSrcSlotsAt (sp : BitVec 64) (recG : SessionGhost)
    (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64) (msgVer : BitVec 32) : SepProp :=
  ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
  ((sp + 0x10#64) ↦₆₄ w.d10) ∗
  ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
  ((sp + 0x24#64) ↦₃₂ w.w24) ∗
  ((sp + 0x28#64) ↦₃₂ w.w28) ∗
  ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
  ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
  ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
  ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
  ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
  ((sp + 0x48#64) ↦₆₄ w.c0) ∗
  ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
  ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
  ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
  ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
  ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
  ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
  ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
  ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
  ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
  ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/- Version-match step (`+0x1bac → +0x1cd4`, `st.version = msgVer`). -/
set_option maxHeartbeats 800000 in
theorem pack_eq_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version = msgVer)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd4#64)
      s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only []
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1bac 0x1cd0
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : msgVer = 2#32 := by
      rw [← hver]; simp only [SessionState.version, hsv0, ↓reduceIte]; rfl
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = false := bne_eq_false_iff_eq.mpr hm.symm
    have hne2 : (msgVer != 2#32) = false := bne_eq_false_iff_eq.mpr hm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0']; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion = msgVer := by
      have hv : st.version = st.sessionVersion := by
        simp only [SessionState.version, hsv0, ↓reduceIte]
      exact hv.symm.trans hver
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = false := bne_eq_false_iff_eq.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = false := bne_eq_false_iff_eq.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hm]; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/- Version-mismatch step (`+0x1bac → +0x1e04`, `st.version ≠ msgVer`). -/
set_option maxHeartbeats 800000 in
theorem pack_ne_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version ≠ msgVer)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e04#64)
      s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x9 = msgVer.setWidth 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only []
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1bac 0x1cb4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : 2#32 ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != 2#32) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0']; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

private theorem sepWPp_done {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

/-- Untouched spatial frame threaded across `pack_eq_wp` / `pack_ne_wp`. -/
def packRestFrame (A : RustAlloc) (img : Obj.Image) (sp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
  A.pool ∗
  stackAt sp chainCloneStack ∗
  memRegion (sp + 0x3e0#64) 104 ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0x98#64) ↦₆₄ 32#64) ∗
  protocolAddressAt A rem remAddrPtr ∗
  protocolAddressAt A loc locAddrPtr ∗
  signalMessageAt A msgG whisperMsgPtr msg ∗
  memRegion (sp + 0x270#64) 48 ∗
  CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗
  logOff img ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
  vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
  vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
  vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
  optSenderChainHeap A w.sender' st.senderChain ∗
  vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
    (w.chains'.zip st.receiverChains) ∗
  OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
  OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
  vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
  vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState

/- Reassembles the post-step destination cells, spill slots, and `packRestFrame` into `genP3PostSpatial`. -/
set_option maxHeartbeats 400000 in
theorem packed_entails_genP3PostSpatial (A : RustAlloc) (img : Obj.Image)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness) (w20 : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (h_loc_deser : PublicKey.deserialize recG.localIk.bytes = .ok st.localIdentity.publicKey)
    (h_rem_deser : match st.remoteIdentity with
      | none => recG.remoteIk.bytes = []
      | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : recG.pending.isSome = st.pendingPreKey)
    (h_reg_len : recG.regIds.length = 8)
    (h_loc_len : recG.localIk.bytes.length = 33)
    (h_rem_len : st.remoteIdentity.isSome → recG.remoteIk.bytes.length = 33)
    (hreg_eq : recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1)
    (hchains_len : w.chains'.length = st.receiverChains.length)
    (hsc_inl : OptSenderChainInline w.sender' st.senderChain
      (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)) :
    ((packSrcSlotsAt sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsWrittenAt sp recG st w w20) ∗
      packRestFrame A img sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
        recG st w rem loc msgG msg) ⊢
      genP3PostSpatial A img sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg := by
  have hst := packDstSlotsWrittenAt_entails_sessionStateAt A sp recG st w w20
    h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl
  have hspill := spillSlots_entails_genP3SpillAll sp recG st w
  have hstk : memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      stackAt sp chainCloneStack = stackAt sp rootStack :=
    (P3P4.stackAt_root_eq_chainClone sp).symm
  unfold packSrcSlotsAt packRestFrame genP3PostSpatial
  refine Entails.trans
    (Q := (packDstSlotsWrittenAt sp recG st w w20 ∗
            vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
            vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
              (w.chains'.zip st.receiverChains) ∗
            vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
            optSenderChainHeap A w.sender' st.senderChain ∗
            OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
            OptKybClone A recG.kyber w.kybCap' w.kybPtr') ∗
          (((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0x10#64) ↦₆₄ w.d10) ∗
            ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0x24#64) ↦₃₂ w.w24) ∗
            ((sp + 0x28#64) ↦₃₂ w.w28) ∗ ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
            ((sp + 0x30#64) ↦₃₂ w.regW0) ∗ ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
            ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
            ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
            ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
            ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
            ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
            ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
            ((sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
            genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5) ∗
          (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
            stackAt sp chainCloneStack) ∗
          (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
            protocolAddressAt A rem remAddrPtr ∗
            protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            memRegion (sp + 0x270#64) 48 ∗
            CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗
            logOff img ∗
            A.pool ∗
            memRegion (sp + 0x3e0#64) 104 ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
            ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
            ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
            ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
            ((sp + 0x3ac#64) ↦₈ 3#8)))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hstk]
  exact Entails.trans (sepConj_mono hst (sepConj_mono_left hspill)) (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

private theorem sepWPp_weaken_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (himp : ∀ s1 P_f, Q s1 P_f → Q' s1 P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hne
  obtain ⟨sf, hsteps, hpost⟩ := h R hm hne
  refine ⟨sf, hsteps, ?_⟩
  rcases hpost with ⟨hpc, hrun, P_f, hm', hQ⟩ | hp
  · exact Or.inl ⟨hpc, hrun, P_f, hm', himp sf P_f hQ⟩
  · exact Or.inr hp

/-- `calleeSavedVRegs`-preserving strengthening of `ClonePackStmt4K`. -/
def ClonePackVRegsStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

/-- `calleeSavedVRegs`-preserving strengthening of `ClonePackStmt`. -/
def ClonePackVRegsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

/- Segment 5 with `calleeSavedVRegs` under `AllocContractsMem4K` (`+0x1bac → +0x1cd4 / +0x1e04`). -/
set_option maxHeartbeats 800000 in
theorem clonePack_vregs_4k_ok : ClonePackVRegsStmt4K := by
  intro A img ext _hA _himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg _hrc_len hsp_align _hsp_root hF hsym hpc hrun htr
  dsimp only [genP3J4]
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_elim
    fun ⟨hsp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29,
         hreg_eq, hchains_len, _hsc_rel, hsc_inl⟩ => ?_
  cases hsp
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_pure_sep A (coroPtr + 0xf8#64) recG st)) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim
    fun ⟨h_loc_deser, h_rem_deser, _, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  dsimp only [genP3CallFrame]
  refine SepWPp.weaken_pre
    (P' := memRegion (s.sp + 0xa90#64) 344 ∗
            (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packRestFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
                recG st w rem loc msgG msg))
    (Entails.of_eq (by dsimp only [packSrcSlotsAt, packRestFrame]; ac_rfl)) ?_
  refine SepWPp.weaken_pre (sepConj_mono_left (memRegion_344_entails_packDstSlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dv => ?_
  refine SepWPp.weaken_pre
    (P' := (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packDstSlotsAt s.sp dv) ∗
            packRestFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
              recG st w rem loc msgG msg)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPC, hver, ↓reduceIte]
    have hstep := pack_eq_wp img.base ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep rfl
      fun s1 hpc1 hrun1 hF1 hsym1 hregs => ?_
    rcases hregs with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done hpc1 hrun1 ⟨?_, htr1.trans htr, hF1, hsym1, hvregs1⟩
    simp only [genP3Post, hver, ↓reduceIte, genP3PostEq]
    apply Entails.pure_right
      ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatial A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st w ((s.readReg64 .x20).truncate 32) rem loc msgG msg
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl
  · simp only [cloneExitPC, hver, ↓reduceIte]
    have hstep := pack_ne_wp img.base ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep rfl
      fun s1 hpc1 hrun1 hF1 hsym1 hregs => ?_
    rcases hregs with ⟨hsp1, htr1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done hpc1 hrun1 ⟨?_, htr1.trans htr, hF1, hsym1, hvregs1⟩
    simp only [genP3Post, hver, ↓reduceIte, genP3PostNe]
    apply Entails.pure_right ⟨hsp1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatial A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st w ((s.readReg64 .x20).truncate 32) rem loc msgG msg
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl

/-- Segment 5 under `AllocContractsMem4K` (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4 → genP3Post`). -/
theorem clonePack_4k_ok : ClonePackStmt4K := by
  intro A img ext hA himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root hF hsym hpc hrun htr
  exact sepWPp_weaken_post
    (clonePack_vregs_4k_ok img ext hA himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root hF hsym
      hpc hrun htr)
    fun _ _ ⟨hent, htr1, hF1, hsym1, _⟩ => ⟨hent, htr1, hF1, hsym1⟩

/-- Segment 5 with `calleeSavedVRegs` (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4 → genP3Post`). -/
theorem clonePack_vregs_ok : ClonePackVRegsStmt :=
  fun img ext hA => clonePack_vregs_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

/-- Segment 5 (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4 → genP3Post`). -/
theorem clonePack_ok : ClonePackStmt :=
  fun img ext hA => clonePack_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
