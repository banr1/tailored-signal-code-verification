/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Phase 3 & 4 Composition of `spqr::send::<signal_session_ratchet::Coins>` (`+3196 -> s0.x30`)

Composes `<Message>::serialize`, `<States>::into_pb`, `PqRatchetState` encoding, drop cleanup,
and the shared return epilogue (`+3196 -> s0.x30`) on the CLI image.
-/

@[expose] public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification

open CryptoVerification.CodeLayout

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.Top.StateSize

open CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_320a4 {A : RustAlloc} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt img.base A ext)
    (s0 sm : State) (sp ret v_20 x21 x23 x25 x27 w0 w16 : BitVec 64)
    (stBytes msgBytes : Bytes) (salt : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (pq' : PqRatchetState) (Rest Fr : SepProp)
    (post : State → SepProp → Prop)
    (hmsg_len : msgBytes.length < 2 ^ 32) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6216#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx23 : sm.readReg64 .x23 = x23) (hx25 : sm.readReg64 .x25 = x25)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 4192#64)
    (hflag : x21 = LibsignalTripleRatchetRepr.noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !pq'.chain.isSome)
    (hpost : ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      (Pf ⊢ spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
        A.pool ∗ stackAt s0.sp spqrSendStack ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest) →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm
      (memRegion ret 72 ∗ vecU8 A (sp + 1424#64) stBytes ∗ vecU8 A (sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A sp salt ∗ ((sp + 32#64) ↦₆₄ v_20) ∗
        (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ w16) ∗
        memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 ∗
        pqRatchetStatePBPinnedAt A g (sp + 4704#64) pq' ∗
        memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hfin := CryptoVerification.Cli.SpqrV1.Top.Send.step_send_finish_320a4' hb hdealloc sm ret v_20 x21 x23 x25 x27
    stBytes msgBytes salt g pq'
    ((sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ w16) ∗
      memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 5056#64) 576 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ Rest)
    hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 (by rw [hsp]; exact hx28) hflag hx25_ch hsp_align
  rw [hsp] at hfin
  refine sepWPp_of_early_return
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq hfin fun s1 Q1 hpc1 _ ⟨hrun1, htr1, hsp1, hx23_1, hvregs1, hQ1⟩ => ?_))
    hpost
  have hsp1' : s1.sp = sp := hsp1
  have hjoin : Q1 ⊢
      memRegion s1.sp 0x60 ∗ chainOrigSlotAt s1.sp x23 ∗ memRegion (s1.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      stackAt s1.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s1.sp s0 ∗
      (spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest) := by
    rw [hsp1', memRegion_b0_1f20_eq_finish sp]
    refine Entails.trans hQ1 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      ((sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 8 ∗ ((sp + 16#64) ↦₆₄ w16) ∗
        memRegion (sp + 24#64) 24 ∗ memRegion (sp + 0x30#64) 48) ∗
      (chainOrigSlotAt sp x23 ∗
        (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1424#64) 24 ∗
         memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
         memRegion (sp + 0x950#64) 928 ∗
         memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 4192#64) 48 ∗
         memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 4704#64) 352 ∗
         memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
         memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
         stackRestCF0_1F20 sp) ∗
        stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
         CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest)) by ac_rfl)) ?_
    exact sepConj_mono_left (memRegion_0_60_join sp w0 w16)
  refine SepWP.weaken_pre hjoin
    (SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_epilogue_from_31a54 s0 s1 x23
      (spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest)
      hpc1 hrun1 (hsp1'.trans hsp_eq) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hcsf, hQf⟩
  exact ⟨Entails.trans hQf (Entails.of_eq (by ac_rfl)), hspf, hcsf, (htrf.trans htr1).trans htr⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_317fc {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hmser : MessageSerializeOkX spqrPolyApi img A ext)
    (hinto : StatesIntoPbOkX img A F ext)
    (s0 s : State) (sp ret x23 : BitVec 64)
    (idx : BitVec 32) (msgKey : Bytes) (hmk_cases : msgKey = [] ∨ msgKey.length = 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4000#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hsp : s.sp = sp) (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 msgKey.length)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg32 .x24 = idx)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32)
    (hpost : ∀ (salt : CryptoGames.HKDF.Salt),
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret
          (some (PqRatchetState.encodeRaw { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) },
                 salt, msg.serialize idx)) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) st1 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsp_align : sp &&& 15#64 = 0#64 := by
    rw [hsp_eq]; exact beq_iff_eq.mp (ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide))
  obtain ⟨salt, hsalt_eq, hsalt_ent⟩ := msgKey_to_optMsgKeySlotsAt A sp msgKey hmk_cases
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion sp 8 ∗ memRegion (sp + 16#64) 24) ∗
    (optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
      memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
      messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
      spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
  rw [memRegion_sp_0_16_24_words sp]
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_20_old
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp18
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp10
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v0
  simp_rw [← encodeToVecOnPanic_congr htr]
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_bridge2_317fc hA himg hmser hinto rfl hinv sp v_20_old v0 v_sp10 v_sp18 idx vn chainPb st1 msg
    hlen hsp_align
    (Frame := (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest)
    hpc hrun hsp rfl hx24 hx26 hx28 ⟨fun _ h => h, rfl, rfl⟩
    (by rw [memRegion_590_224_eq_88_136 sp, memRegion_1260_928_eq_88_840 sp]; ac_rfl) ?_
  intro sm g w0_new pq' hpc_m hrun_m hsp_m htr_m hx19_m hx21_m hx23_m _ hx25_ch hx27_m hx28_m hinv_m _
  simp_rw [encodeToVecOnPanic_congr htr]
  have hdrop :
      ((Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64) pq' ∗
        vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
        vecU8 A (sp + 4080#64) (msg.serialize idx) ∗
        ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
        (sp ↦₆₄ w0_new) ∗ ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain pq'.chain) ∗
        ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
        memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        ((img.base + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        statesIntoPbJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗
       ((∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ Rest)) =
      (((img.base + bv% (ls_xref% (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 56) (ls_off% "<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len [local#3]" + 60))) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((img.base + bv% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344) + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        statesIntoPbJumpTableAt img.base) ∗
      ((((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey)) ∗
       (memRegion ret 72 ∗
        vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
        vecU8 A (sp + 4080#64) (msg.serialize idx) ∗
        ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
        (sp ↦₆₄ w0_new) ∗ ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain pq'.chain) ∗
        memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 ∗
        Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64) pq' ∗
        memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)) := by
    rw [hx22, memRegion_1060_80_eq_48_32 sp]; ac_rfl
  rw [hdrop]
  apply sepWPp_drop_left
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left hsalt_ent) ?_)
    (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_320a4 (φ_panic := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      img ext hb hA.dealloc s0 sm sp ret (s.readReg64 .x20)
      (s.readReg64 .x21) x23 (sm.readReg64 .x25) (s.readReg64 .x27) w0_new
      (Prost.EncodeToVec.optChainCap g.chain chainPb)
      (PqRatchetState.encodeRaw { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) })
      (msg.serialize idx) salt g
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } Rest Fr post
      (message_serialize_len_lt_2_32 msg idx) hsp0_align hsp_eq hpc_m hrun_m hsp_m (htr_m.trans htr)
      (hx19_m.trans hx19) hx21_m (hx23_m.trans hx23) rfl hx27_m hx28_m hflag hx25_ch (hpost salt hsalt_eq)
      (hinv_m.2.2.trans hvregs))
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_chunkedStatesLocal1JumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" + 44) (ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#3]" + 48))) (n := 10) (bs := chunkedStatesLocal1JumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.sepWPp_intro_chunkedStatesLocal1JumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s (CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R0 hm hL
  have hm' : s.mem ⊨ (CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact CryptoVerification.Cli.SpqrV1.Top.Send.rodata_chunkedStatesLocal1JumpTable himg hF hm
  exact h R0 hm' hL

/-! ## Phase 3 (`+3196` -> return) and Pure Model Reduction Lemmas -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_314d8_ext {A : RustAlloc} {F : ShaCompress} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name) (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F img.base))
    (hfrom_pb : ChainFromPbOkX img A ext)
    (hfrom_vn : ChainFromVersionNegotiationOkExt img (spqrHkdfWith F) A ext)
    (hadd_epoch : ChainAddEpochOkExt img (spqrHkdfWith F) A ext)
    (hsend_key : ChainSendKeyOkExt img (spqrHkdfWith F) A ext)
    (hinto_pb : ChainIntoPbOkX img A ext)
    (hser_call : MessageSerializeOkX spqrPolyApi img A ext)
    (hstates_into_pb : StatesIntoPbOkX img A F ext)
    (s0 sm : State) (sp ret x21 x27 x23 : BitVec 64)
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54)
    (hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      Prost.EncodeToVec.pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63)
    (hinv : ImgCallInv img sm)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3196#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx22 : sm.readReg64 .x22 = sOut.msg.epoch) (hx23 : sm.readReg64 .x23 = x23)
    (hx25 : sm.readReg64 .x25 = sp + 0x550#64) (hx26 : sm.readReg64 .x26 = sp + 0x1260#64)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 0x1060#64)
    (hx23_none : x23 = LibsignalTripleRatchetRepr.noneCap ↔ pq.chain = none)
    (hpstate : sm.pstate = addsPState64 x23 1#64)
    (hφ : ∀ sf : State, (((sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_panic sf)
    (herr_post : ∀ err : LibsignalSpqrV1.Error,
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          statesIntoPbJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_post : ∀ (idx : BitVec 32) (msgKey : Bytes) (chainPb : Option ChainPB) (salt : CryptoGames.HKDF.Salt),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb) →
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := pq.versionNegotiation
                      chain := chainPb
                      inner := some (.v1 sOut.state.into_pb) },
                   salt, sOut.msg.serialize idx)) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          statesIntoPbJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm
      (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_dealloc_ok hA
  apply CryptoVerification.Cli.SpqrV1.Top.Send.sepWPp_intro_chunkedStatesLocal1JumpTable himg hinv.1
  let Frame314d8 : SepProp :=
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
    memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
    memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
    memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
    messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
    spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
  have hres := CryptoVerification.Cli.SpqrV1.Top.Send.step_chain_resolve_314d8_to_7fc_ext img (spqrHkdfWith F) hb hA.dealloc
    hdrop_slice hdrop_states hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb
    s0 sm ret x21 x27 x23 pq.chain hchain_raw pq.versionNegotiation sOut.key sOut.msg.epoch
    sOut.state Frame314d8 Fr φ_panic hinv hpc hrun htr hx23_none hpstate
    hx19 hx21 hx22 hx23 (by rw [hsp]; exact hx25) (by rw [hsp]; exact hx26)
    hx27 (by rw [hsp]; exact hx28) hsp_align hφ
  rw [hsp] at hres
  have hpre_eq :
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
      (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest) =
      ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame314d8 := by
    dsimp only [Frame314d8]; ac_rfl
  rw [hpre_eq]
  refine sepWPp_bind hres fun s1 P1 hpc1 hrun1 hpost1 => ?_
  generalize hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = res at hpc1 hpost1
  rcases res with (err | p) | ⟨idx, msgKey, chainPb⟩
  · rcases hpost1 with ⟨_, htr1, hsp1, hinv1, hx23_1, hvregs1, hQ1⟩
    refine SepWPp.weaken_pre hQ1 ?_
    have hjoin_err :
        spqrSendResultAt A ret none ∗ memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗
        memRegion (sp + 0x28#64) 8 ∗ memRegion (sp + 0x8#64) 8 ∗
        memRegion (sp + 0x190#64) 928 ∗ CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) ⊢
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        (memRegion sp 0x30 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
         chainOrigSlotAt sp x23 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) ∗
         stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
         (spqrSendResultAt A ret none ∗ A.pool ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          statesIntoPbJumpTableAt img.base ∗ Rest)) := by
      dsimp only [Frame314d8]
      have hmsg := messageAt_entails_memRegion_48 (sp + 0x1d70#64) sOut.msg
      have h0_30 :
          memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8 =
          memRegion sp 0x30 := by
        rw [memRegion_0_30_eq sp,
            ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 16) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
            memRegion_32_16_eq_8_8 sp]
        ac_rfl
      have hff0 : (sp + 0xff0#64 : BitVec 64) = sp + 4080#64 := rfl
      rw [hff0]
      refine Entails.trans (Entails.of_eq (show _ =
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
        (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8) ∗
        (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x590#64) 88 ∗
         memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp) ∗
        memRegion (sp + 0x950#64) 928 ∗
        (memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
         memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
         stackRestCF0_1F20 sp) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hmsg) ?_
      rw [h0_30, ← memRegion_b0_950_eq_rest sp]
      refine Entails.trans (Entails.of_eq (show _ =
        memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗ memRegion (sp + 0x950#64) 928 ∗
        (memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
         memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
         memRegion (sp + 0x1d70#64) 48 ∗ stackRestCF0_1F20 sp) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
      have hb0_1f20 :
          memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
          memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) := by
        rw [memRegion_b0_1f20_eq sp]
      rw [← memRegion_cf0_1f20_eq_rest sp]
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
         memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
      rw [hb0_1f20]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hjoin_err ?_
    apply sepWPp_drop_left (Drop := CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base)
    have hep := CryptoVerification.Cli.SpqrV1.Top.Send.step_epilogue_from_31a3c hA.dealloc s0 s1 pq.versionNegotiation x23
      (spqrSendResultAt A ret none ∗
       CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
       statesIntoPbJumpTableAt img.base ∗ Rest)
      hpc1 hrun1 (hsp1.trans hsp_eq) hx23_1 hsp0_align hvregs1
    rw [hsp1] at hep
    refine sepWPp_of_early_return
      (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hep ?_))
      (herr_post err hch)
    intro sf Pf _ _ ⟨_, htr_f, hsp_f, hcs_f, hPf⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f.trans htr1⟩
  · exact False.elim hpost1
  · rcases hpost1 with ⟨_, htr1, hsp1, hinv1, hx19_1, hx22_1, hx23_1, hx24_1, hx26_1, hx28_1, hflag_1, hvregs1, hQ1⟩
    refine SepWPp.weaken_pre hQ1 ?_
    have hdrop_ro :
        optChainPBRegSlotAt A (sp + 0xd90#64) (s1.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗ CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) =
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base ∗
        (optChainPBRegSlotAt A (sp + 0xd90#64) (s1.readReg64 .x25) chainPb ∗
          (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
            ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
          memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
          memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (sp + 0x190#64) sOut.state ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
          memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
          memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
          memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
          spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)) := by
      dsimp only [Frame314d8]; ac_rfl
    rw [hdrop_ro]
    apply sepWPp_drop_left (Drop := CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTableAt img.base)
    have hmk_cases := sendChainPhase_msgKey_cases F pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    have hch_le := sendChainPhase_raw_le (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    refine sepWPp_weaken_panic (φ1 := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun sf ha => hφ sf (Or.inr ha)) ?_
    exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_317fc img ext himg hA hser_call hstates_into_pb s0 s1 sp ret x23
      idx msgKey hmk_cases pq.versionNegotiation chainPb sOut.state sOut.msg
      (hpq'_len chainPb hch_le)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest) Fr post
      hsp0_align hsp_eq hpc1 hrun1 htr1 hsp1 hinv1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 hflag_1
      (fun salt hsalt sf Pf hpc_f hrun_f hPf hsp_f hcs_f htr_f =>
        hok_post idx msgKey chainPb salt hch hsalt sf Pf hpc_f hrun_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl))) hsp_f hcs_f htr_f)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_314d8 {A : RustAlloc} {F : ShaCompress} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Name) (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1Spec A F img.base))
    (hfrom_pb : ChainFromPbOkX img A ext)
    (hfrom_vn : ChainFromVersionNegotiationOkX img (spqrHkdfWith F) A ext)
    (hadd_epoch : ChainAddEpochOkX img (spqrHkdfWith F) A ext)
    (hsend_key : ChainSendKeyOkX img (spqrHkdfWith F) A ext)
    (hinto_pb : ChainIntoPbOkX img A ext)
    (hser_call : MessageSerializeOkX spqrPolyApi img A ext)
    (hstates_into_pb : StatesIntoPbOkX img A F ext)
    (s0 sm : State) (sp ret x21 x27 x23 : BitVec 64)
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54)
    (hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      Prost.EncodeToVec.pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63)
    (hinv : ImgCallInv img sm)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3196#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx22 : sm.readReg64 .x22 = sOut.msg.epoch) (hx23 : sm.readReg64 .x23 = x23)
    (hx25 : sm.readReg64 .x25 = sp + 0x550#64) (hx26 : sm.readReg64 .x26 = sp + 0x1260#64)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 0x1060#64)
    (hx23_none : x23 = LibsignalTripleRatchetRepr.noneCap ↔ pq.chain = none)
    (hpstate : sm.pstate = addsPState64 x23 1#64)
    (hφ : ∀ sf : State, (((sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_panic sf)
    (herr_post : ∀ err : LibsignalSpqrV1.Error,
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err) →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret none ∗ A.pool ∗ stackAt s0.sp spqrSendStack ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          statesIntoPbJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_post : ∀ (idx : BitVec 32) (msgKey : Bytes) (chainPb : Option ChainPB) (salt : CryptoGames.HKDF.Salt),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb) →
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := pq.versionNegotiation
                      chain := chainPb
                      inner := some (.v1 sOut.state.into_pb) },
                   salt, sOut.msg.serialize idx)) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
          statesIntoPbJumpTableAt img.base ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm
      (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_send_from_314d8_ext img ext himg hb hA
    hdrop_slice hdrop_states hfrom_pb
    (chainFromVnOkExt_of_okX hfrom_vn)
    (chainAddEpochOkExt_of_okX hadd_epoch)
    (chainSendKeyOkExt_of_okX hsend_key)
    hinto_pb hser_call hstates_into_pb s0 sm sp ret x21 x27 x23 pq sOut Rest Fr post
    hsp0_align hsp_eq hchain_raw hpq'_len hinv hpc hrun hsp htr
    hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx23_none hpstate hφ herr_post hok_post hvregs

end CryptoVerification.SpqrV1.Top.Send

/-! ## Trap-at-rng (`trTrapExterns`) Hook Lifting and `decode_state_ok_x_trap` -/

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.SpqrV1.Top.Send (spqrHooks_tripleRatchetExterns)

/-- `sessionExterns C.F abs` embeds into `trTrapExterns C abs` under `Rust.withPanics`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.sessionExterns_le_trTrap
    (C : Crypto) (abs : String → Option (State → State)) :
    ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (trTrapExterns C abs) n = some f := by
  intro n f h
  have hr : n ≠ rngFillName := by
    rintro rfl
    simp [Rust.withPanics, CryptoVerification.LibsignalSession.sessionExterns,
      rngFillName, Rust.isPanicSymbol] at h
  rw [withPanics_trTrap_eq_kit C 0#64 abs hr]
  exact ConsumeMessageKeyTransfer.sessionExterns_le C 0#64 abs n f h

/-- Transfer a `HookSat` contract away from `rngFillName` from `tripleRatchetExterns` to `trTrapExterns`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit
    {α : Type} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sym : String} {spec : Spec α}
    (hr : sym ≠ rngFillName)
    (h : HookSat (tripleRatchetExterns C ctl abs) sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_eq_tripleRatchetExterns C ctl abs hr).trans hfn, hok⟩

/-- Lift `SpqrHooks C A K abs` to `trTrapExterns C abs`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrHooks_trTrapExterns
    {C : Crypto} {A : RustAlloc} {K : MlKem} {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (trTrapExterns C abs) :=
  let hk := spqrHooks_tripleRatchetExterns (C := C) (ctl := 0#64) hSH
  { hk with
    fromSeed := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.fromSeed
    pk1 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.pk1
    pk2 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.pk2
    encaps1 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.encaps1
    encaps2 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.encaps2
    decaps := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.decaps
    validatePk := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.validatePk
    hmac := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.hmac }

/-- `spqr::decode_state` meets `DecodeStateOkX canonicalV1InnerHeap img A ext` from `Stage2Contracts_trap`
    (no `rng_fill` contract required). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.decode_state_ok_x_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.base_aligned_of_loads himg
  have hAlloc : AllocContracts img.base A ext := hC.toAllocContracts
  have hFrom := hC.decode_error_from
  have hPush := hC.decode_error_push
  have h_off_eq : ∀ {name callee : String} {k : BitVec 64},
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name) + k =
        BitVec.ofNat 64 (libsignalSessionCode.fnOff callee) →
      (tripleRatchetProgAtExt img.base ext).fnAddr name + k =
        (tripleRatchetProgAtExt img.base ext).fnAddr callee := by
    intro name callee k hk
    change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff name)) + k =
      img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff callee)
    rw [BitVec.add_assoc, hk]
  have hVarint : Varint.DecodeVarint2OkExt img.base A ext := by
    refine Varint.decodeVarint2_ok_of_contracts ?_ ?_
    · rw [Varint.decodeVarint2_add_from_eq_fnAddr]; exact hFrom
    · rw [h_off_eq (name := Varint.decodeVarint2Name)
        (callee := "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")
        (by rw [(ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]"),
                (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")]; bv_omega)]
      exact decodeVarintSlow_ok_of_session2 hC.decode_varint_slow
  have hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.skipField3Name)
      (Varint.skipField3Spec A) := by
    refine Varint.skipField3_ok_of_contracts ?_ hVarint
    rw [Varint.skipField3_add_from_eq_fnAddr]; exact hFrom
  have hBC : BytesMerge3Contracts img A ext :=
    { loads := himg
      alloc := hAlloc
      decode_error_from := hFrom
      decode_varint2 := subroutine_ok_inImage_of_subroutine_ok img hVarint
      bytes_from_vec := bytesFromVecOk_ext himg rfl
      reserve7 := CryptoVerification.SpqrV1.Alloc.do_reserve_7_ok_ext hAlloc
      vtable_slot := bytesVtableSlotLoaded
      vtable_drop := fun p v => bytesVtableDropOk_ext p v v.length hAlloc himg rfl }
  have hBytes := hBC.ok_ext
  have hGrowVecU8 := growOneVecU8_ok_ext img.base A ext hAlloc
  have hChainParams : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DecodeState.chainParamsMergeName)
      (DecodeState.chainParamsMergeSpec A) := by
    have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName)
        (CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeSpec A) := by
      refine chainParamsMerge_ok_of_contracts ?_ ?_ ?_ ?_
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorFromName)]; exact hFrom
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorPushName)]; exact hPush
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := Varint.skipField3Name)]; exact hSkip
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
    let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.ChainParamsMergeGhost :=
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
    exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout
  have hEpochDir : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DecodeState.epochDirectionMergeName)
      ((DecodeState.epochDirectionMergeSpec A).inImage img) := by
    have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName)
        ((CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeSpec A).inImage img) := by
      refine epochDirectionMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorFromName)]; exact hFrom
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorPushName)]; exact hPush
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
      · rw [fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := Varint.skipField3Name)]; exact hSkip
      · rw [h_off_eq (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := bytesMerge3Name)
          (by rw [CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMerge_fnOff, bytesMerge3_fnOff]; bv_omega)]; exact hBytes
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
    let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.EpochDirectionMergeGhost :=
      ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
    exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout
  have hPolyEnc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName)
      ((polyEncoderMergeSpec A).inImage img) := by
    refine polyEncoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorFromName)]; exact hFrom
    · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorPushName)]; exact hPush
    · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
    · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := Varint.skipField3Name)]; exact hSkip
    · rw [h_off_eq (name := polyEncoderMergeName) (callee := bytesMerge3Name)
        (by rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
                (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]; bv_omega)]
      exact hBytes
    · rw [h_off_eq (name := polyEncoderMergeName) (callee := growOneVecU8Name)
        (by rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
                (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]; bv_omega)]
      exact hGrowVecU8
  have hPolyDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) := by
    refine polyDecoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorFromName)]; exact hFrom
    · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorPushName)]; exact hPush
    · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
    · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.skipField3Name)]; exact hSkip
    · rw [h_off_eq (name := polyDecoderMergeName) (callee := bytesMerge3Name)
        (by rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
                (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]; bv_omega)]
      exact hBytes
    · rw [h_off_eq (name := polyDecoderMergeName) (callee := growOneVecU8Name)
        (by rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
                (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]; bv_omega)]
      exact hGrowVecU8
  have hAuth : Auth.AuthMergeOkX img A ext :=
    Auth.auth_merge_ok_ext hFrom hPush hVarint hSkip hBytes
  have hUcEk := unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hBytes hAuth
  have hUcCt1 := unchunkedCt1SentMerge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hBytes hAuth
  have hV1State : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr v1StateMergeName)
      ((v1StateMergeSpec A img.base).inImage img) :=
    v1State_merge_ok_of_fnAddr
      hFrom hPush hVarint hSkip hC.dealloc
      (CryptoVerification.SpqrV1.Drop.drop_opt_proto_inner_state_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ct1_received_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_sent_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ek_sent_ct1_received_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_no_header_received_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_received_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_proto_unchunked_ct1_sent_ek_received_ok_ext hC.dealloc)
      (CryptoVerification.SpqrV1.Drop.drop_glue_proto_poly_encoder_ok_ext hC.dealloc)
      (chunked_keys_unsampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth)
      (chunked_keys_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
      (chunked_header_sent_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc hPolyDec)
      (chunkedCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyEnc)
      (chunkedEkSentCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyDec)
      (chunked_no_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyDec)
      (chunked_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hBytes hPolyDec)
      (chunkedCt1Sampled_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyEnc hPolyDec)
      (chunked_ek_received_ct1_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
      (chunkedCt1Acknowledged_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyDec)
      (chunked_ct2_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyEnc)
  exact decodeState_ok
    { b_page_aligned := hb
      of_drop_inner := of_drop_inner_canonical A
      of_cap_inner := of_cap_inner_ok A
      alloc := hAlloc
      decodeErrorFrom := hFrom
      decodeErrorPush := hPush
      decodeVarint2 := hVarint
      skipField3 := hSkip
      chainParamsMerge := hChainParams
      growOneChainEpoch := CryptoVerification.SpqrV1.Alloc.grow_one_chain_epoch_full_ok_ext hAlloc
      dropOptProtoInnerState := dropOptProtoInnerState_canonical_ok hb hC.dealloc
      dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_ok hb hC.dealloc
      bytesMerge3 := hBytes
      epochDirectionMerge := hEpochDir
      v1StateMerge := hV1State }

end CryptoVerification.SpqrV1.Top.DecodeState

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-- Assemble `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt canonicalV1InnerHeap img A ctl C K ext`
    without an `rng_fill` contract (`Stage2Contracts_trap`), using `decode_state_ok_x_trap`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContractsExt_of_callees_noRng
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith C.F) ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hhooks : SpqrHooks C A K ext)
    (hfrom_pb : StatesFromPbOkX img A C.F ext)
    (hnc : PolyNextChunkOkX img A ext := poly_next_chunk_ok_x himg hC.toAllocContracts) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt canonicalV1InnerHeap img A ctl C K ext where
  base_aligned := ProofLib.base_aligned_of_loads himg
  loads := himg
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A
  alloc := hC.toAllocContracts
  decodeState_ok := CryptoVerification.Cli.SpqrV1.Top.Send.decode_state_ok_x_trap himg hC
  statesFromPb_ok := hfrom_pb
  statesIntoPb_ok := states_into_pb_ok_x hC.toAllocContracts
  chainFromPb_ok := chain_from_pb_ok_x hC.toAllocContracts
  chainFromVn_ok := chain_from_version_negotiation_ok_ext' himg hhkdf hC.toAllocContracts
  chainAddEpoch_ok := chain_add_epoch_ok_ext' himg hhkdf hC.toAllocContracts
  chainSendKey_ok := chain_send_key_ok_ext' himg hhkdf hC.toAllocContracts hRO
  chainIntoPb_ok := chain_into_pb_ok_x hC.toAllocContracts
  messageSerialize_ok := message_serialize_ok_x hC.toAllocContracts hhooks
  encodeVarint_ok := spqr_encode_varint_ok_x hC.toAllocContracts hhooks
  authMacHdr_ok := auth_mac_hdr_ok_x himg hC.toAllocContracts hRO hhooks
  authUpdate_ok := auth_update_ok_ext himg hhkdf hC.toAllocContracts hRO hZero
  hkdfToVec_ok := hkdf_to_vec_ok_ext' img A (spqrHkdfWith C.F) ext hC.toAllocContracts hZero hhkdf
  encodeBytes_ok := encode_bytes_ok_x hC.toAllocContracts
  polyNextChunk_ok := hnc
  headerSentSendEkChunk_ok := headerSent_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1ReceivedSendEkChunk_ok := ct1Received_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1SampledSendCt1Chunk_ok := ct1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ekReceivedCt1SampledSendCt1Chunk_ok := ekReceivedCt1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ct2SampledSendCt2Chunk_ok := ct2Sampled_send_ct2_chunk_ok_x hC.toAllocContracts hnc
  dropProtoChain_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_proto_spqr_chain_ok_x hC.toAllocContracts
  dropChainEpochSlice_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_chain_epoch_slice_local1_ok_x hC.toAllocContracts

end CryptoVerification.SpqrV1.Top.Send

