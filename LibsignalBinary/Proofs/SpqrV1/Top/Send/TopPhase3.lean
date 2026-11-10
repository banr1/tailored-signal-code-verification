/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# `spqr::send::<HookRng>` Phase 3 and 4 Composition (`0x314d8 -> s0.x30`)

Composes Phase 3b–3c (`AfterStatesBridge1.lean`), Phase 3d–3e (`AfterStatesBridge2.lean`),
Phase 4 (`TopRegions.lean`), and the shared epilogue into `step_send_from_314d8`.
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

theorem step_send_from_320a4 {A : RustAlloc} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt img.base A ext)
    (s0 sm : State) (sp ret v_20 x21 x23 x25 x27 w0 w16 : BitVec 64)
    (stBytes msgBytes : Bytes) (salt : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (pq' : PqRatchetState) (Rest Fr : SepProp)
    (post : State → SepProp → Prop)
    (hmsg_len : msgBytes.length < 2 ^ 32) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 6216#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx23 : sm.readReg64 .x23 = x23) (hx25 : sm.readReg64 .x25 = x25)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 4192#64)
    (hflag : x21 = LibsignalTripleRatchetRepr.noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !pq'.chain.isSome)
    (hpost : ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      (Pf ⊢ spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
        A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTableAt img.base ∗ Rest) →
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
        spqrSendDropJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hfin := step_send_finish_320a4' hb hdealloc sm ret v_20 x21 x23 x25 x27
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
       spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest) := by
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
         spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest)) by ac_rfl)) ?_
    exact sepConj_mono_left (memRegion_0_60_join sp w0 w16)
  refine SepWP.weaken_pre hjoin
    (SepWP.mono (step_epilogue_from_31a54 s0 s1 x23
      (spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
       spqrSendDropJumpTableAt img.base ∗ A.pool ∗ Rest)
      hpc1 hrun1 (hsp1'.trans hsp_eq) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hcsf, hQf⟩
  exact ⟨Entails.trans hQf (Entails.of_eq (by ac_rfl)), hspf, hcsf, (htrf.trans htr1).trans htr⟩

theorem encodeToVecOnPanic_congr {s0 s : State} (htr : s.trace = s0.trace) (sf : State) :
    encodeToVecOnPanic s sf = encodeToVecOnPanic s0 sf := by
  unfold encodeToVecOnPanic allocFailedIn; rw [htr]

theorem memRegion_sp_0_16_24_words (sp : BitVec 64) :
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 =
      ∃∗ v_20_old : BitVec 64, ∃∗ v_sp18 : BitVec 64, ∃∗ v_sp10 : BitVec 64, ∃∗ v0 : BitVec 64,
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) := by
  have h20 : sp + 32#64 = sp + 0x20#64 := rfl
  rw [ProofLib.memRegion_eight sp,
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 16) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 16#64), ProofLib.memRegion_eight (sp + 24#64), ProofLib.memRegion_eight (sp + 32#64), h20]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem step_send_from_317fc {A : RustAlloc} {F : ShaCompress}
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
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4000#64)
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
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTableAt img.base ∗ Rest) →
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗ Rest)
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
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
  rw [memRegion_sp_0_16_24_words sp]
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_20_old
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp18
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp10
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v0
  simp_rw [← encodeToVecOnPanic_congr htr]
  refine step_send_bridge2_317fc hA himg hmser hinto rfl hinv sp v_20_old v0 v_sp10 v_sp18 idx vn chainPb st1 msg
    hlen hsp_align
    (Frame := (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗ Rest)
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
        ((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        statesIntoPbJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗
       ((∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗ Rest)) =
      (((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
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
        spqrSendDropJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)) := by
    rw [hx22, memRegion_1060_80_eq_48_32 sp]; ac_rfl
  rw [hdrop]
  apply sepWPp_drop_left
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left hsalt_ent) ?_)
    (step_send_from_320a4 (φ_panic := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
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

theorem rodata_chunkedStatesLocal1JumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ chunkedStatesLocal1JumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x35b7c 0x35b80)) (n := 10) (bs := chunkedStatesLocal1JumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem sepWPp_intro_chunkedStatesLocal1JumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s (chunkedStatesLocal1JumpTableAt img.base ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R0 hm hL
  have hm' : s.mem ⊨ (chunkedStatesLocal1JumpTableAt img.base ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact rodata_chunkedStatesLocal1JumpTable himg hF hm
  exact h R0 hm' hL

/-! ## Phase 3 (`0x314d8 -> s0.x30`) and Pure Model Reduction Lemmas -/

theorem sepWPp_bind_weaken_panic {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp Qp' : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q Qp)
    (hqp : ∀ sf P_f, Qp sf P_f → Qp' sf P_f)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWPp prog ret sm Pm Q' Qp') :
    SepWPp prog ret s P Q' Qp' :=
  sepWPp_bind (sepWPp_mono_post (fun _ _ h => h) hqp h1) h2

theorem optVersionNegotiationPBTail_to_proto (A : RustAlloc) (a30 w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) :
    (a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn ⊢
    ProtoRepr.optVersionNegotiationPBAt A a30 vn := by
  cases vn with
  | none =>
    unfold DecodeState.optVersionNegotiationPBTailAt ProtoRepr.optVersionNegotiationPBAt
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          memRegion (a30 + 16#64) 32) =
        ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro rfl
    rw [ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  | some v =>
    unfold DecodeState.optVersionNegotiationPBTailAt DecodeState.versionNegotiationPBTailAt
      ProtoRepr.optVersionNegotiationPBAt ProtoRepr.versionNegotiationPBAt rustBytesVecAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans (Entails.of_eq (show _ =
      ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
        ((a30 + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
        DecodeState.vecU8Heap A w0 w1 v.authKey) ∗
      (ProtoRepr.optChainParamsPBAt (a30 + 24#64) v.chainParams ∗
        ((a30 + 36#64) ↦₃₂ v.direction) ∗ ((a30 + 40#64) ↦₃₂ v.minVersion) ∗
        memRegion (a30 + 44#64) 4) by ac_rfl)) ?_
    exact sepConj_mono_left (words_to_vecU8 A a30 w0 w1 v.authKey)

/-! ### Pure Model Reduction Lemmas -/

open CryptoVerification.SpqrV1.Top.StateSize in
theorem sendChainPhase_raw_le (hkdf : HkdfFn) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendChainPhase hkdf chain vn key epoch = .ok (idx, msgKey, chainPb)) :
    optRaw rawChain chainPb ≤ optRaw rawChain chain + 624 := by
  unfold sendChainPhase at h
  rcases except_bind_eq_ok h with ⟨ch, hres, hstep⟩
  cases ch with
  | none =>
    unfold sendStepChain at hstep
    cases hk : key.isNone <;> simp only [hk, Bool.false_eq_true, ↓reduceIte] at hstep
    · contradiction
    · have hch : none = chainPb := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hstep)).2).2
      subst hch; simp
  | some c0 =>
    have hc0 := sendResolveChain_raw_le hkdf chain vn hres
    unfold sendStepChain at hstep
    have htail : ∀ c1 : Chain, rawChain c1.intoPb ≤ optRaw rawChain chain + 592 →
        (if epoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
          let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (c1.sendKey hkdf (epoch - 1#64))
          pure (idx, mk, some chain2.intoPb)) = .ok (idx, msgKey, chainPb) →
        optRaw rawChain chainPb ≤ optRaw rawChain chain + 624 := by
      intro c1 hc1 hs
      split at hs
      · contradiction
      · rcases except_bind_eq_ok hs with ⟨⟨c2, idx', mk'⟩, hsk, hp⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hsk
        have hc2 := Chain.sendKey_raw_le hkdf c1 (epoch - 1#64) hsk
        have hch : some c2.intoPb = chainPb := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hp)).2).2
        subst hch; simp only [optRaw_some]; omega
    cases key with
    | none =>
      dsimp only [pure, Pure.pure, Except.pure, Bind.bind, Except.bind] at hstep
      exact htail c0 (by omega) hstep
    | some es =>
      dsimp only at hstep
      rcases except_bind_eq_ok hstep with ⟨c1, hae, hs⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hae
      have hc1 := Chain.addEpoch_raw_le hkdf c0 es hae
      exact htail c1 (by omega) hs

theorem sendPanics_of_statesSend_panic {F : ShaCompress} {K : MlKem}
    {stateBytes rest : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {p : StatesPanic}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .error (.panic p)) :
    (spqrV1 F K).sendPanics stateBytes rest := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb; simp [hinner]
  have hfrom_deps := spqrDeps_statesFromPb_of_ok F K hfrom
  have hsend := send_of_statesFromPb_ok (spqrDeps F K) (spqrHkdfWith F) (tape := rest)
    hd hinner_pb hfrom_deps
  have hss : ((spqrDeps F K).statesSend st0 rest).1 = .error (.panic .v1) := by
    dsimp [spqrDeps, liftStatesResult]; rw [hsend0]
  apply spqrV1_sendPanics_of_panic (p := .v1)
  rw [hsend]; dsimp only; rw [hss]

theorem sendAfterStates_spqrDeps_eq {F : ShaCompress} {K : MlKem}
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (pqRatchetStateToPb pq)
      sOut.msg sOut.key sOut.state =
      match sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
      | .error e => .error e
      | .ok (idx, msgKey, chainPb) =>
        .ok { state := PqRatchetState.encodeRaw
                { versionNegotiation := pq.versionNegotiation
                  chain := chainPb
                  inner := some (.v1 sOut.state.into_pb) }
              msg := sOut.msg.serialize idx
              key := if msgKey.isEmpty then none else some msgKey } := by
  have heq := sendAfterStates_eq_bind_sendChainPhase (spqrDeps F K) (spqrHkdfWith F)
    (pqRatchetStateToPb pq) sOut.msg sOut.key sOut.state
  rw [heq]
  have hch : (pqRatchetStateToPb pq).chain = pq.chain := rfl
  have hvn : (pqRatchetStateToPb pq).versionNegotiation = pq.versionNegotiation := rfl
  have hep : (spqrDeps F K).msgEpoch sOut.msg = sOut.msg.epoch := rfl
  rw [hch, hvn, hep]
  cases sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
  | error e => rfl
  | ok val =>
    rcases val with ⟨idx, msgKey, chainPb⟩
    dsimp only
    obtain ⟨tail, hser⟩ := message_serialize_eq_cons sOut.msg idx
    have hmser : (spqrDeps F K).msgSerialize sOut.msg idx = 1#8 :: tail := hser
    rw [hmser]
    have hv1 : (1#8 != Version.v1.toU8) = false := by decide
    simp only [hv1, Bool.false_eq_true, ↓reduceIte]
    rw [← hser]
    rfl

theorem send_eq_of_statesSend_ok {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest')) :
    LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes rest =
      (sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (pqRatchetStateToPb pq)
        sOut.msg sOut.key sOut.state, rest') := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb; simp [hinner]
  have hfrom_deps := spqrDeps_statesFromPb_of_ok F K hfrom
  have hsend := send_of_statesFromPb_ok (spqrDeps F K) (spqrHkdfWith F) (tape := rest)
    hd hinner_pb hfrom_deps
  have hss : (spqrDeps F K).statesSend st0 rest = (.ok (sOut.msg, sOut.key, sOut.state), rest') := by
    dsimp [spqrDeps, liftStatesResult]; rw [hsend0]
  rw [hsend, hss]

theorem sendPanics_of_sendChainPhase_panic {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hpan : (sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true) :
    (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  rcases hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with e | _
  · rcases e with err | p
    · rw [hch] at hpan; contradiction
    · apply spqrV1_sendPanics_of_panic (p := p)
      rw [hsend, hafter, hch]
  · rw [hch] at hpan; contradiction

theorem send_and_draws_of_sendChainPhase_error {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {err : LibsignalSpqrV1.Error}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err)) :
    (spqrV1 F K).send stateBytes rest = none ∧
    (spqrV1 F K).draws stateBytes rest = rest.length - rest'.length ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  refine ⟨spqrV1_send_of_err (by rw [hsend, hafter, hch]), ?_,
    spqrV1_not_sendPanics_of_err (by rw [hsend, hafter, hch])⟩
  rw [spqrV1_draws_eq, hsend]

theorem send_and_draws_of_sendChainPhase_ok {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    {salt : CryptoGames.HKDF.Salt}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb))
    (hsalt : messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt) :
    (spqrV1 F K).send stateBytes rest =
      some (PqRatchetState.encodeRaw
              { versionNegotiation := pq.versionNegotiation
                chain := chainPb
                inner := some (.v1 sOut.state.into_pb) },
            salt, sOut.msg.serialize idx) ∧
    (spqrV1 F K).draws stateBytes rest = rest.length - rest'.length ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  refine ⟨spqrV1_send_of_ok (by rw [hsend, hafter, hch]) hsalt, ?_,
    spqrV1_not_sendPanics_of_ok (by rw [hsend, hafter, hch])⟩
  rw [spqrV1_draws_eq, hsend]

theorem sepWPp_weaken_panic {prog : Program} {ret : BitVec 64} {s : State}
    {P Fr : SepProp} {post : State → SepProp → Prop}
    {φ1 φ2 : State → Prop}
    (himp : ∀ sf, φ1 sf → φ2 sf)
    (h : SepWPp prog ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ1 sf⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ2 sf⌝ ∗ anyHeap) ∗ Fr)) := by
  intro R hmR hL
  rcases h R hmR hL with ⟨sm, hsteps, hok | ⟨hpan, P_f, hmPf, hQf⟩ | hoom⟩
  · exact ⟨sm, hsteps, Or.inl hok⟩
  · refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmPf, fun hmFr => ?_⟩)⟩
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono (himp sm))))
      (hQf hmFr)
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem step_send_from_314d8_ext {A : RustAlloc} {F : ShaCompress} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
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
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64)
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
          spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
          spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
        spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc := spqrSend_dealloc_ok hA
  apply sepWPp_intro_chunkedStatesLocal1JumpTable himg hinv.1
  let Frame314d8 : SepProp :=
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
    memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
    memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
    memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
    messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
    spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
    (spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
  have hres := step_chain_resolve_314d8_to_7fc_ext img (spqrHkdfWith F) hb hA.dealloc
    hdrop_slice hdrop_states hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb
    s0 sm ret x21 x27 x23 pq.chain hchain_raw pq.versionNegotiation sOut.key sOut.msg.epoch
    sOut.state Frame314d8 Fr φ_panic hinv hpc hrun htr hx23_none hpstate
    hx19 hx21 hx22 hx23 (by rw [hsp]; exact hx25) (by rw [hsp]; exact hx26)
    hx27 (by rw [hsp]; exact hx28) hsp_align hφ
  rw [hsp] at hres
  have hpre_eq :
      chunkedStatesLocal1JumpTableAt img.base ∗
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
        spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest) =
      ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame314d8 := by
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
        memRegion (sp + 0x190#64) 928 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) ⊢
        chunkedStatesLocal1JumpTableAt img.base ∗
        (memRegion sp 0x30 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
         chainOrigSlotAt sp x23 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) ∗
         stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
         (spqrSendResultAt A ret none ∗ A.pool ∗
          spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        chunkedStatesLocal1JumpTableAt img.base ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ Rest) by ac_rfl)) ?_
      rw [hb0_1f20]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hjoin_err ?_
    apply sepWPp_drop_left (Drop := chunkedStatesLocal1JumpTableAt img.base)
    have hep := step_epilogue_from_31a3c hA.dealloc s0 s1 pq.versionNegotiation x23
      (spqrSendResultAt A ret none ∗
       spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) =
        chunkedStatesLocal1JumpTableAt img.base ∗
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
          spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
          (spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)) := by
      dsimp only [Frame314d8]; ac_rfl
    rw [hdrop_ro]
    apply sepWPp_drop_left (Drop := chunkedStatesLocal1JumpTableAt img.base)
    have hmk_cases := sendChainPhase_msgKey_cases F pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    have hch_le := sendChainPhase_raw_le (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    refine sepWPp_weaken_panic (φ1 := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun sf ha => hφ sf (Or.inr ha)) ?_
    exact step_send_from_317fc img ext himg hA hser_call hstates_into_pb s0 s1 sp ret x23
      idx msgKey hmk_cases pq.versionNegotiation chainPb sOut.state sOut.msg
      (hpq'_len chainPb hch_le)
      (spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest) Fr post
      hsp0_align hsp_eq hpc1 hrun1 htr1 hsp1 hinv1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 hflag_1
      (fun salt hsalt sf Pf hpc_f hrun_f hPf hsp_f hcs_f htr_f =>
        hok_post idx msgKey chainPb salt hch hsalt sf Pf hpc_f hrun_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl))) hsp_f hcs_f htr_f)

theorem step_send_from_314d8 {A : RustAlloc} {F : ShaCompress} {φ_panic : State → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
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
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64)
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
          spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
          spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
        spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) :=
  step_send_from_314d8_ext img ext himg hb hA hdrop_slice hdrop_states hfrom_pb
    (chainFromVnOkExt_of_okX hfrom_vn) (chainAddEpochOkExt_of_okX hadd_epoch)
    (chainSendKeyOkExt_of_okX hsend_key) hinto_pb hser_call hstates_into_pb
    s0 sm sp ret x21 x27 x23 pq sOut Rest Fr post hsp0_align hsp_eq hchain_raw hpq'_len
    hinv hpc hrun hsp htr hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx23_none hpstate
    hφ herr_post hok_post hvregs

/-! ## Stack Region Split/Join Helpers (`0x309cc` and `0x314d8`) -/

theorem allocFailedIn_of_trace_eq {s0 s1 sf : State} (htr : s1.trace = s0.trace) :
    (allocFailedIn s1 sf ∧ s1.trace <+: sf.trace) ↔
    (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) := by
  unfold allocFailedIn
  rw [htr]

theorem optVN_30_to_proto (A : RustAlloc) (sp w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) :
    ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) vn ⊢
    ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn := by
  have h := optVersionNegotiationPBTail_to_proto A (sp + 0x30#64) w0 w1 vn
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem memRegion_0_30_pre_arm (sp : BitVec 64) :
    memRegion sp 0x30 =
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗
      memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16 := by
  rw [memRegion_0_30_eq sp,
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 8) (b' := sp + 24#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_16_16_and_32_16_post_arm (sp : BitVec 64) :
    memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16 =
      memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 16#64) (n := 16) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
      memRegion_32_16_eq_8_8 sp]
  ac_rfl

theorem pre_309cc_regions_eq (sp : BitVec 64) :
    memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
    memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗ statesSendPreArmScratch sp ∗
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp := by
  rw [memRegion_0_30_pre_arm sp, memRegion_b0_950_eq sp, memRegion_cf0_1f20_eq sp]
  unfold statesSendPreArmScratch
  ac_rfl

theorem post_3196_regions_eq (sp : BitVec 64) :
    memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      statesSendPostArmScratch sp ∗
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp =
    memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
      memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
      memRegion (sp + 0x8#64) 8 ∗ memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0xff0#64) 24 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp := by
  have h1 := statesSendPostArmScratch_split sp
  have h2 := memRegion_16_16_and_32_16_post_arm sp
  have hff0 : (sp + 4080#64 : BitVec 64) = sp + 0xff0#64 := rfl
  rw [hff0] at h1
  unfold stackRestB0_950
  calc
    _ = (statesSendPostArmScratch sp ∗ stackRestC sp) ∗
        memRegion (sp + 0x590#64) 920 ∗
        (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
         memRegion (sp + 0x580#64) 16 ∗ memRegion sp 8 ∗
         memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
         memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp) := by ac_rfl
    _ = (memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16) ∗
        (memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
         memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
         memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x8#64) 8 ∗
         memRegion sp 8 ∗ memRegion (sp + 1512#64) 136 ∗
         (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1648#64) 696 ∗ stackRestA sp) ∗
         memRegion (sp + 0xff0#64) 24 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp) := by
      rw [h1, memRegion_590_920_eq sp]; ac_rfl
    _ = _ := by rw [h2]; ac_rfl

end CryptoVerification.SpqrV1.Top.Send
