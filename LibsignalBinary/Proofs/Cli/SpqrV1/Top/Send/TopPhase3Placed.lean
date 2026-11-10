/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1Placed
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Relocatable Phase 3 & 4 Composition of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Composes relocatable Phase 3b–3e (`AfterStatesBridge1Placed`, `AfterStatesBridge2Placed`),
Phase 4 (`AfterStatesFinishPlaced`), and the shared epilogue (`+3196 -> s0.x30`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

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
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open CryptoVerification.Cli.SpqrV1.ProtoRepr
open CryptoVerification.Cli.SpqrV1.Drop (chunkedStatesLocal1JumpTablePlacedAt chunkedStatesLocal1JumpTable_lsro_cli_intro dropChunkedStatesLocal1PlacedSpec)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

theorem step_send_from_320a4_placed {A : RustAlloc} {φ_panic : State → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s0 sm : State) (sp ret v_20 x21 x23 x25 x27 w0 w16 : BitVec 64)
    (stBytes msgBytes : Bytes) (salt : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (pq' : PqRatchetState) (Rest Fr : SepProp)
    (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl sm.mem)
    (hmsg_len : msgBytes.length < 2 ^ 32) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : sm.pc = spqrSendPlacedEntry + 6216#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx23 : sm.readReg64 .x23 = x23) (hx25 : sm.readReg64 .x25 = x25)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 4192#64)
    (hflag : x21 = LibsignalTripleRatchetRepr.noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !pq'.chain.isSome)
    (hpost : ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      (Pf ⊢ spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
        A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
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
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hfin := step_send_finish_320a4'_placed hdealloc sm ret v_20 x21 x23 x25 x27
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
    hcl hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 (by rw [hsp]; exact hx28) hflag hx25_ch hsp_align
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
       spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ Rest) := by
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
         spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ Rest)) by ac_rfl)) ?_
    exact sepConj_mono_left (memRegion_0_60_join sp w0 w16)
  refine SepWP.weaken_pre hjoin
    (SepWP.mono (step_epilogue_from_31a54_placed s0 s1 x23
      (spqrSendResultAt A ret (some (stBytes, salt, msgBytes)) ∗
       spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ Rest)
      hpc1 hrun1 (hsp1'.trans hsp_eq) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hcsf, hQf⟩
  exact ⟨Entails.trans hQf (Entails.of_eq (by ac_rfl)), hspf, hcsf, (htrf.trans htr1).trans htr⟩

theorem step_send_from_317fc_placed {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hmser : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi A)))
    (hinto : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)))
    (s0 s : State) (sp ret x23 : BitVec 64)
    (idx : BitVec 32) (msgKey : Bytes) (hmk_cases : msgKey = [] ∨ msgKey.length = 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hsp : s.sp = sp)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
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
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) := by
  have hsp_align : sp &&& 15#64 = 0#64 := by
    rw [hsp_eq]; exact beq_iff_eq.mp (ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide))
  obtain ⟨salt, hsalt_eq, hsalt_ent⟩ := msgKey_to_optMsgKeySlotsAt A sp msgKey hmk_cases
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion sp 8 ∗ memRegion (sp + 16#64) 24) ∗
    (optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
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
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
  rw [memRegion_sp_0_16_24_words sp]
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_20_old
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp18
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp10
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v0
  simp_rw [← encodeToVecOnPanic_congr htr]
  refine step_send_bridge2_317fc_placed hA hmser hinto hinv sp v_20_old v0 v_sp10 v_sp18 idx vn chainPb st1 msg
    hlen hsp_align
    (Frame := (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
    hpc hrun hsp rfl hx24 hx26 hx28 ⟨fun _ h => h, rfl, rfl⟩
    (by rw [memRegion_590_224_eq_88_136 sp, memRegion_1260_928_eq_88_840 sp]; ac_rfl) ?_
  intro sm g w0_new pq' hpc_m hrun_m hsp_m htr_m hx19_m hx21_m hx23_m _ hx25_ch hx27_m hx28_m hinv_m hinvm_lscro
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
        ((lsρ cliV1StateJtSym) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗
       ((∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)) =
      (((lsρ cliV1StateJtSym) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        statesIntoPbJumpTablePlacedAt) ∗
      ((((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey)) ∗
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
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Rest)) := by
    rw [hx22, memRegion_1060_80_eq_48_32 sp]; ac_rfl
  rw [hdrop]
  apply sepWPp_drop_left
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left hsalt_ent) ?_)
    (step_send_from_320a4_placed (φ_panic := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      hA.dealloc s0 sm sp ret (s.readReg64 .x20)
      (s.readReg64 .x21) x23 (sm.readReg64 .x25) (s.readReg64 .x27) w0_new
      (Prost.EncodeToVec.optChainCap g.chain chainPb)
      (PqRatchetState.encodeRaw { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) })
      (msg.serialize idx) salt g
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } Rest Fr post
      hinvm_lscro.1 (message_serialize_len_lt_2_32 msg idx) hsp0_align hsp_eq hpc_m hrun_m hsp_m (htr_m.trans htr)
      (hx19_m.trans hx19) hx21_m (hx23_m.trans hx23) rfl hx27_m hx28_m hflag hx25_ch (hpost salt hsalt_eq)
      (hinv_m.2.2.trans hvregs))
  exact Entails.of_eq (by ac_rfl)

theorem lsro_chunkedStatesLocal1JumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ chunkedStatesLocal1JumpTablePlacedAt ∗ P :=
  chunkedStatesLocal1JumpTable_lsro_cli_intro hro hP

theorem sepWPp_intro_chunkedStatesLocal1JumpTable_placed
    {prog : Program} {ret : BitVec 64} {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s (chunkedStatesLocal1JumpTablePlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R0 hm hL
  have hm' : s.mem ⊨ (chunkedStatesLocal1JumpTablePlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact lsro_chunkedStatesLocal1JumpTablePlacedAt hro hm
  exact h R0 hm' hL

/-! ## Phase 3 (`spqrSendPlacedEntry + 3196#64` -> return) -/

theorem step_send_from_314d8_placed {A : RustAlloc} {F : ShaCompress} {φ_panic : State → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hpanic : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked)
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec A F)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A)))
    (hfrom_vn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith F) A)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) A)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith F) A)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A)))
    (hser_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi A)))
    (hstates_into_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)))
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
    (hinv : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc : sm.pc = spqrSendPlacedEntry + 3196#64)
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
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          statesIntoPbJumpTablePlacedAt ∗ Rest) →
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
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc := spqrSend_dealloc_ok_placed hA
  apply sepWPp_intro_chunkedStatesLocal1JumpTable_placed hinv.2
  let Frame314d8 : SepProp :=
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
    memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
    memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
    memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
    messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
    spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
    (spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest)
  have hres := step_chain_resolve_314d8_to_7fc_placed (spqrHkdfWith F) hpanic hpanic_sub hdealloc
    hdrop_slice hdrop_states hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb
    s0 sm ret x21 x27 x23 pq.chain hchain_raw pq.versionNegotiation sOut.key sOut.msg.epoch
    sOut.state Frame314d8 Fr φ_panic hinv hpc hrun htr hx23_none hpstate
    hx19 hx21 hx22 hx23 (by rw [hsp]; exact hx25) (by rw [hsp]; exact hx26)
    hx27 (by rw [hsp]; exact hx28) hsp_align hφ hvregs
  rw [hsp] at hres
  have hpre_eq :
      chunkedStatesLocal1JumpTablePlacedAt ∗
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
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest) =
      ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame314d8 := by
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
        memRegion (sp + 0x190#64) 928 ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) ⊢
        chunkedStatesLocal1JumpTablePlacedAt ∗
        (memRegion sp 0x30 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
         chainOrigSlotAt sp x23 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) ∗
         stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
         (spqrSendResultAt A ret none ∗ A.pool ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          statesIntoPbJumpTablePlacedAt ∗ Rest)) := by
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
        chunkedStatesLocal1JumpTablePlacedAt ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
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
        chunkedStatesLocal1JumpTablePlacedAt ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
      have hb0_1f20 :
          memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
          memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) := by
        rw [memRegion_b0_1f20_eq sp]
      rw [← memRegion_cf0_1f20_eq_rest sp]
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
         memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A ret none ∗ A.pool ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ Rest) by ac_rfl)) ?_
      rw [hb0_1f20]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hjoin_err ?_
    apply sepWPp_drop_left (Drop := chunkedStatesLocal1JumpTablePlacedAt)
    have hep := step_epilogue_from_31a3c_placed hdealloc s0 s1 pq.versionNegotiation x23
      (spqrSendResultAt A ret none ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       statesIntoPbJumpTablePlacedAt ∗ Rest)
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
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (sp + 0x190#64) sOut.state ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) =
        chunkedStatesLocal1JumpTablePlacedAt ∗
        (optChainPBRegSlotAt A (sp + 0xd90#64) (s1.readReg64 .x25) chainPb ∗
          (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
            ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ Top.DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
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
          spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          (spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest)) := by
      dsimp only [Frame314d8]; ac_rfl
    rw [hdrop_ro]
    apply sepWPp_drop_left (Drop := chunkedStatesLocal1JumpTablePlacedAt)
    have hmk_cases := sendChainPhase_msgKey_cases F pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    have hch_le := sendChainPhase_raw_le (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    refine sepWPp_weaken_panic (φ1 := fun sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun sf ha => hφ sf (Or.inr ha)) ?_
    exact step_send_from_317fc_placed hA hser_call hstates_into_pb s0 s1 sp ret x23
      idx msgKey hmk_cases pq.versionNegotiation chainPb sOut.state sOut.msg
      (hpq'_len chainPb hch_le)
      (spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest) Fr post
      hsp0_align hsp_eq hpc1 hrun1 htr1 hsp1 hinv1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 hflag_1
      (fun salt hsalt sf Pf hpc_f hrun_f hPf hsp_f hcs_f htr_f =>
        hok_post idx msgKey chainPb salt hch hsalt sf Pf hpc_f hrun_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl))) hsp_f hcs_f htr_f)
      hvregs1

end CryptoVerification.Cli.SpqrV1.Top.Send
