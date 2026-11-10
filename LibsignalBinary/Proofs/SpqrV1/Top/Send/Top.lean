/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Final
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.SpqrV1.Drop.States1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# End-to-End Verification of `spqr::send::<HookRng>` (`0x3085c`)

Composes Phase 1 (`Final.lean`), Phase 2 (`StatesSendDispatch.lean`), and Phases 3–4
(`TopPhase3.lean`) to verify `spqr::send::<libsignal_session::HookRng>` (`SpqrSendV1Stmt`,
`DEV-SPQR5`).
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
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.States CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-- Additional hook and callee contracts used by Phase 2 (`States::send`) and Phase 3
    (`drop_in_place::<chunked::States>`) alongside `SpqrSendContracts`. -/
structure SpqrSendExtraContracts
    (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  allocZeroed_hook : HookSat ext allocZeroedName (rustAllocZeroedSpec A)
  rngFill_hook : HookSat ext rngFillName (rngFillSpec ctl)
  mlkemFromSeed_hook : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K)
  mlkemPk1_hook : HookSat ext mlkemPk1Name mlkemPk1Spec
  mlkemPk2_hook : HookSat ext mlkemPk2Name mlkemPk2Spec
  mlkemEncaps1_hook : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K)
  fromSeed_pk1_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList
  fromSeed_pk2_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList
  macHdrPinned_ok : AuthMacHdrPinnedOkX img C.F A ext
  doReserve2_ok : DoReserve2OkX img A ext
  dropChunkedStates_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name)
    (dropChunkedStatesLocal1Spec A C.F img.base)

/-- Assemble `SpqrSendExtraContracts` from `Obj.Loads libsignalSessionImage img`,
    `TripleRatchetHooks`, and `SpqrHooks`. -/
theorem spqrSendExtraContracts_of_hooks
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    SpqrSendExtraContracts img A ctl C K (tripleRatchetExterns C ctl abs) := by
  have hC : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K)
      (tripleRatchetExterns C ctl abs) :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  have hRO : HookSat (tripleRatchetExterns C ctl abs) memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_tripleRatchetExterns C ctl abs
  have hSH_ext := spqrHooks_tripleRatchetExterns (ctl := ctl) hSH
  exact
    { allocZeroed_hook := hookSat_allocZeroed_tripleRatchetExterns hTH.allocZeroed
      rngFill_hook := ⟨rngFillHook ctl, rfl, rngFillHook_ok ctl⟩
      mlkemFromSeed_hook := hSH_ext.fromSeed
      mlkemPk1_hook := hSH_ext.pk1
      mlkemPk2_hook := hSH_ext.pk2
      mlkemEncaps1_hook := hSH_ext.encaps1
      fromSeed_pk1_slice := hSH.fromSeed_pk1
      fromSeed_pk2_slice := hSH.fromSeed_pk2
      macHdrPinned_ok := authMacHdrPinned_ok_ext_x himg
        (slice_concat_3_ok_x hC.toAllocContracts hRO) hSH_ext.hmac
        (AllocContractsX.of_AllocContracts hC.toAllocContracts)
      doReserve2_ok := doReserve2_ok_ext_x img hC.toAllocContracts
      dropChunkedStates_ok := drop_chunked_states_local1_ok_ext hC.toAllocContracts.dealloc }

/-- Assemble `SpqrSendExtraContracts` on arbitrary `ext` from `AllocContracts`, `memcpy` RO,
    `allocZeroed`, `rngFill`, and `SpqrHooks`. -/
theorem spqrSendExtraContracts_of_callees
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hRng : HookSat ext rngFillName (rngFillSpec ctl)) (hSH : SpqrHooks C A K ext) :
    SpqrSendExtraContracts img A ctl C K ext :=
  { allocZeroed_hook := hZero, rngFill_hook := hRng
    mlkemFromSeed_hook := hSH.fromSeed, mlkemPk1_hook := hSH.pk1
    mlkemPk2_hook := hSH.pk2, mlkemEncaps1_hook := hSH.encaps1
    fromSeed_pk1_slice := hSH.fromSeed_pk1, fromSeed_pk2_slice := hSH.fromSeed_pk2
    macHdrPinned_ok := authMacHdrPinned_ok_ext_x himg
      (slice_concat_3_ok_x hA hRO) hSH.hmac (AllocContractsX.of_AllocContracts hA)
    doReserve2_ok := doReserve2_ok_ext_x img hA
    dropChunkedStates_ok := drop_chunked_states_local1_ok_ext hA.dealloc }

set_option maxHeartbeats 800000 in
/-- Full active V1 continuation (`0x309cc -> s0.readReg64 .x30`) on `SpqrSendContractsExt` whenever
    `st0.send K x.rest = .ok (sOut, rest')`. -/
theorem step_send_active_of_statesSend_ok_ext {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)} (hC : SpqrSendContractsExt H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext) (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi C.F)) (rest' : Bytes)
    (hdec : spqrDecodeState x.st.bytes = .ok pq) (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (hsend0 : st0.send K x.rest = .ok (sOut, rest'))
    (w0 w1 : BitVec 64) (_hw0 : w0 ≠ DecodeState.none2Cap) (sf : State) (hinvf : ImgCallInv img sf)
    (hpcf : sf.pc = spqrSendEntry img.base + statesSendArmOffset st0) (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 0x1f80#64) (htrf : sf.trace = s0.trace)
    (hx19 : sf.readReg64 .x19 = x.ret) (hx20 : sf.readReg64 .x20 = chunkedStatesWord0 st0)
    (_hx21 : sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64) (_hx23 : sf.readReg64 .x23 = w0)
    (hx24 : sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64)
    (hx25 : sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64)
    (hx26 : sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx28 : sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64)
    (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗ chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗ memRegion x.ret 72 ∗ A.pool ∗
        statesFromPbJumpTableAt img.base ∗ spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗ spqrSendEncodeJumpTableAt img.base ∗
         spqrSendDropJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)))
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
          spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  let sp : BitVec 64 := s0.sp - 0x1f80#64
  have hfsp_align : (sp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp_align (by decide)
  have hdec_deps := decodeState_spqrDeps_of_spqrDecodeState_ok C.F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb; simp [hinner]
  have hraw := StateSize.decodeState_spqrDeps_raw_le hdec_deps
  have hraw' :
      optRaw rawVN pq.versionNegotiation + optRaw rawChain pq.chain + rawV1State v1 ≤
        201 * x.st.bytes.length := by
    simpa only [pbToPqRatchetState, pqRatchetStateToPb, rawPqState, rawPqInner,
      hinner, Option.map, optRaw_some] using hraw
  have hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54 := by omega
  rcases States.from_pb_raw_le hfrom with ⟨hst0_raw, _⟩
  have hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63 := by
    intro st hst; subst hst
    have hrk := headerReceived_rootKey_le_rawV1State st
    omega
  have hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      Prost.EncodeToVec.pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 :=
    fun chainPb hch_le =>
      pqRatchetStatePBEncodedLen_lt_of_send C.F K hlen hdec_deps hinner_pb hfrom hsend0 hch_le
  let RestTail : SepProp :=
    statesFromPbJumpTableAt img.base ∗ spqrSendStatesJumpTableAt img.base ∗
    x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base
  let FrameArm : SepProp :=
    ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
    memRegion x.ret 72 ∗
    (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
     memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
     memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
    spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
    spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ RestTail
  have hlog_eq : logOff img = spqrLogLevelZeroAt img.base := rfl
  have hpre_arm :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)) ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
        spqrLogLevelZeroAt img.base ∗ tapeAt ctl x.cur x.rest ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
        memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
        memRegion (sp + 0x590#64) 920 ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        statesSendPreArmScratch sp) ∗ FrameArm := by
    have hvn := optVN_30_to_proto A sp w0 w1 pq.versionNegotiation
    have hreg := pre_309cc_regions_eq sp
    rw [hlog_eq]
    dsimp only [FrameArm, RestTail]
    refine Entails.trans (Entails.of_eq (show _ =
      (((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation) ∗
      (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
        spqrLogLevelZeroAt img.base ∗ tapeAt ctl x.cur x.rest ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion x.ret 72 ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
        spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗
        statesFromPbJumpTableAt img.base ∗ spqrSendStatesJumpTableAt img.base ∗
        x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hvn) ?_
    rw [hreg]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_arm ?_
  let mid3196 := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64
  let P3196 (sm : State) : SepProp :=
    (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
      chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
      memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x950#64) 928 ∗
      optEpochSecretRegSlotAt A sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
      messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
      statesSendPostArmScratch sp ∗
      tapeAfter ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ FrameArm
  let post3196 : State → SepProp → Prop := fun sm Pm =>
    ImgCallInv img sm ∧ sm.sp = sp ∧ sm.trace = sf.trace ∧
    sm.readReg64 .x19 = sf.readReg64 .x19 ∧
    sm.readReg64 .x20 = chunkedStatesWord0 sOut.state ∧
    sm.readReg64 .x22 = sOut.msg.epoch ∧
    sm.readReg64 .x25 = sp + 0x550#64 ∧
    sm.readReg64 .x26 = sp + 0x1260#64 ∧
    sm.readReg64 .x28 = sf.readReg64 .x28 ∧
    (sm.readReg64 .x23 = LibsignalTripleRatchetRepr.noneCap ↔ pq.chain = none) ∧
    sm.pstate = addsPState64 (sm.readReg64 .x23) 1#64 ∧
    calleeSavedVRegs sm = calleeSavedVRegs sf ∧
    Pm = P3196 sm
  have hpcf' : sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + statesSendArmOffset st0 := by
    rwa [← fnAddr_spqrSend_eq] at hpcf
  have hphase2 :
      SepWPp (tripleRatchetProgAtExt img.base ext) mid3196 sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗
          GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
          spqrLogLevelZeroAt img.base ∗ tapeAt ctl x.cur x.rest ∗
          ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
          memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          memRegion (sp + 0x590#64) 920 ∗
          chunkedStatesAt A (sp + 0x950#64) st0 ∗
          statesSendPreArmScratch sp) ∗ FrameArm)
        post3196
        (fun s_pan P_f => (s_pan.mem ⊨ P_f ∗ R) →
          (s_pan.mem ⊨ (⌜allocFailedIn sf s_pan ∧ sf.trace <+: s_pan.trace⌝ ∗ anyHeap) ∗ R)) := by
    refine step_send_statesSend_ext (ctl := ctl) img A ext hC.loads hC.base_aligned hC.alloc
      hE.allocZeroed_hook hE.rngFill_hook hE.mlkemFromSeed_hook hE.mlkemPk1_hook hE.mlkemPk2_hook
      hE.mlkemEncaps1_hook hE.fromSeed_pk1_slice hE.fromSeed_pk2_slice
      hE.macHdrPinned_ok hE.doReserve2_ok hC.encodeBytes_ok hC.polyNextChunk_ok hC.hkdfToVec_ok hC.authUpdate_ok
      hC.headerSentSendEkChunk_ok hC.ct1ReceivedSendEkChunk_ok hC.ct1SampledSendCt1Chunk_ok
      hC.ct2SampledSendCt2Chunk_ok hC.ekReceivedCt1SampledSendCt1Chunk_ok
      (s0 := sf) (s := sf) sp x.cur x.rest rest' pq.chain st0 sOut hroot_len hsend0
      hinvf hpcf' hrunf hspf hfsp_align rfl rfl hx20 hx24 hx25 hx26 hx28 rfl rfl rfl ?_
    intro sm hinv_m hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx22_m hx25_m hx26_m hx28_m hx23_none_m hpstate_m hvregs_m
    exact SepWPp.done hpc_m hrun_m
      ⟨hinv_m, hsp_m, htr_m, hx19_m, hx20_m, hx22_m, hx25_m, hx26_m, hx28_m, hx23_none_m, hpstate_m, hvregs_m, rfl⟩
  refine sepWPp_bind_weaken_panic hphase2 ?_ ?_
  · intro s_pan P_f hqp hm
    have hm' := hqp hm
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono fun h => ?_))) hm'
    rcases (allocFailedIn_of_trace_eq htrf).mp h with ⟨ha, htr_p⟩
    exact ⟨Or.inl ha, htr_p⟩
  · rintro sm Pm hpc_m hrun_m
      ⟨hinv_m, hsp_m, htr_m, hx19_m, _, hx22_m, hx25_m, hx26_m, hx28_m, hx23_none_m, hpstate_m, hvregs_m, rfl⟩
    rw [htrf] at htr_m
    rw [hx19] at hx19_m
    rw [hx28] at hx28_m
    let Rest314d8 : SepProp :=
      tapeAfter ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      GF.Mul2U16.tokenInitAt img.base ∗ GF.UnacceleratedMul.reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ RestTail
    have hP3196_eq :
        P3196 sm =
        (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
          ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
          optEpochSecretRegSlotAt A sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
          memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
          memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
          memRegion (sp + 0x8#64) 8 ∗ memRegion x.ret 72 ∗
          chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
          memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
          memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
          spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
          spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest314d8) := by
      have hreg := post_3196_regions_eq sp
      calc
        P3196 sm = (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
              memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
              statesSendPostArmScratch sp ∗
              memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
              memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
              memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
            (ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
              ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
              optEpochSecretRegSlotAt A sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
              memRegion x.ret 72 ∗ chunkedStatesAt A (sp + 0x190#64) sOut.state ∗
              A.pool ∗ stackAt sp spqrSendCalleeStack ∗
              memRegion (sp + 0x950#64) 928 ∗
              messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
              spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTableAt img.base ∗
              spqrSendEncodeJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ Rest314d8) := by
          dsimp only [P3196, FrameArm, Rest314d8]; ac_rfl
        _ = _ := by rw [hreg]; ac_rfl
    rw [hP3196_eq]
    refine step_send_from_314d8_ext img ext hC.loads hC.base_aligned hC.alloc
      hC.dropChainEpochSlice_ok hE.dropChunkedStates_ok hC.chainFromPb_ok hC.chainFromVn_ok
      hC.chainAddEpoch_ok hC.chainSendKey_ok hC.chainIntoPb_ok hC.messageSerialize_ok
      hC.statesIntoPb_ok s0 sm sp x.ret (sm.readReg64 .x21) (sm.readReg64 .x27) (sm.readReg64 .x23)
      pq sOut Rest314d8 R _ hsp_align rfl hchain_raw hpq'_len hinv_m hpc_m hrun_m hsp_m htr_m
      hx19_m rfl hx22_m rfl hx25_m hx26_m rfl hx28_m hx23_none_m hpstate_m
      ?hφ ?herr ?hok
    case hφ =>
      intro s_pan hpan
      rcases hpan with ⟨hch_pan, htr_p⟩ | ⟨ha, htr_p⟩
      · refine ⟨Or.inr (sendPanics_of_sendChainPhase_panic hdec hinner hfrom hsend0 hch_pan), ?_⟩
        rw [htr_p]
      · exact ⟨Or.inl ha, htr_p⟩
    case herr =>
      intro err hch sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_error hdec hinner hfrom hsend0 hch
      refine ⟨hsp_f, hcs_f, ?_⟩
      rw [hsend_eq, hdraws_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoAt, spqrSendRoAt]
      rw [hlog_eq]
      exact Entails.of_eq (by ac_rfl)
    case hok =>
      intro idx msgKey chainPb salt hch hsalt sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_ok hdec hinner hfrom hsend0 hch hsalt
      refine ⟨hsp_f, hcs_f, ?_⟩
      rw [hsend_eq, hdraws_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoAt, spqrSendRoAt]
      rw [hlog_eq]
      exact Entails.of_eq (by ac_rfl)

/-- Full active V1 continuation (`0x309cc -> s0.readReg64 .x30`) whenever
    `st0.send K x.rest = .ok (sOut, rest')`. -/
theorem step_send_active_of_statesSend_ok {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)} (hC : SpqrSendContracts H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext) (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi C.F)) (rest' : Bytes)
    (hdec : spqrDecodeState x.st.bytes = .ok pq) (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (hsend0 : st0.send K x.rest = .ok (sOut, rest'))
    (w0 w1 : BitVec 64) (_hw0 : w0 ≠ DecodeState.none2Cap) (sf : State) (hinvf : ImgCallInv img sf)
    (hpcf : sf.pc = spqrSendEntry img.base + statesSendArmOffset st0) (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 0x1f80#64) (htrf : sf.trace = s0.trace)
    (hx19 : sf.readReg64 .x19 = x.ret) (hx20 : sf.readReg64 .x20 = chunkedStatesWord0 st0)
    (_hx21 : sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64) (_hx23 : sf.readReg64 .x23 = w0)
    (hx24 : sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64)
    (hx25 : sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64)
    (hx26 : sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx28 : sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64)
    (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢
          ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  step_send_active_of_statesSend_ok_ext hC.toExt hE x s0 R hlen hsp_align pq v1 st0 sOut rest'
    hdec hinner hfrom hsend0 w0 w1 _hw0 sf hinvf hpcf hrunf hspf htrf
    hx19 hx20 _hx21 _hx23 hx24 hx25 hx26 hx28 hvregsf

def rawInnerKeysUnsampled : V1State.InnerState → Nat
  | .keysUnsampled v => rawChKeysUnsampled v
  | _ => 0

def rawV1KeysUnsampled (v : V1State) : Nat :=
  optRaw rawInnerKeysUnsampled v.innerState

def rawPqInnerKeysUnsampled : PqRatchetState.Inner → Nat
  | .v1 v => rawV1KeysUnsampled v

def rawPqKeysUnsampled (m : PqRatchetState) : Nat :=
  optRaw rawPqInnerKeysUnsampled m.inner

private theorem branch_ite_ok {S : Type} {R : Prop} {c : Bool} [Decidable (c = true)]
    {a b : Except Proto.DecodeErr (S × Bytes)} {x : S × Bytes}
    (h : (if c then a else b) = .ok x)
    (ha : a = .ok x → R) (hb : b = .ok x → R) : R := by
  split at h
  · exact ha h
  · exact hb h

private theorem branch_skip_one {S : Type} {rawS : S → Nat} {s s' : S}
    {wt : Proto.WireType} {tag : BitVec 32} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.skipField wt tag rest depth) (fun bs' => Except.ok (s, bs')) = .ok (s', rest')) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  rcases he : Proto.skipField wt tag rest depth with err | bs'
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨skipField_length_le he, Nat.le_add_right _ _⟩

@[simp, reducible] private def unOk1 {S : Type} (s : S) : Except Proto.DecodeErr (S × Bytes) → S
  | .ok (s', _) => s'
  | .error _ => s

private theorem bind_pair_ok1 {S α : Type} {e : Except Proto.DecodeErr (α × Bytes)}
    {k : α × Bytes → Except Proto.DecodeErr (S × Bytes)} {s s' : S} {rest' : Bytes}
    (h : Bind.bind e k = .ok (s', rest'))
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs')) :
    ∃ v, e = .ok (v, rest') ∧ s' = unOk1 s (k (v, rest')) := by
  rcases he : e with err | ⟨v, bs'⟩
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind] at h
    rw [hk v bs'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨v, rfl, rfl⟩

private theorem branch_oneof_zero {Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    (hb : MergeFieldBound mergeSub rawSub Ksub)
    {s s' : Option V1State.InnerState} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (Option V1State.InnerState × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hz : ∀ v, optRaw rawInnerKeysUnsampled (unOk1 s (k (v, rest'))) = 0)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧
      optRaw rawInnerKeysUnsampled s' ≤ optRaw rawInnerKeysUnsampled s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, _⟩ := mergeMessage_raw_le hb he
  rw [hz v]
  exact ⟨hle, Nat.zero_le _⟩

private theorem branch_oneof_one {S Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat}
    {rawS : S → Nat}
    {s s' : S} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub 1)
    (hprev : rawSub prev ≤ rawS s) (hg : ∀ v, rawS (unOk1 s (k (v, rest'))) = rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, hv⟩ := mergeMessage_raw_le hb he
  rw [hg v]
  exact ⟨hle, by omega⟩

private theorem branch_optMessage_one {S Sub : Type} [Inhabited Sub]
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat}
    {s s' : S} {old : Option Sub}
    {k : Option Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeOptMessage mergeSub wt old rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hdef : rawSub default = 0)
    (hg : ∀ v, rawS (unOk1 s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, _⟩ := mergeOptMessage_raw_le hb hdef he
  rw [hg v]
  exact ⟨hle, Nat.le_add_right _ _⟩

theorem mergeFieldBound_chKeysUnsampled_one :
    MergeFieldBound V1State.Chunked.KeysUnsampled.mergeField rawChKeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Chunked.KeysUnsampled.mergeField at h
  refine branch_ite_ok h (fun h => ?_) branch_skip_one
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  obtain ⟨hle, hv⟩ := mergeOptMessage_raw_le mergeFieldBound_ucKeysUnsampled rfl he
  exact ⟨hle, by simp only [unOk1, rawChKeysUnsampled]; omega⟩

theorem mergeFieldBound_innerKeysUnsampled :
    MergeFieldBound V1State.InnerState.merge (optRaw rawInnerKeysUnsampled) 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.InnerState.merge at h
  exact branch_ite_ok h
    (fun h => branch_oneof_one h mergeFieldBound_chKeysUnsampled_one
      (by cases s with | none => rfl | some is => cases is <;> exact Nat.le_refl _)
      (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chKeysSampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chHeaderSent h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Received h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chEkSentCt1Received h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chNoHeaderReceived h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chHeaderReceived h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Sampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chEkReceivedCt1Sampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Acknowledged h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt2Sampled h (fun _ => rfl))
      branch_skip_one))))))))))

theorem mergeFieldBound_v1KeysUnsampled :
    MergeFieldBound V1State.mergeField rawV1KeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.mergeField at h
  refine branch_ite_ok h (fun h => ?_) branch_skip_one
  obtain ⟨is', he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_innerKeysUnsampled s.innerState tag wt rest depth is' rest' he

theorem mergeFieldBound_pqInnerKeysUnsampled :
    MergeFieldBound PqRatchetState.Inner.merge (optRaw rawPqInnerKeysUnsampled) 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.Inner.merge at h
  exact branch_ite_ok h
    (fun h => branch_oneof_one h mergeFieldBound_v1KeysUnsampled
      (by cases s with | none => rfl | some is => cases is; exact Nat.le_refl _)
      (fun _ => rfl))
    branch_skip_one

theorem mergeFieldBound_pqKeysUnsampled :
    MergeFieldBound PqRatchetState.mergeField rawPqKeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.mergeField at h
  refine branch_ite_ok h (fun h => branch_optMessage_one h mergeFieldBound_vn rfl (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_optMessage_one h mergeFieldBound_chain rfl (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => ?_) branch_skip_one))
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_pqInnerKeysUnsampled s.inner tag wt rest depth v rest' he

theorem spqrDecodeState_rawPqKeysUnsampled_le {bs : Bytes} {st : PqRatchetState}
    (h : Proto.spqrDecodeState bs = .ok st) : rawPqKeysUnsampled st ≤ bs.length := by
  unfold Proto.spqrDecodeState at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp [rawPqKeysUnsampled, optRaw]
  · rcases hdec : PqRatchetState.decode bs with e | st'
    · simp [hdec] at h
    · simp only [hdec, Except.ok.injEq] at h; subst h
      have hraw := mergeFieldsLoop_raw_le mergeFieldBound_pqKeysUnsampled bs.length default bs
        Proto.RECURSION_LIMIT st' hdec
      have hdef : rawPqKeysUnsampled default = 0 := rfl
      omega

theorem keysUnsampled_macKey_le_of_from_pb {F : ShaCompress} {pq : PqRatchetState} {v1 : V1State}
    {st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)} {bs : Bytes}
    (hdec : Proto.spqrDecodeState bs = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok (.keysUnsampled st)) :
    st.uc.auth.macKey.length ≤ bs.length := by
  have h1 := spqrDecodeState_rawPqKeysUnsampled_le hdec
  have h2 : rawPqKeysUnsampled pq = rawV1KeysUnsampled v1 := by
    simp [rawPqKeysUnsampled, hinner, rawPqInnerKeysUnsampled]
  rcases States.from_pb_raw_le hfrom with ⟨hraw_from, _⟩
  have hmac := keysUnsampled_macKey_le_rawV1State st
  have hv1_eq : rawV1State v1 = rawV1KeysUnsampled v1 := by
    unfold States.from_pb at hfrom
    rcases his : v1.innerState with _ | is
    · rw [his] at hfrom; nomatch hfrom
    · rw [his] at hfrom
      cases is with
      | keysUnsampled ch =>
        simp [rawV1State, rawV1KeysUnsampled, his, rawInnerState, rawInnerKeysUnsampled]
      | keysSampled ch =>
        rcases hsub : Chunked.SendEk.KeysSampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | headerSent ch =>
        rcases hsub : Chunked.SendEk.HeaderSent.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Received ch =>
        rcases hsub : Chunked.SendEk.Ct1Received.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ekSentCt1Received ch =>
        rcases hsub : Chunked.SendEk.EkSentCt1Received.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | noHeaderReceived ch =>
        rcases hsub : Chunked.SendCt.NoHeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | headerReceived ch =>
        rcases hsub : Chunked.SendCt.HeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Sampled ch =>
        rcases hsub : Chunked.SendCt.Ct1Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ekReceivedCt1Sampled ch =>
        rcases hsub : Chunked.SendCt.EkReceivedCt1Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Acknowledged ch =>
        rcases hsub : Chunked.SendCt.Ct1Acknowledged.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct2Sampled ch =>
        rcases hsub : Chunked.SendCt.Ct2Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
  omega

/-- Under `bs.length < 2 ^ 32` and `64 ≤ tape.length` (`DEV-SPQR5`), any `st0` decoded by
    `States.from_pb` with `statesPolyEncoderValid st0` either succeeds in `st0.send K tape`
    or is in the `.headerReceived` arm where `K.encaps1` returns `none`. -/
theorem statesSend_ok_or_headerReceived_encaps1_of_le_64 {F : ShaCompress} (K : MlKem)
    {pq : PqRatchetState} {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {bs tape : Bytes}
    (hlen : bs.length < 2 ^ 32)
    (h64 : 64 ≤ tape.length)
    (hdec : Proto.spqrDecodeState bs = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hv : statesPolyEncoderValid st0) :
    (∃ sOut tape', st0.send K tape = .ok (sOut, tape')) ∨
    (∃ st, st0 = .headerReceived st ∧
      K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none ∧
      st0.send K tape = .error (.panic .encaps1Failed)) := by
  cases st0 with
  | keysUnsampled st =>
    have hk := keysUnsampled_macKey_le_of_from_pb hdec hinner hfrom
    exact Or.inl (send_keysUnsampled_ok_of_le_64 K st (by omega) h64)
  | keysSampled st => exact Or.inl (send_keysSampled_ok_of_valid K tape st hv)
  | headerSent st => exact Or.inl (send_headerSent_ok_of_valid K tape st hv)
  | ct1Received st => exact Or.inl (send_ct1Received_ok_of_valid K tape st hv)
  | ekSentCt1Received st => exact Or.inl ⟨_, _, rfl⟩
  | noHeaderReceived st => exact Or.inl ⟨_, _, rfl⟩
  | headerReceived st =>
    rcases send_headerReceived_ok_or_encaps1_of_le_32 (tape := tape) K st (by omega) with hok | ⟨henc, herr⟩
    · exact Or.inl hok
    · exact Or.inr ⟨st, rfl, henc, herr⟩
  | ct1Sampled st => exact Or.inl (send_ct1Sampled_ok_of_valid K tape st hv)
  | ekReceivedCt1Sampled st => exact Or.inl (send_ekReceivedCt1Sampled_ok_of_valid K tape st hv)
  | ct1Acknowledged st => exact Or.inl ⟨_, _, rfl⟩
  | ct2Sampled st => exact Or.inl (send_ct2Sampled_ok_of_valid K tape st hv)

set_option maxHeartbeats 800000 in
/-- Full active V1 continuation (`0x309cc -> s0.readReg64 .x30`) on `SpqrSendContractsExt` for all
    11 arms of `st0` under `64 ≤ x.rest.length` (`DEV-SPQR5`). -/
theorem step_send_active_of_le_64_ext
    {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendContractsExt H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext)
    (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32)
    (hrest_len : 64 ≤ x.rest.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (hdec : spqrDecodeState x.st.bytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (w0 w1 : BitVec 64) (hw0 : w0 ≠ DecodeState.none2Cap)
    (sf : State) (hinvf : ImgCallInv img sf)
    (hpcf : sf.pc = spqrSendEntry img.base + statesSendArmOffset st0)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 0x1f80#64)
    (htrf : sf.trace = s0.trace)
    (hx19 : sf.readReg64 .x19 = x.ret)
    (hx20 : sf.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx21 : sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx23 : sf.readReg64 .x23 = w0)
    (hx24 : sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64)
    (hx25 : sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64)
    (hx26 : sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx28 : sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64)
    (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢
          ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  let sp : BitVec 64 := s0.sp - 0x1f80#64
  let RestPre : SepProp :=
    (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
      memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
      spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0) ∗
     (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
      (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
       spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
       statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base))
  have hpull_valid :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)) ⊢
      ⌜statesPolyEncoderValid st0⌝ ∗
      ((stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base))) := by
    have hv0 := chunkedStatesAt_entails_polyEncoderValid A (sp + 0x950#64) st0
    refine Entails.trans (Entails.of_eq (show _ = chunkedStatesAt A (sp + 0x950#64) st0 ∗ RestPre by
      dsimp only [RestPre]; ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hv0) ?_
    exact Entails.of_eq (by dsimp only [RestPre]; ac_rfl)
  refine SepWPp.weaken_pre hpull_valid (ProofLib.SepWPp.pure_elim fun hv => ?_)
  rcases statesSend_ok_or_headerReceived_encaps1_of_le_64 K hlen hrest_len hdec hinner hfrom hv with
    ⟨sOut, rest', hsend0⟩ | ⟨st, rfl, hencaps, hsend_err⟩
  · exact step_send_active_of_statesSend_ok_ext hC hE x s0 R hlen hsp_align pq v1 st0 sOut rest'
      hdec hinner hfrom hsend0 w0 w1 hw0 sf hinvf hpcf hrunf hspf htrf
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  · have hfsp_align : (sp &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp_align (by decide)
    have hpan : (spqrV1 C.F K).sendPanics x.st.bytes x.rest :=
      sendPanics_of_statesSend_panic hdec hinner hfrom hsend_err
    have hpcf' : sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64 := by
      rwa [← fnAddr_spqrSend_eq] at hpcf
    let FramePan : SepProp :=
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
      (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
       memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 0x590#64) 920 ∗
       (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp)) ∗
      memRegion x.ret 72 ∗ statesFromPbJumpTableAt img.base ∗
      spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0 ∗
      x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
      GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
      spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
      statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base
    have hpre_pan :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
          spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
          (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
           spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
           statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tapeAt ctl x.cur x.rest ∗
          chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗ statesSendPreArmScratch sp) ∗ FramePan := by
      have hreg := pre_309cc_regions_eq sp
      refine Entails.of_eq ?_
      calc
        _ = (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
              memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
            (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tapeAt ctl x.cur x.rest ∗
              chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗
              ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
              DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
              ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
              memRegion x.ret 72 ∗ statesFromPbJumpTableAt img.base ∗
              spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs sp s0 ∗
              x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
              GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
              spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
              statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base) := by ac_rfl
        _ = _ := by dsimp only [FramePan]; rw [hreg]; ac_rfl
    refine SepWPp.weaken_pre hpre_pan ?_
    refine sepWPp_mono_post (fun _ _ hq => hq) (fun s_pan P_f hqp hm => ?_)
      (step_send_arm_headerReceived_encaps1_none (R := R) (Frame := FramePan)
        hC.base_aligned hC.alloc hE.allocZeroed_hook hE.rngFill_hook hE.mlkemEncaps1_hook
        sp x.cur x.rest (by omega) st hencaps hpan hinvf hpcf' hrunf hspf hfsp_align
        htrf hx24 hx26 hx28 rfl)
    have hm' := hqp hm
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono fun ⟨hp, htr_p⟩ => ?_))) hm'
    exact ⟨hp.symm, htr_p⟩

/-- Full active V1 continuation (`0x309cc -> s0.readReg64 .x30`) for all 11 arms of `st0`
    under `64 ≤ x.rest.length` (`DEV-SPQR5`). -/
theorem step_send_active_of_le_64 {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)} (hC : SpqrSendContracts H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext) (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32) (hrest_len : 64 ≤ x.rest.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (hdec : spqrDecodeState x.st.bytes = .ok pq) (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (w0 w1 : BitVec 64) (hw0 : w0 ≠ DecodeState.none2Cap) (sf : State) (hinvf : ImgCallInv img sf)
    (hpcf : sf.pc = spqrSendEntry img.base + statesSendArmOffset st0) (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 0x1f80#64) (htrf : sf.trace = s0.trace)
    (hx19 : sf.readReg64 .x19 = x.ret) (hx20 : sf.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx21 : sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64) (hx23 : sf.readReg64 .x23 = w0)
    (hx24 : sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64)
    (hx25 : sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64)
    (hx26 : sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx28 : sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64)
    (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ statesFromPbJumpTableAt img.base ∗
        spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
         spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
         statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢
          ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  step_send_active_of_le_64_ext hC.toExt hE x s0 R hlen hrest_len hsp_align pq v1 st0
    hdec hinner hfrom w0 w1 hw0 sf hinvf hpcf hrunf hspf htrf
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf

/-- Active Phase 2 + Phase 3 continuation obligation under `DEV-SPQR5` (`64 ≤ x.rest.length`). -/
def SpqrSendActiveContinuationPanic64
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (x : SendCall) (s0 : State) (R : SepProp),
    x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → (s0.sp &&& 15#64 == 0#64) = true →
    ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F)),
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0 →
      ∀ (w0 w1 : BitVec 64), w0 ≠ DecodeState.none2Cap →
      ∀ (sf : State), ImgCallInv img sf →
        sf.pc = spqrSendEntry img.base + statesSendArmOffset st0 →
        sf.status = .Running → sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = x.ret → sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 → sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗ chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗ memRegion x.ret 72 ∗ A.pool ∗
            statesFromPbJumpTableAt img.base ∗ spqrSendStatesJumpTableAt img.base ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗
            (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗ spqrSendEncodeJumpTableAt img.base ∗
             spqrSendDropJumpTableAt img.base ∗ statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base)))
          (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
            (Pf ⊢ ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
                ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
              spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
              tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
              A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img))
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
              s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))

/-- Discharge `SpqrSendActiveContinuationPanic64` from `TripleRatchetHooks`, `SpqrHooks`,
    and `Obj.Loads libsignalSessionImage img`. -/
theorem spqrSendActiveContinuation_ok
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    SpqrSendActiveContinuationPanic64 img C A ctl K (tripleRatchetExterns C ctl abs) := by
  intro x s0 R hlen hrest_len hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hinvf
    hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  exact step_send_active_of_le_64
    (spqrSendContracts_of_hooks_and_remaining himg hTH hSH)
    (spqrSendExtraContracts_of_hooks himg hTH hSH)
    x s0 R hlen hrest_len hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hinvf
    hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf

/-- Discharge `SpqrSendActiveContinuationPanic64` on arbitrary `ext` from `SpqrSendContractsExt`
    and `SpqrSendExtraContracts`. -/
theorem spqrSendActiveContinuation_ok_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrSendContractsExt H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext) :
    SpqrSendActiveContinuationPanic64 img C A ctl K ext :=
  fun x s0 R hlen hrest_len hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hinvf
    hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf =>
    step_send_active_of_le_64_ext hC hE x s0 R hlen hrest_len hsp_align pq v1 st0
      hdec hinner hfrom w0 w1 hw0 sf hinvf hpcf hrunf hspf htrf
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf

/-- `spqrSendSpecT` with the `DEV-SPQR5` (`64 ≤ x.rest.length`) precondition conjunct. -/
def spqrSendSpecT64 (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall where
  pre x s := ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ TokenInit img ∗ (spqrSendSpec A ctl S img).pre x s
  post x s0 sf := TokenInit img ∗ (spqrSendSpec A ctl S img).post x s0 sf
  onPanic x s0 sf := (spqrSendSpec A ctl S img).onPanic x s0 sf

/-- `spqr::send::<HookRng>` (`0x3085c`) meets `spqrSendSpecT64 A ctl (spqrV1 C.F K) img`
    on `tripleRatchetProgAtExt img.base ext` given `SpqrSendContractsExt` and
    `SpqrSendActiveContinuationPanic64`. -/
theorem spqr_send_ok_ext_of_contractsExt_and_continuation_panic64
    {H_inner : V1InnerHeapPred}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendContractsExt H_inner img A ctl C K ext)
    (hcont : SpqrSendActiveContinuationPanic64 img C A ctl K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName)
      (spqrSendSpecT64 A ctl (spqrV1 C.F K) img) := by
  refine subroutine_ok_of_sepWPp_init fun x R s0 hpc hrun hpre hsp_align => ?_
  rw [fnAddr_spqrSend_eq] at hpc
  dsimp only [spqrSendSpecT64, spqrSendSpec, Spec.inImage] at hpre ⊢
  have hpre1 :
      s0.mem ⊨ ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        (⌜ImgCallInv img s0⌝ ∗
          (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.st.v⌝ ∗
            (TokenInit img ∗ logOff img ∗
              (x.st.at A ∗ memRegion x.ret 72 ∗ tapeAt ctl x.cur x.rest ∗
                A.pool ∗ stackAt s0.sp spqrSendStack ∗ R)))) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [ImgCallInv]; ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨⟨hlen, htape64⟩, hpre1⟩
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨hinv0, hpre2⟩
  rw [satisfies_pure_sepConj] at hpre2; rcases hpre2 with ⟨⟨hx0, hx1⟩, hmem0⟩
  have hmem_ro :
      s0.mem ⊨ spqrSendFullRoAt img ∗
        (x.st.at A ∗ memRegion x.ret 72 ∗ tapeAt ctl x.cur x.rest ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ R) :=
    rodata_spqrSendFullRoAt hC.loads hinv0.1 hmem0
  let Rest0 : SepProp :=
    tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitAt img.base ∗ logOff img ∗
    spqrSendEncodeJumpTableAt img.base ∗ spqrSendDropJumpTableAt img.base ∗
    statesIntoPbJumpTableAt img.base ∗ reduceTableAt img.base
  let P0 : SepProp :=
    stackAt s0.sp spqrSendStack ∗ x.st.at A ∗ memRegion x.ret 72 ∗ A.pool ∗
    Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ statesFromPbJumpTableAt img.base ∗
    spqrSendStatesJumpTableAt img.base ∗ Rest0
  have hP0 : s0.mem ⊨ P0 ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem_ro
    dsimp only [P0, Rest0, spqrSendFullRoAt, spqrSendRoAt]; ac_rfl
  let postGoal : State → SepProp → Prop := fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (Pf ⊢
      ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
      x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
      tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
      A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img)
  have hstep1 :
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0 P0
        postGoal
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
    refine spqr_send_phase1_step_panic (H_inner := H_inner) (F := C.F) (K := K)
      (φ_panic := (spqrV1 C.F K).sendPanics x.st.bytes x.rest)
      img A ext hC.base_aligned hC.h_inner_eq hC.alloc hC.decodeState_ok
      hC.statesFromPb_ok hC.dropProtoChain_ok s0 x.ret x.st hlen
      (Rest := Rest0) (Fr := R) (post := postGoal)
      hinv0 hsp_align hpc hrun hx0 hx1
      ?hdec_err ?hnone ?herr ?hok
    case hdec_err =>
      intro e hdec sf Pf _ _ hPf hspf hcsf htrf
      have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_spqrDecodeState_error (F := C.F) (K := K)
        (rest := x.rest) hdec
      refine ⟨hspf, hcsf, ?_⟩; rw [hsend, hdraws]
      refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
      have hsub :
          tapeAt ctl x.cur x.rest ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoAt, spqrSendRoAt]; ac_rfl
    case hnone =>
      intro pq hdec hinner sf Pf _ _ hPf hspf hcsf htrf
      have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_spqrDecodeState_inner_none (F := C.F) (K := K)
        (rest := x.rest) hdec hinner
      refine ⟨hspf, hcsf, ?_⟩; rw [hsend, hdraws]
      refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
      have hsub :
          tapeAt ctl x.cur x.rest ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret (some ([], none, [])) ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret (some ([], none, [])) ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoAt, spqrSendRoAt]; ac_rfl
    case herr =>
      intro pq v1 err hdec hinner hfrom sf Pf _ _ hPf hspf hcsf htrf
      have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_statesFromPb_error (F := C.F) (K := K)
        (rest := x.rest) hdec hinner hfrom
      refine ⟨hspf, hcsf, ?_⟩; rw [hsend, hdraws]
      refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
      have hsub :
          tapeAt ctl x.cur x.rest ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoAt img) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoAt, spqrSendRoAt]; ac_rfl
    case hok =>
      intro pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hinvf
        hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
      exact hcont x s0 R hlen htape64 hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hinvf
        hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  refine ⟨P0, hP0, fun R' hm' hL => ?_⟩
  rcases hstep1 R' hm' hL with
    ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmemf, hspf, hcsf, hPf⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Pf, hmemf, fun hmfR => ?_, hspf, hcsf⟩⟩
    have hmemf' : sf.mem ⊨
        spqrSendFullRoAt img ∗
        (⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
           ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
         x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
         tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
         A.pool ∗ stackAt s0.sp spqrSendStack ∗ R) := by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq ?_)) hmfR
      ac_rfl
    have hrestored := spqrSendFullRoAt_restore (img := img) hmemf'
    refine Satisfies.mono (Entails.of_eq ?_) hrestored
    ac_rfl
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- `spqr::send::<HookRng>` (`0x3085c`) meets `spqrSendSpecT64 A ctl (spqrV1 C.F K) img`
    on `tripleRatchetProgAtExt img.base ext` given `SpqrSendContracts` and
    `SpqrSendActiveContinuationPanic64`. -/
theorem spqr_send_ok_ext_of_contracts_and_continuation_panic64
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrSendContracts H_inner img A ctl C K ext)
    (hcont : SpqrSendActiveContinuationPanic64 img C A ctl K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName)
      (spqrSendSpecT64 A ctl (spqrV1 C.F K) img) :=
  spqr_send_ok_ext_of_contractsExt_and_continuation_panic64 hC.toExt hcont

/-- End-to-end `spqr::send::<HookRng>` (`0x3085c`) on `tripleRatchetProgAtExt img.base ext` from
    `SpqrSendContractsExt` and `SpqrSendExtraContracts`. -/
theorem spqr_send_ok_ext_of_contracts
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrSendContractsExt H_inner img A ctl C K ext)
    (hE : SpqrSendExtraContracts img A ctl C K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName)
      (spqrSendSpecT64 A ctl (spqrV1 C.F K) img) :=
  spqr_send_ok_ext_of_contractsExt_and_continuation_panic64 hC
    (spqrSendActiveContinuation_ok_ext hC hE)

/-- End-to-end `spqr::send::<HookRng>` (`0x3085c`) on arbitrary `ext` from `Stage2Contracts` and
    `HkdfToSliceSpqrOkExt`. -/
theorem spqr_send_ok_of_callees_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith C.F) ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hRng : HookSat ext rngFillName (rngFillSpec ctl))
    (hSH : SpqrHooks C A K ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img spqrSendName)
      (spqrSendSpecT64 A ctl (spqrV1 C.F K) img) :=
  root_of_tripleRatchetProgAtExt himg
    (spqr_send_ok_ext_of_contracts
      (spqrSendContractsExt_of_callees_and_remaining himg hC hhkdf hRO hZero hSH)
      (spqrSendExtraContracts_of_callees himg hC.toAllocContracts hRO hZero hRng hSH))

/-- End-to-end verification of `spqr::send::<HookRng>` (`0x3085c`) against `spqrSendSpecT64`
    (`DEV-SPQR5`). -/
theorem spqr_send_ok_of_dev_spqr5
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics (tripleRatchetExterns C ctl abs)))
      (entryOf img spqrSendName)
      (spqrSendSpecT64 A ctl (spqrV1 C.F K) img) :=
  root_of_tripleRatchetProgAtExt himg
    (spqr_send_ok_ext_of_contracts_and_continuation_panic64
      (spqrSendContracts_of_hooks_and_remaining himg hTH hSH)
      (spqrSendActiveContinuation_ok himg hTH hSH))

/-- End-to-end `spqr::send::<HookRng>` (`0x3085c`) verification (`SpqrSendV1Stmt`). -/
theorem spqr_send_ok
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrSendV1Stmt C A ctl K abs img :=
  spqr_send_ok_of_dev_spqr5 C A ctl K abs img

end CryptoVerification.SpqrV1.Top.Send
