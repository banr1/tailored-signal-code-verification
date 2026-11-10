/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegionsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Relocatable End-to-End Verification of `spqr::send::<HookRng>` (Block 124)

Composes relocatable Phase 1 (`FinalPlaced.lean`), Phase 2 (`StatesSendDispatchPlaced.lean`),
and Phases 3–4 (`TopPhase3Placed.lean`) to verify `spqr::send::<libsignal_session::HookRng>`
against `spqrSendPlacedSpecT64` (`DEV-SPQR5`).
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
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-- Additional hook and callee contracts used by relocatable Phase 2 (`States::send`) and Phase 3
    (`drop_in_place::<chunked::States>`) alongside `SpqrSendPlacedContracts`. -/
structure SpqrSendExtraContractsPlaced
    (A : RustAlloc) (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  panic_hook : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked
  panicSubOverflow_hook :
    ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" =
      some Rust.panicked
  unwrapFailed_hook : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked
  allocZeroed_hook : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A)
  rngFill_hook : HookSat (Rust.withPanics ext) rngFillName (rngFillSpec ctl)
  mlkemFromSeed_hook : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (mlkemFromSeedSpec K)
  mlkemPk1_hook : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym mlkemPk1Spec
  mlkemPk2_hook : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym mlkemPk2Spec
  mlkemEncaps1_hook : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (mlkemEncaps1Spec K)
  fromSeed_pk1_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList
  fromSeed_pk2_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList
  macHdrPinned_ok : AuthMacHdrPinnedPlacedOkX C.F A ext
  doReserve2_ok : DoReserve2PlacedOkX A ext
  dropChainEpochSlice_raw_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 143)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A))
  dropChunkedStates_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 140)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec A C.F))

/-- Convert `Top.Recv.statesIntoPbPlacedSpecX` (which explicitly includes
    `statesIntoPbJumpTablePlacedAt` in pre/post) to `statesIntoPbPlacedSpecX`
    (which extracts it from `LibsignalCodeRoLoaded lsmpl`). -/
private theorem statesIntoPb_placed_ok_of_recv
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (Top.Recv.statesIntoPbPlacedSpecX A F))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hfr, hpre⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (Top.Recv.statesIntoPbPlacedSpecX A F)).pre x s0 ∗ R := by
    have hro := lsro_statesIntoPbJumpTablePlacedAt hfr.2 hpre
    dsimp only [withLsCodeRoLoaded, Top.Recv.statesIntoPbPlacedSpecX,
      Top.Recv.statesIntoPbJumpTablePlacedAt,
      statesIntoPbPlacedSpecX,
      statesIntoPbJumpTablePlacedAt] at hro ⊢
    refine Satisfies.mono (Entails.trans (Entails.pure_right hfr (Entails.refl _)) (Entails.of_eq ?_)) hro
    ac_rfl
  refine hok.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Top.Recv.statesIntoPbPlacedSpecX,
      Top.Recv.statesIntoPbJumpTablePlacedAt,
      statesIntoPbPlacedSpecX,
      statesIntoPbJumpTablePlacedAt] at hq ⊢
    have hq' : sf.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
        ((⌜sf.trace = s0.trace⌝ ∗
          Drop.optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
          memRegion x.stA chunkedStatesSize ∗
          A.pool ∗ stackAt s0.sp statesIntoPbStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by dsimp only [statesIntoPbJumpTablePlacedAt]; ac_rfl)) hq
    exact Satisfies.of_sep_right hq'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

set_option maxHeartbeats 800000 in
/-- Full active V1 continuation (`spqrSendPlacedEntry + statesSendArmOffset st0 -> s0.readReg64 .x30`)
    whenever `st0.send K x.rest = .ok (sOut, rest')`. -/
theorem step_send_active_of_statesSend_ok_placed
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext)
    (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi C.F)) (rest' : Bytes)
    (hdec : spqrDecodeState x.st.bytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (hsend0 : st0.send K x.rest = .ok (sOut, rest'))
    (w0 w1 : BitVec 64) (_hw0 : w0 ≠ DecodeState.none2Cap)
    (sf : State) (hcrlf : LibsignalCodeRoLoaded lsmpl sf.mem)
    (hpcf : sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 0x1f80#64)
    (htrf : sf.trace = s0.trace)
    (hx19 : sf.readReg64 .x19 = x.ret)
    (hx20 : sf.readReg64 .x20 = chunkedStatesWord0 st0)
    (_hx21 : sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (_hx23 : sf.readReg64 .x23 = w0)
    (hx24 : sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64)
    (hx25 : sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64)
    (hx26 : sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx28 : sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64)
    (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢
          ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt))
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
    Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
    x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt
  let FrameArm : SepProp :=
    ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) pq.versionNegotiation ∗
    memRegion x.ret 72 ∗
    (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
     memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
     memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
    spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
    spqrSendEncodeJumpTablePlacedAt ∗ States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ RestTail
  have hpre_arm :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        GF.Mul2U16.tokenInitPlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt ∗
        spqrLogLevelZeroPlacedAt ∗ tapeAt ctl x.cur x.rest ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
        memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
        memRegion (sp + 0x590#64) 920 ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        statesSendPreArmScratch sp) ∗ FrameArm := by
    have hvn := optVN_30_to_proto A sp w0 w1 pq.versionNegotiation
    have hreg := pre_309cc_regions_eq sp
    dsimp only [FrameArm, RestTail]
    refine Entails.trans (Entails.of_eq (show _ =
      (((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation) ∗
      (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        GF.Mul2U16.tokenInitPlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt ∗
        spqrLogLevelZeroPlacedAt ∗ tapeAt ctl x.cur x.rest ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion x.ret 72 ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
        Top.Recv.statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
        x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hvn) ?_
    rw [hreg]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_arm ?_
  let mid3196 := spqrSendPlacedEntry + 3196#64
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
      GF.Mul2U16.tokenInitPlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ FrameArm
  let post3196 : State → SepProp → Prop := fun sm Pm =>
    LibsignalCodeRoLoaded lsmpl sm.mem ∧ sm.sp = sp ∧ sm.trace = sf.trace ∧
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
  have hphase2 :
      SepWPp (spqrSendPlacedProg ext) mid3196 sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗
          GF.Mul2U16.tokenInitPlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ tapeAt ctl x.cur x.rest ∗
          ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
          memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          memRegion (sp + 0x590#64) 920 ∗
          chunkedStatesAt A (sp + 0x950#64) st0 ∗
          statesSendPreArmScratch sp) ∗ FrameArm)
        post3196
        (fun s_pan P_f => (s_pan.mem ⊨ P_f ∗ R) →
          (s_pan.mem ⊨ (⌜allocFailedIn sf s_pan ∧ sf.trace <+: s_pan.trace⌝ ∗ anyHeap) ∗ R)) := by
    refine step_send_statesSend_placed (ctl := ctl) A ext hC.alloc
      hE.allocZeroed_hook hE.rngFill_hook hE.mlkemFromSeed_hook hE.mlkemPk1_hook hE.mlkemPk2_hook
      hE.mlkemEncaps1_hook hE.fromSeed_pk1_slice hE.fromSeed_pk2_slice
      hE.macHdrPinned_ok hE.doReserve2_ok hC.encodeBytes_ok hC.polyNextChunk_ok hC.hkdfToVec_ok hC.authUpdate_ok
      hC.headerSentSendEkChunk_ok hC.ct1ReceivedSendEkChunk_ok hC.ct1SampledSendCt1Chunk_ok
      hC.ct2SampledSendCt2Chunk_ok hC.ekReceivedCt1SampledSendCt1Chunk_ok
      (s0 := sf) (s := sf) sp x.cur x.rest rest' pq.chain st0 sOut hroot_len hsend0
      hcrlf hpcf hrunf hspf hfsp_align rfl rfl hx20 hx24 hx25 hx26 hx28 rfl rfl rfl ?_
    intro sm hcrl_m hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx22_m hx25_m hx26_m hx28_m hx23_none_m hpstate_m hvregs_m
    exact SepWPp.done hpc_m hrun_m
      ⟨hcrl_m, hsp_m, htr_m, hx19_m, hx20_m, hx22_m, hx25_m, hx26_m, hx28_m, hx23_none_m, hpstate_m, hvregs_m, rfl⟩
  refine sepWPp_bind_weaken_panic hphase2 ?_ ?_
  · intro s_pan P_f hqp hm
    have hm' := hqp hm
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono fun h => ?_))) hm'
    rcases (allocFailedIn_of_trace_eq htrf).mp h with ⟨ha, htr_p⟩
    exact ⟨Or.inl ha, htr_p⟩
  · rintro sm Pm hpc_m hrun_m
      ⟨hcrl_m, hsp_m, htr_m, hx19_m, _, hx22_m, hx25_m, hx26_m, hx28_m, hx23_none_m, hpstate_m, hvregs_m, rfl⟩
    rw [htrf] at htr_m
    rw [hx19] at hx19_m
    rw [hx28] at hx28_m
    let Rest314d8 : SepProp :=
      tapeAfter ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      GF.Mul2U16.tokenInitPlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ RestTail
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
          spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗ States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
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
              spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
          dsimp only [P3196, FrameArm, Rest314d8]; ac_rfl
        _ = _ := by rw [hreg]; ac_rfl
    rw [hP3196_eq]
    refine step_send_from_314d8_placed hC.alloc hE.panic_hook hE.panicSubOverflow_hook
      hE.dropChainEpochSlice_raw_ok hE.dropChunkedStates_ok hC.chainFromPb_ok hC.chainFromVn_ok
      hC.chainAddEpoch_ok hC.chainSendKey_ok hC.chainIntoPb_ok hC.messageSerialize_ok
      (statesIntoPb_placed_ok_of_recv hC.statesIntoPb_ok) s0 sm sp x.ret (sm.readReg64 .x21) (sm.readReg64 .x27) (sm.readReg64 .x23)
      pq sOut Rest314d8 R _ hsp_align rfl hchain_raw hpq'_len hcrl_m
      hpc_m hrun_m hsp_m htr_m hx19_m rfl hx22_m rfl hx25_m hx26_m rfl hx28_m hx23_none_m hpstate_m
      ?hφ ?herr ?hok (hvregs_m.trans hvregsf)
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
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      exact Entails.of_eq (by ac_rfl)
    case hok =>
      intro idx msgKey chainPb salt hch hsalt sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_ok hdec hinner hfrom hsend0 hch hsalt
      refine ⟨hsp_f, hcs_f, ?_⟩
      rw [hsend_eq, hdraws_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Full active V1 continuation (`spqrSendPlacedEntry + statesSendArmOffset st0 -> s0.readReg64 .x30`)
    for all 11 arms of `st0` under `64 ≤ x.rest.length` (`DEV-SPQR5`). -/
theorem step_send_active_of_le_64_placed
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext)
    (x : SendCall) (s0 : State) (R : SepProp)
    (hlen : x.st.bytes.length < 2 ^ 32)
    (hrest_len : 64 ≤ x.rest.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F))
    (hdec : spqrDecodeState x.st.bytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0)
    (w0 w1 : BitVec 64) (hw0 : w0 ≠ DecodeState.none2Cap)
    (sf : State) (hcrlf : LibsignalCodeRoLoaded lsmpl sf.mem)
    (hpcf : sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
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
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
      ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢
          ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt))
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
      memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
     (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt))
  have hpull_valid :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
      ⌜statesPolyEncoderValid st0⌝ ∗
      ((stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A (sp + 0x950#64) st0 ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt))) := by
    have hv0 := chunkedStatesAt_entails_polyEncoderValid A (sp + 0x950#64) st0
    refine Entails.trans (Entails.of_eq (show _ = chunkedStatesAt A (sp + 0x950#64) st0 ∗ RestPre by
      dsimp only [RestPre]; ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hv0) ?_
    exact Entails.of_eq (by dsimp only [RestPre]; ac_rfl)
  refine SepWPp.weaken_pre hpull_valid (ProofLib.SepWPp.pure_elim fun hv => ?_)
  rcases statesSend_ok_or_headerReceived_encaps1_of_le_64 K hlen hrest_len hdec hinner hfrom hv with
    ⟨sOut, rest', hsend0⟩ | ⟨st, rfl, hencaps, hsend_err⟩
  · exact step_send_active_of_statesSend_ok_placed hC hE x s0 R hlen hsp_align pq v1 st0 sOut rest'
      hdec hinner hfrom hsend0 w0 w1 hw0 sf hcrlf hpcf hrunf hspf htrf
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  · have hfsp_align : (sp &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp_align (by decide)
    have hpan : (spqrV1 C.F K).sendPanics x.st.bytes x.rest :=
      sendPanics_of_statesSend_panic hdec hinner hfrom hsend_err
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
      memRegion x.ret 72 ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
      x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
      States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt
    have hpre_pan :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          ProtoRepr.optChainPBAt A (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
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
              memRegion x.ret 72 ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
              spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
              x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
              GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
              States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt) := by ac_rfl
        _ = _ := by dsimp only [FramePan]; rw [hreg]; ac_rfl
    refine SepWPp.weaken_pre hpre_pan ?_
    refine sepWPp_mono_post (fun _ _ hq => hq) (fun s_pan P_f hqp hm => ?_)
      (step_send_arm_headerReceived_encaps1_none_placed (R := R) (Frame := FramePan)
        hC.alloc hE.allocZeroed_hook hE.rngFill_hook hE.mlkemEncaps1_hook hE.unwrapFailed_hook
        sp x.cur x.rest (by omega) st hencaps hpan hcrlf hpcf hrunf hspf hfsp_align
        htrf hx24 hx26 hx28 rfl)
    have hm' := hqp hm
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono fun ⟨hp, htr_p⟩ => ?_))) hm'
    exact ⟨hp.symm, htr_p⟩

/-- Relocatable active Phase 2 + Phase 3 continuation obligation under `DEV-SPQR5` (`64 ≤ x.rest.length`). -/
def SpqrSendActiveContinuationPanic64Placed
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (x : SendCall) (s0 : State) (R : SepProp),
    x.st.bytes.length < 2 ^ 32 →
    64 ≤ x.rest.length →
    (s0.sp &&& 15#64 == 0#64) = true →
    ∀ (pq : PqRatchetState) (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi C.F)),
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st0 →
      ∀ (w0 w1 : BitVec 64), w0 ≠ DecodeState.none2Cap →
      ∀ (sf : State),
        LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = x.ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion x.ret 72 ∗ A.pool ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (x.st.at A ∗ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
            (tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
             spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
             States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt)))
          (fun sf Pf =>
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
            (Pf ⊢
              ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
                ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
              x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
              tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
              A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt))
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
              s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))

/-- Discharge `SpqrSendActiveContinuationPanic64Placed` from `SpqrSendPlacedContracts` and
    `SpqrSendExtraContractsPlaced`. -/
theorem spqrSendActiveContinuation_placed_ok
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext) :
    SpqrSendActiveContinuationPanic64Placed C A ctl K ext := by
  intro x s0 R hlen hrest_len hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hcrlf
    hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  exact step_send_active_of_le_64_placed hC hE x s0 R hlen hrest_len hsp_align pq v1 st0
    hdec hinner hfrom w0 w1 hw0 sf hcrlf hpcf hrunf hspf htrf
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf

/-- Relocatable `[LibsignalPlacement]` contract for `spqr::send::<HookRng>` (`Block 124`). -/
def spqrSendPlacedSpec (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) : Spec SendCall :=
  withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗
        spqrLogLevelZeroPlacedAt ∗
        x.st.at A ∗ memRegion x.ret 72 ∗ tapeAt ctl x.cur x.rest ∗
        A.pool ∗ stackAt s.sp spqrSendStack
      post := fun x s0 sf =>
        ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
          ¬ S.sendPanics x.st.bytes x.rest⌝ ∗
        x.st.at A ∗ spqrSendResultAt A x.ret (S.send x.st.bytes x.rest) ∗
        tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
        spqrLogLevelZeroPlacedAt ∗ A.pool ∗ stackAt s0.sp spqrSendStack
      onPanic := fun x s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.sendPanics x.st.bytes x.rest) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-- `spqrSendPlacedSpec` with `GF.Mul2U16.tokenInitPlacedAt` and the `DEV-SPQR5`
    (`x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length`) precondition conjunct. -/
def spqrSendPlacedSpecT64 (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) :
    Spec SendCall where
  pre x s :=
    ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
    GF.Mul2U16.tokenInitPlacedAt ∗ (spqrSendPlacedSpec A ctl S).pre x s
  post x s0 sf :=
    GF.Mul2U16.tokenInitPlacedAt ∗ (spqrSendPlacedSpec A ctl S).post x s0 sf
  onPanic x s0 sf :=
    (spqrSendPlacedSpec A ctl S).onPanic x s0 sf

/-- `spqr::send::<HookRng>` (Block `124`) meets `spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)`
    on `spqrSendPlacedProg ext` given `SpqrSendPlacedContracts` and
    `SpqrSendActiveContinuationPanic64Placed`. -/
theorem spqr_send_placed_ok_ext_of_contracts_and_continuation_panic64
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hcont : SpqrSendActiveContinuationPanic64Placed C A ctl K ext) :
    subroutine_ok (spqrSendPlacedProg ext) spqrSendPlacedEntry
      (spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)) := by
  refine subroutine_ok_of_sepWPp_init fun x R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [spqrSendPlacedSpecT64, spqrSendPlacedSpec, withLsCodeRoLoaded] at hpre ⊢
  have hpre1 :
      s0.mem ⊨ ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.st.v⌝ ∗
            (GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              (x.st.at A ∗ memRegion x.ret 72 ∗ tapeAt ctl x.cur x.rest ∗
                A.pool ∗ stackAt s0.sp spqrSendStack ∗ R)))) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨⟨hlen, htape64⟩, hpre1⟩
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨hcrl0, hpre2⟩
  rw [satisfies_pure_sepConj] at hpre2; rcases hpre2 with ⟨⟨hx0, hx1⟩, hmem0⟩
  have hmem_ro :
      s0.mem ⊨ spqrSendFullRoPlacedAt ∗
        (x.st.at A ∗ memRegion x.ret 72 ∗ tapeAt ctl x.cur x.rest ∗
          A.pool ∗ stackAt s0.sp spqrSendStack ∗ R) :=
    lsro_spqrSendFullRoPlacedAt hcrl0.2 hmem0
  let Rest0 : SepProp :=
    tapeAt ctl x.cur x.rest ∗ GF.Mul2U16.tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
    spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
    States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ GF.UnacceleratedMul.reduceTablePlacedAt
  let P0 : SepProp :=
    stackAt s0.sp spqrSendStack ∗ x.st.at A ∗ memRegion x.ret 72 ∗ A.pool ∗
    Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ Top.Recv.statesFromPbJumpTablePlacedAt ∗
    spqrSendStatesJumpTablePlacedAt ∗ Rest0
  have hP0 : s0.mem ⊨ P0 ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem_ro
    dsimp only [P0, Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; ac_rfl
  let postGoal : State → SepProp → Prop := fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (Pf ⊢
      ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
      x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
      tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
      A.pool ∗ stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt)
  have hstep1 :
      SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0 P0
        postGoal
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ (spqrV1 C.F K).sendPanics x.st.bytes x.rest) ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
    refine spqr_send_phase1_step_placed_panic (H_inner := H_inner) (F := C.F) (K := K)
      (φ_panic := (spqrV1 C.F K).sendPanics x.st.bytes x.rest)
      A ext hC.h_inner_eq hC.alloc hC.decodeState_ok
      hC.statesFromPb_ok hC.dropProtoChain_ok s0 x.ret x.st hlen
      (Rest := Rest0) (Fr := R) (post := postGoal)
      hcrl0 hsp_align hpc hrun hx0 hx1
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
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; ac_rfl
    case hnone =>
      intro pq hdec hinner sf Pf _ _ hPf hspf hcsf htrf
      have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_spqrDecodeState_inner_none (F := C.F) (K := K)
        (rest := x.rest) hdec hinner
      refine ⟨hspf, hcsf, ?_⟩; rw [hsend, hdraws]
      refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
      have hsub :
          tapeAt ctl x.cur x.rest ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret (some ([], none, [])) ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret (some ([], none, [])) ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; ac_rfl
    case herr =>
      intro pq v1 err hdec hinner hfrom sf Pf _ _ hPf hspf hcsf htrf
      have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_statesFromPb_error (F := C.F) (K := K)
        (rest := x.rest) hdec hinner hfrom
      refine ⟨hspf, hcsf, ?_⟩; rw [hsend, hdraws]
      refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
      have hsub :
          tapeAt ctl x.cur x.rest ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
          tapeAfter ctl x.cur x.rest 0 ∗
            (x.st.at A ∗ spqrSendResultAt A x.ret none ∗ A.pool ∗
             stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
        sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)
      refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by ac_rfl)))
      dsimp only [Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; ac_rfl
    case hok =>
      intro pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hcrlf
        hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
      exact hcont x s0 R hlen htape64 hsp_align pq v1 st0 hdec hinner hfrom w0 w1 hw0 sf hcrlf
        hpcf hrunf hspf htrf hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  refine ⟨P0, hP0, fun R' hm' hL => ?_⟩
  rcases hstep1 R' hm' hL with
    ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmemf, hspf, hcsf, hPf⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Pf, hmemf, fun hmfR => ?_, hspf, hcsf⟩⟩
    have hmemf' : sf.mem ⊨
        spqrSendFullRoPlacedAt ∗
        (⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
           ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
         x.st.at A ∗ spqrSendResultAt A x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
         tapeAfter ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
         A.pool ∗ stackAt s0.sp spqrSendStack ∗ R) := by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq ?_)) hmfR
      ac_rfl
    have hrestored := spqrSendFullRoPlacedAt_restore hmemf'
    refine Satisfies.mono (Entails.of_eq ?_) hrestored
    ac_rfl
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- `spqr::send::<HookRng>` (Block `124`) meets `spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)`
    on `spqrSendPlacedProg ext` from `SpqrSendPlacedContracts` and `SpqrSendExtraContractsPlaced`. -/
theorem spqr_send_placed_ok_of_contracts
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext) :
    subroutine_ok (spqrSendPlacedProg ext) spqrSendPlacedEntry
      (spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)) :=
  spqr_send_placed_ok_ext_of_contracts_and_continuation_panic64 hC
    (spqrSendActiveContinuation_placed_ok hC hE)

theorem spqr_send_placed_ok_blockProgram_of_contracts
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 124 (Rust.withPanics ext))
      (lsmpl.base 124)
      (spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)) := by
  have hok := spqr_send_placed_ok_of_contracts hC hE
  rwa [← IsLsBlockProg.eq_blockProgram (prog := spqrSendPlacedProg ext)]

/-- Direct `libsignalSessionLib.blockProgram lsmpl 124 ext` form of
    `spqr_send_placed_ok_blockProgram_of_contracts` when `ext` already maps all
    `Rust.isPanicSymbol` symbols to `some Rust.panicked`. -/
theorem spqr_send_placed_ok_blockProgram_ext_of_contracts
    {H_inner : V1InnerHeapPred}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrSendPlacedContracts H_inner A ctl C K ext)
    (hE : SpqrSendExtraContractsPlaced A ctl C K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 124 ext)
      (lsmpl.base 124)
      (spqrSendPlacedSpecT64 A ctl (spqrV1 C.F K)) := by
  have heq : Rust.withPanics ext = ext := by
    funext sym; unfold Rust.withPanics; split
    · next h => exact (hp sym h).symm
    · rfl
  simpa only [heq] using spqr_send_placed_ok_blockProgram_of_contracts hC hE

end CryptoVerification.SpqrV1.Top.Send
