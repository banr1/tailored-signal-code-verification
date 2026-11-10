/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlaced
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Envelope Bridges, Exits, & Tag Dispatch for `spqr::decode_state` (Block `325`)

Proves `DecodeStateLoopEnv` and polynomial-capacity preservation bridges across `V1State::merge`,
the empty-input fast path (`+1604..+1624`) and post-loop success exit (`+1676..+1724`), and
outer-loop tag dispatch (`+160`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost IsDropSuffix SkipFieldGhost sliceCursorAfter)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound V1StateMergeGhost codecWireTypeToProto mergeLoopBin
   optPolyDecoderPtsLen optPolyEncoderPolysLen optPolyEncoderPtsLen
   proto_decodeKey_suffix proto_decodeVarint_suffix
   proto_mergeMessage_len_le proto_skipField_suffix
   v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB GrowOneCall PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (DecodeErr mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateResultAt decodeStateSavedAt frame_4chunks_to_1296
   head16_tail336_entails_protoPqRatchetStateAt lower_352_fold none2Cap none3Cap
   optProtoPqRatchetInnerAt pqRatchetState_default_eq
   pqRatchetState_mergeField_other pqRatchetState_mergeField_tag1 pqRatchetState_mergeField_tag2
   pqRatchetState_mergeField_tag3 protoPqRatchetStateAt protoPqRatchetStateAt_entails_head16_tail336
   protoPqRatchetStateCapOkAt relocProtoPqRatchetStateTailAt scratch_688_fold_48
   sp_sub_1392_aligned spqrDecodeState_nil spqrDecodeState_toOption_eq_mergeLoopBin
   stackAt_of_callee stackAt_to_callee tag_cmp32_of_gt tag_setWidth32_ofNat)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv withVmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneVecU8Env RawVecGrowEnv rawVecGrowEvents rawVecNewCap)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env skipField3EventsCore)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (GrowOneStrideEnv growOneStrideEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv bytesMergeEventsCore)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (BytesMerge3EnvCore DecodeErrorPushMergeEnv SpqrMergeLoopEnv SpqrMergeSmallStep
   mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv innerStatePolyCapMax optInnerStatePolyCapBound
   optInnerStatePolyCapBound_mono_len optInnerStatePolyCapMax v1StateMergePostEnv_imp_pre)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (ct1AcknowledgedPolyCapBound_le ct1ReceivedPolyCapBound_le ct1SampledPolyCapBound_le
   ct2SampledPolyCapBound_le ekReceivedCt1SampledPolyCapBound_le ekSentCt1ReceivedPolyCapBound_le
   headerReceivedPolyCapBound_le headerSentPolyCapBound_le keysSampledPolyCapBound_le
   noHeaderReceivedPolyCapBound_le optInnerStatePolyCapBound_ge_len
   optInnerStatePolyCapBound_of_ct1Acknowledged optInnerStatePolyCapBound_of_ct1Received
   optInnerStatePolyCapBound_of_ct1Sampled optInnerStatePolyCapBound_of_ct2Sampled
   optInnerStatePolyCapBound_of_ekReceivedCt1Sampled optInnerStatePolyCapBound_of_ekSentCt1Received
   optInnerStatePolyCapBound_of_headerReceived optInnerStatePolyCapBound_of_headerSent
   optInnerStatePolyCapBound_of_keysSampled optInnerStatePolyCapBound_of_keysUnsampled
   optInnerStatePolyCapBound_of_noHeaderReceived)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.FitsEnv
  (decodeStateLoop_head decodeStateLoop_mono decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv decodeState_epilogue_53e60_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (decodeStateErrFramePlaced fitsEnv_decodeErrorPush_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget
  (decodeState_outer_skip_53664_placed_ofEnv decodeState_v1_entry_535d4_placed_ofEnv
   pqRatchetStateV1MsgPtr pqRatchetStateV1OrDefault)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget
  (decodeState_chain_entry_53590_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
  (bytesMerge3Det_of_contractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudget
  (decodeState_vn_entry_53554_placed_ofEnv)

private def protoWireTypeToCodec : CryptoVerification.LibsignalSpqrV1.Proto.WireType → WireType
  | .varint => .varint
  | .SixtyFourBit => .sixtyFourBit
  | .lengthDelimited => .lengthDelimited
  | .startGroup => .startGroup
  | .endGroup => .endGroup
  | .ThirtyTwoBit => .thirtyTwoBit

private theorem codecWireTypeToProto_protoWireTypeToCodec
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    codecWireTypeToProto (protoWireTypeToCodec wt) = wt := by
  cases wt <;> rfl

/-! ## 1. Pure Envelope & `optInnerStatePolyCapBound` Bridges -/

theorem decodeErrorPushMergeEnv_imp_pushEnv {n : Nat} {evs : List AllocEvent}
    (hn : n ≤ 4) (h : DecodeErrorPushMergeEnv n evs) :
    DecodeErrorPushEnv n evs := by
  unfold DecodeErrorPushMergeEnv at h
  unfold DecodeErrorPushEnv
  rcases h with rfl | ⟨hn0, rfl⟩ | ⟨hpos, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨hn0, 4, by decide, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨n, Nat.max (2 * n) 4, hpos, Nat.le_refl n,
      by simp only [Nat.max_def]; split <;> omega,
      by simp only [Nat.max_def]; split <;> omega, rfl⟩)

theorem growOneVecU8Env_imp_stride {g : GrowOneCall} {evs : List AllocEvent}
    (h : GrowOneVecU8Env g evs) :
    GrowOneStrideEnv g.cap 24 8 evs := by
  unfold GrowOneVecU8Env RawVecGrowEnv rawVecNewCap at h
  unfold GrowOneStrideEnv growOneStrideEvents
  rcases h with ⟨hc0, rfl⟩ | ⟨hcne, rfl⟩
  · simp only [hc0, ↓reduceIte]
  · simp only [hcne, ↓reduceIte]

theorem spqrMergeSmallStep_to_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : SpqrMergeSmallStep polyCapBound evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  cases h with
  | nil => exact .nil
  | deallocs hf => exact .deallocs hf
  | fromErr => exact .fromErr
  | pushErr hn hp => exact .pushErr hn (decodeErrorPushMergeEnv_imp_pushEnv hn hp)
  | bytesMergeErr wt valCap bs hm hb =>
    dsimp only [BytesMerge3EnvCore] at hb
    subst hb
    have hnil : mergeBytes wt [] = none := by cases wt <;> rfl
    have heq : bytesMergeEventsCore wt valCap bs = bytesMergeEventsCore wt 0#64 [] := by
      dsimp only [bytesMergeEventsCore]
      rw [hm, hnil]
    rw [heq]
    exact .bytesMerge wt 0#64 [] (Nat.zero_le _) (Nat.zero_le _)
  | growVecU8 g hcap hg =>
    exact .growPolyElem g.cap hcap (growOneVecU8Env_imp_stride hg)

theorem spqrMergeLoopEnv_to_decodeStateLoopEnv {fuel maxLen polyCapBound : Nat}
    {evs : List AllocEvent}
    (h : SpqrMergeLoopEnv fuel maxLen polyCapBound evs) (hmax : maxLen < 2 ^ 64) :
    DecodeStateLoopEnv fuel maxLen polyCapBound evs := by
  revert hmax
  induction h with
  | nil => intro _; exact .nil
  | step h1 _ ih =>
    intro hmax'
    exact .step (spqrMergeSmallStep_to_iter h1) (ih hmax')
  | @bytesStep fuel' maxLen' poly' wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    intro hmax'
    let g : BytesMergeGhost := ⟨wt, 0#64, valCap, 0#64, bs, 0#64, 0#64, 0#64, bs⟩
    have hbm : BytesMergeEnv g _ := hb
    have h1 := DecodeStateIterEnv.of_bytesMergeEnv (polyCapBound := poly') (x := g) hbs hmax'
      (fun v' r' hm' => by
        dsimp only [g] at hm'
        have := mergeBytes_len_bound hm'
        omega) hbm
    have hstep := DecodeStateLoopEnv.step h1 (ih hmax')
    exact hstep.mono_fuel (by omega)

theorem skipField3Env_ok_nil {iwt : WireType} {itag depth : Nat}
    {bufRef slot ptr : BitVec 64} {bs rest : List (BitVec 8)} {evs : List AllocEvent}
    (hsf : skipField (2 * bs.length + 2) depth itag iwt bs = some rest)
    (h : SkipField3Env ⟨iwt, itag, depth, bufRef, slot, ptr, bs⟩ evs) :
    evs = [] := by
  dsimp only [SkipField3Env, skipField3EventsCore] at h
  rw [hsf] at h
  exact h

private theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ite_true_branch {c : Prop} [Decidable c] {α : Type} {t e : α} (hc : c) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

private theorem ite_false_branch {c : Prop} [Decidable c] {α : Type} {t e : α} (hc : ¬ c) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

private theorem mergeFieldsLoop_v1State_polyCap (fuel : Nat) :
    ∀ {m m' : V1State} {s : List (BitVec 8)},
      CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop V1State.mergeField fuel m s 99 = .ok m' →
      optInnerStatePolyCapMax m'.innerState ≤ optInnerStatePolyCapMax m.innerState + s.length := by
  induction fuel with
  | zero =>
    intro m m' s h
    cases s with
    | nil => cases h; omega
    | cons _ _ => nomatch h
  | succ fuel ih =>
    intro m m' s h
    cases s with
    | nil => cases h; omega
    | cons b tl =>
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop, Bind.bind, Except.bind] at h
      rcases hdk : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, r1⟩
      · rw [hdk] at h; nomatch h
      · rw [hdk] at h; dsimp only at h
        have hlt1 : r1.length < (b :: tl).length :=
          (proto_decodeKey_suffix (by rw [hdk]; rfl)).1
        rcases hmf : V1State.mergeField m tag wt r1 99 with _ | ⟨m1, r2⟩
        · rw [hmf] at h; nomatch h
        · rw [hmf] at h; dsimp only at h
          have hs : optInnerStatePolyCapMax m1.innerState + r2.length ≤
              optInnerStatePolyCapMax m.innerState + r1.length := by
            let iwt := protoWireTypeToCodec wt
            have hiwt : codecWireTypeToProto iwt = wt := codecWireTypeToProto_protoWireTypeToCodec wt
            unfold V1State.mergeField at hmf
            by_cases htr : (tag ≥ 1#32 && tag ≤ 11#32) = true
            · rw [ite_true_branch htr] at hmf
              obtain ⟨⟨is', r_is⟩, hm_is, h2_is⟩ := bind_ok_inv hmf; cases h2_is
              change optInnerStatePolyCapMax is' + r2.length ≤ optInnerStatePolyCapMax m.innerState + r1.length
              unfold V1State.InnerState.merge at hm_is
              by_cases ht1 : (tag == 1#32) = true
              · rw [ite_true_branch ht1] at hm_is
                obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                have hb := optInnerStatePolyCapBound_of_keysUnsampled (by rw [h1]; rfl)
                unfold optInnerStatePolyCapBound at hb; omega
              · rw [ite_false_branch ht1] at hm_is
                by_cases ht2 : (tag == 2#32) = true
                · rw [ite_true_branch ht2] at hm_is
                  obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                  have hb := optInnerStatePolyCapBound_of_keysSampled (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                  have hle := keysSampledPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                  unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                · rw [ite_false_branch ht2] at hm_is
                  by_cases ht3 : (tag == 3#32) = true
                  · rw [ite_true_branch ht3] at hm_is
                    obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                    have hb := optInnerStatePolyCapBound_of_headerSent (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                    have hle := headerSentPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                    unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                  · rw [ite_false_branch ht3] at hm_is
                    by_cases ht4 : (tag == 4#32) = true
                    · rw [ite_true_branch ht4] at hm_is
                      obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                      have hb := optInnerStatePolyCapBound_of_ct1Received (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                      have hle := ct1ReceivedPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                      unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                    · rw [ite_false_branch ht4] at hm_is
                      by_cases ht5 : (tag == 5#32) = true
                      · rw [ite_true_branch ht5] at hm_is
                        obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                        have hb := optInnerStatePolyCapBound_of_ekSentCt1Received (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                        have hle := ekSentCt1ReceivedPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                        unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                      · rw [ite_false_branch ht5] at hm_is
                        by_cases ht6 : (tag == 6#32) = true
                        · rw [ite_true_branch ht6] at hm_is
                          obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                          have hb := optInnerStatePolyCapBound_of_noHeaderReceived (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                          have hle := noHeaderReceivedPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                          unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                        · rw [ite_false_branch ht6] at hm_is
                          by_cases ht7 : (tag == 7#32) = true
                          · rw [ite_true_branch ht7] at hm_is
                            obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                            have hb := optInnerStatePolyCapBound_of_headerReceived (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                            have hle := headerReceivedPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                            unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                          · rw [ite_false_branch ht7] at hm_is
                            by_cases ht8 : (tag == 8#32) = true
                            · rw [ite_true_branch ht8] at hm_is
                              obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                              have hb := optInnerStatePolyCapBound_of_ct1Sampled (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                              have hle := ct1SampledPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                              unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                            · rw [ite_false_branch ht8] at hm_is
                              by_cases ht9 : (tag == 9#32) = true
                              · rw [ite_true_branch ht9] at hm_is
                                obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                                have hb := optInnerStatePolyCapBound_of_ekReceivedCt1Sampled (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                                have hle := ekReceivedCt1SampledPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                                unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                              · rw [ite_false_branch ht9] at hm_is
                                by_cases ht10 : (tag == 10#32) = true
                                · rw [ite_true_branch ht10] at hm_is
                                  obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                                  have hb := optInnerStatePolyCapBound_of_ct1Acknowledged (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                                  have hle := ct1AcknowledgedPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                                  unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                                · rw [ite_false_branch ht10] at hm_is
                                  by_cases ht11 : (tag == 11#32) = true
                                  · rw [ite_true_branch ht11] at hm_is
                                    obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                                    have hb := optInnerStatePolyCapBound_of_ct2Sampled (iwt := iwt) (msgPtr := 0#64) (bufRef := 0#64) (slot := 0#64) (ptr := 0#64) (by rw [hiwt, h1]; rfl)
                                    have hle := ct2SampledPolyCapBound_le iwt 0#64 0#64 0#64 0#64 r1 m.innerState
                                    unfold optInnerStatePolyCapBound at hb hle; exact Nat.le_trans hb hle
                                  · rw [ite_false_branch ht11] at hm_is
                                    obtain ⟨r, h1, h2⟩ := bind_ok_inv hm_is; cases h2
                                    have hsk := (proto_skipField_suffix (by rw [h1]; rfl)).1
                                    omega
            · rw [ite_false_branch htr] at hmf
              obtain ⟨r, h1, h2⟩ := bind_ok_inv hmf; cases h2
              have hsk := (proto_skipField_suffix (by rw [h1]; rfl)).1
              omega
          have hih := ih h
          omega

private theorem proto_takeExact_len :
    ∀ (n : Nat) (bs sub after : List (BitVec 8)),
      CryptoVerification.LibsignalSpqrV1.Proto.takeExact n bs = .ok (sub, after) →
      sub.length + after.length = bs.length
  | 0, bs, sub, after, h => by cases h; simp
  | n + 1, [], sub, after, h => by nomatch h
  | n + 1, b :: rest, sub, after, h => by
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.takeExact, Bind.bind, Except.bind] at h
    rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.takeExact n rest with _ | ⟨hd, tl⟩
    · rw [h1] at h; nomatch h
    · rw [h1] at h; cases h
      have ih := proto_takeExact_len n rest hd tl h1
      simp only [List.length_cons]
      omega

theorem optInnerStatePolyCapBound_of_v1State_merge {iwt : WireType}
    {m m' : V1State} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) m bs 100).toOption = some (m', after)) :
    optInnerStatePolyCapBound m'.innerState after.length ≤
      optInnerStatePolyCapBound m.innerState bs.length := by
  simp only [mergeMessage, Bind.bind, Except.bind] at hm
  rcases hcw : CryptoVerification.LibsignalSpqrV1.Proto.checkWireType .lengthDelimited
      (codecWireTypeToProto iwt) with _ | ⟨⟩
  · simp [hcw, Except.toOption] at hm
  · simp only [hcw] at hm
    rcases hdv : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint bs with _ | ⟨len, r0⟩
    · simp [hdv, Except.toOption] at hm
    · simp only [hdv] at hm
      have hlt0 : r0.length < bs.length := (proto_decodeVarint_suffix (by rw [hdv]; rfl)).1
      rcases hte : CryptoVerification.LibsignalSpqrV1.Proto.takeExact len.toNat r0 with _ | ⟨sub, after'⟩
      · simp [hte, Except.toOption] at hm
      · simp only [hte] at hm
        have hte_eq : sub.length + after'.length = r0.length :=
          proto_takeExact_len len.toNat r0 sub after' hte
        rcases hml : CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
            V1State.mergeField sub.length m sub 99 with _ | m1
        · simp [hml, Except.toOption] at hm
        · simp only [hml, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          have hloop := mergeFieldsLoop_v1State_polyCap sub.length hml
          unfold optInnerStatePolyCapBound
          omega

theorem decodeState_codecWireTypeToProto_eq (iwt : WireType) :
    CryptoVerification.SpqrV1.Top.DecodeState.codecWireTypeToProto iwt = codecWireTypeToProto iwt := by
  cases iwt <;> rfl

theorem pqRatchetState_tag3_some_inv {curSt st' : PqRatchetState}
    {iwt : WireType} {rest1 rest2 : List (BitVec 8)}
    (hmf : (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption =
      some (st', rest2)) :
    ∃ v1',
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt)
        (pqRatchetStateV1OrDefault curSt) rest1 100).toOption = some (v1', rest2) ∧
      st' = ⟨curSt.versionNegotiation, curSt.chain, some (.v1 v1')⟩ := by
  rcases curSt with ⟨optVn, optCh, inner⟩
  have htag3 := pqRatchetState_mergeField_tag3 ⟨optVn, optCh, inner⟩ iwt rest1 100
  rw [decodeState_codecWireTypeToProto_eq] at htag3
  rw [htag3] at hmf
  cases inner with
  | none =>
    dsimp only [pqRatchetStateV1OrDefault] at hmf ⊢
    rcases hm : (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption
        with _ | ⟨v1', rest2'⟩
    · rw [hm] at hmf; cases hmf
    · rw [hm] at hmf; cases hmf
      exact ⟨v1', rfl, rfl⟩
  | some inr =>
    cases inr with
    | v1 v1 =>
      dsimp only [pqRatchetStateV1OrDefault] at hmf ⊢
      rcases hm : (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption
          with _ | ⟨v1', rest2'⟩
      · rw [hm] at hmf; cases hmf
      · rw [hm] at hmf; cases hmf
        exact ⟨v1', rfl, rfl⟩

/-! ## 2. Empty-Input Fast Path (`+1604`) and Post-Loop Success Exit (`+1676`) -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

theorem spqrDecodeState_eq_of_mergeLoopBin_top_err {bs : List (BitVec 8)} (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = none) :
    spqrDecodeState bs = .error .stateDecode := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState at hopt
    unfold spqrDecodeState CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st
    · rfl
    · simp [hm, Except.toOption] at hopt

theorem spqrDecodeState_eq_of_mergeLoopBin_top_ok {bs : List (BitVec 8)} {st : PqRatchetState}
    (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = some st) :
    spqrDecodeState bs = .ok st := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState at hopt
    unfold spqrDecodeState CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st'
    · simp [hm, Except.toOption] at hopt
    · simp only [hm, Except.toOption, Option.some.injEq] at hopt
      subst hopt
      rfl

private theorem memRegion_352_empty_split (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 8#64) 40 ∗
      memRegion (outPtr + 56#64) 72 ∗
      memRegion (outPtr + 136#64) 216 ∗
      (∃∗ w128 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w0 : BitVec 64,
        (outPtr ↦₆₄ w0) ∗ ((outPtr + 48#64) ↦₆₄ w48) ∗ ((outPtr + 128#64) ↦₆₄ w128)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 40) (k := 304)
      (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 296)
      (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 56#64) (n := 72) (k := 224)
      (b' := outPtr + 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 128#64) (n := 8) (k := 216)
      (b' := outPtr + 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 48#64),
    ProofLib.memRegion_eight (outPtr + 128#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem fold_decodeStateResultAt_empty (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (outPtr : BitVec 64) {bs : List (BitVec 8)} (hbs : bs = []) :
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (outPtr + 8#64) 40 ∗
      ((outPtr + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (outPtr + 56#64) 72 ∗
      ((outPtr + 128#64) ↦₆₄ 0xfffffffffffffffd#64) ∗ memRegion (outPtr + 136#64) 216 ⊢
      decodeStateResultAt H_inner A outPtr (spqrDecodeState bs) := by
  subst hbs
  unfold spqrDecodeState
  rw [spqrDecodeState_nil, pqRatchetState_default_eq]
  unfold decodeStateResultAt protoPqRatchetStateAt
    optVersionNegotiationPBAt optChainPBAt optProtoPqRatchetInnerAt
    noneCap none3Cap
  dsimp only
  have ha56 : (outPtr + 48#64) + 8#64 = outPtr + 56#64 := by bv_omega
  have ha136 : (outPtr + 128#64) + 8#64 = outPtr + 136#64 := by bv_omega
  rw [ha56, ha136]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem stack_1392_fold_1296 (sp w0 : BitVec 64) :
    ((sp - 1392#64) ↦₆₄ w0) ∗ memRegion (sp - 1384#64) 1288 ⊢
      memRegion (sp - 1392#64) 1296 := by
  rw [ProofLib.memRegion_split' (b := sp - 1392#64) (n := 8) (k := (1288 : Nat))
      (b' := sp - 1384#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 1392#64) w0)

/-- Envelope-parameterized empty-input fast path `+1604..+1624` (6 instructions) -> `+2500`. -/
theorem decodeState_empty_53ae0_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64) (hbs : x.st.bytes = [])
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 1604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      ((s0.sp - 1392#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 1384#64) 1288 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  refine SepWP.fold (memRegion_352_empty_split x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool ((blkPl_325).base + 2500#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (fold_decodeStateResultAt_empty H_inner A.repAlloc x.outPtr hbs)
    (by sep_focus) ?_
  refine SepWP.fold (stack_1392_fold_1296 s0.sp w0) (by sep_focus) ?_
  exact decodeState_epilogue_53e60_placed_ofEnv x st0 st s0 _ _ R post hpost henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    hs0A
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)

theorem decodeState_empty_53ae0_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64) (hbs : x.st.bytes = [])
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 1604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      ((s0.sp - 1392#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 1384#64) 1288 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_empty_53ae0_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    x st0 st w0 hbs s0 s P R post hpost henv hpc hrun hsp hs0A htr hx19 hP

private theorem head_ne_none2Cap_branch {w : BitVec 64} (hne : w ≠ none2Cap) :
    (w + 2#64 == 0#64) = false ∧ (w + 2#64 != 0#64) = true := by
  have h0 : w + 2#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -2#64
    bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h0, bne_iff_ne.mpr h0⟩

private theorem state_1040_fold_352 (sp w0 w1 : BitVec 64) {bs336 : List (BitVec 8)}
    (hlen : bs336.length = 336) :
    ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) ⊢
      memRegion (sp - 1040#64) 352 := by
  have h16 : ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ⊢ memRegion (sp - 1040#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 8)
        (b' := sp - 1032#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ w0)
      (ProofLib.pointsTo64_entails_memRegion _ w1)
  have h336 : ((sp - 1024#64) ↦ₛ bs336) ⊢ memRegion (sp - 1024#64) 336 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp - 1024#64) bs336
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 16) (k := 336)
      (b' := sp - 1024#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) =
      (((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1)) ∗ ((sp - 1024#64) ↦ₛ bs336) := by
    sep_ac_rfl
  rw [hassoc]
  exact sepConj_mono h16 h336

private theorem memRegion_352_split_head16_tail336 (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 16#64) 336 ∗
      (∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (outPtr ↦₆₄ out0) ∗ ((outPtr + 8#64) ↦₆₄ out1)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 8) (k := 336)
      (b' := outPtr + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Envelope-parameterized post-loop success exit (`+1676..+1724`, 13 instructions) -> `+2500`. -/
theorem decodeState_ok_exit_53b28_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0_scr : BitVec 64) (curSt : PqRatchetState)
    (hok : spqrDecodeState x.st.bytes = .ok curSt)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) 0 curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy allocHookStack (Nat.le_refl _) (by decide)
  simp only [withVmPreserved, sessionMemcpySpec] at hmemcpy
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x [] 0 curSt s0 s)
    (by sep_focus) ?_
  refine SepWP.fold (scratch_688_fold_48 s0.sp w0_scr)
    (by dsimp only [decodeStateErrFramePlaced]; sep_focus) ?_
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hmemcpy ⊢
  refine SepWP.fold (protoPqRatchetStateAt_entails_head16_tail336 H_inner A.repAlloc
    (s0.sp - 1040#64) curSt) (by sep_focus) ?_
  wp_pull_exists
  rename_i w0 w1 bs336
  wp_focus_pure; rintro ⟨hw0_ne, hbs336_len⟩
  have ⟨hcmn_eq_f, hcmn_ne_t⟩ := head_ne_none2Cap_branch hw0_ne
  rw [ProofLib.memRegion_split' (b := s0.sp - 1392#64) (n := 336) (k := 16)
      (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  try simp only [State.setMem_setMem]
  wp_apply
  wp_conv_pre => simp only [*]
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (state_1040_fold_352 s0.sp w0 w1 hbs336_len) (by sep_focus) ?_
  refine SepWP.fold (memRegion_352_split_head16_tail336 x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool (lsρ "memcpy")
  try simp only [State.setMem_setMem]
  wp_apply
  wp_conv_pre => simp only [*]
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  have h336_sp : ((s0.sp - 1392#64) ↦ₛ bs336) ⊢ memRegion (s0.sp - 1392#64) 336 := by
    rw [← hbs336_len]; exact pointsToBytes_entails_memRegion (s0.sp - 1392#64) bs336
  refine SepWP.fold h336_sp (by sep_focus) ?_
  refine SepWP.fold (lower_352_fold s0.sp) (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2500#64)
  try simp only [State.setMem_setMem]
  have hfold_ok :
      (x.outPtr ↦₆₄ w0) ∗ ((x.outPtr + 8#64) ↦₆₄ w1) ∗ ((x.outPtr + 16#64) ↦ₛ bs336) ∗
        (relocProtoPqRatchetStateTailAt H_inner A.repAlloc w0 w1 curSt).1 bs336 ⊢
        decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) := by
    rw [hok]
    exact head16_tail336_entails_protoPqRatchetStateAt H_inner A.repAlloc
      x.outPtr w0 w1 bs336 curSt hbs336_len
  refine SepWP.fold hfold_ok (by sep_focus) ?_
  exact decodeState_epilogue_53e60_placed_ofEnv x st0 st s0 _ _ R post hpost henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    hs0A
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)

theorem decodeState_ok_exit_53b28_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0_scr : BitVec 64) (curSt : PqRatchetState)
    (hok : spqrDecodeState x.st.bytes = .ok curSt)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) 0 curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_ok_exit_53b28_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0_scr curSt hok s0 s P R post hpost henv hs0A hpc hrun hsp htr hx19 hx22 hP

/-! ## 3. Outer Loop Tag Dispatch (`+160..+180`) -/

/-- Envelope-parameterized outer loop tag dispatch at `+160` (6 instructions) given `1 ≤ tag < 2 ^ 29`:
dispatches `tag = 3` (`+312`), `tag = 2` (`+244`), `tag = 1` (`+184`), and
`tag ∉ {1, 2, 3}` (`+456`), reaching `entry + 1576` on success while maintaining
`hlinks`, `hpoly`, `hacc`, `hst`, and `hFit` (`8 * (rest1.length - rest2.length)` steps). -/
theorem decodeState_outer_dispatch_5353c_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (curSt.chain.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (hpoly : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault curSt).innerState rest1.length ≤
      2 * x.st.bytes.length + 16)
    (herr_of_none :
      (match (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption with
       | none => none
       | some (st', rest2) => mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 8 * rest1.length + 24 ≤ rem)
    (hf : f + 8 * rest1.length + 24 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      (st'.chain.getD default).links.length + rest2.length ≤ 2 * x.st.bytes.length + 4 →
      optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 →
      DecodeStateLoopEnv (f + 8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases htag3 : tag = 3
  · subst htag3
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 312#64)
    wp_steps 2
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    refine decodeState_v1_entry_535d4_placed_ofEnv
      (V1PreEnv := V1StateMergeEnv) (V1PostEnv := V1StateMergePostEnv)
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
      hc.toDecodeStateCalleeContractsPlaced hc.v1StateMerge
      x st0 st w0 curSt rest1 iwt hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [show BitVec.ofNat 32 3 = 3#32 from rfl, hnone]))
      s0 _ _ R post hpost
      (fun _ => hFit.mono fun evs hevs => by
        dsimp only [V1StateMergeEnv] at hevs
        have hdl := spqrMergeLoopEnv_to_decodeStateLoopEnv hevs (by omega)
        exact hdl.mono (by omega) hrest1_le hpoly)
      (fun evs_v1 evs_drop n _ _ hv1 hdrop hn => by
        have hv1' := v1StateMergePostEnv_imp_pre hv1
        dsimp only [V1StateMergeEnv] at hv1'
        have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1' (by omega)
        have hv1_l : DecodeStateLoopEnv (8 * rest1.length + 16) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_v1 :=
          hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
        have hdr_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_drop :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hdrop)
        have h12 := hv1_l.append hdr_l
        have hFit1 : FitsEnv M lim (M.stepEvents (evs_v1 ++ evs_drop) st)
            (DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split h12
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        rw [M.stepEvents_append] at hFit1
        exact fitsEnv_decodeErrorPush_of_loop hn (by decide) hFit1)
      (fun evs_v1 evs_drop evs_p evs_f n _ _ hv1 hdrop hn hp hf_evs => by
        have hv1' := v1StateMergePostEnv_imp_pre hv1
        dsimp only [V1StateMergeEnv] at hv1'
        have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1' (by omega)
        have hv1_l : DecodeStateLoopEnv (8 * rest1.length + 16) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_v1 :=
          hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
        have hdr_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_drop :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hdrop)
        have hp_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_p :=
          DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hp)
        have hf_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_f :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hf_evs)
        have htot := (((hacc.append hv1_l).append hdr_l).append hp_l).append hf_l
        refine ⟨((((evs_acc ++ evs_v1) ++ evs_drop) ++ evs_p) ++ evs_f),
          hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
        rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst])
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
      (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
      (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
      (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
      (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
      (by
        dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
    intro w0' st' rest2 evs_v1 sf P' hmf _ hv1 hle2 hsuf2
    obtain ⟨v1', hv1_ok, hst'_eq⟩ := pqRatchetState_tag3_some_inv hmf
    have hv1_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_v1 := by
      dsimp only [V1StateMergePostEnv] at hv1
      rw [hv1_ok] at hv1
      have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1 (by omega)
      exact hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
    have hlinks' : (st'.chain.getD default).links.length + rest2.length ≤
        2 * x.st.bytes.length + 4 := by
      rw [hst'_eq]; dsimp only; omega
    have hpoly' : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 := by
      rw [hst'_eq]; dsimp only [pqRatchetStateV1OrDefault]
      exact Nat.le_trans (optInnerStatePolyCapBound_of_v1State_merge hv1_ok) hpoly
    have hFit' : FitsEnv M lim (M.stepEvents evs_v1 st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) :=
      decodeStateLoop_split hv1_step
        (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
    exact hnext w0' st' rest2 evs_v1 sf P' hle2 hsuf2
      (by rw [show BitVec.ofNat 32 3 = 3#32 from rfl]; exact hmf)
      hlinks' hpoly' (hacc.append hv1_step) (by rw [M.stepEvents_append, hst]) hFit'
  · by_cases htag2 : tag = 2
    · subst htag2
      rcases curSt with ⟨optVn, optCh, inner⟩
      have htag2_eq := pqRatchetState_mergeField_tag2 ⟨optVn, optCh, inner⟩ iwt rest1 100
      rw [decodeState_codecWireTypeToProto_eq] at htag2_eq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 244#64)
      wp_steps 4
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      refine decodeState_chain_entry_53590_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 st evs_acc f rem w0 optVn optCh inner rest1 iwt
        hrest1_le hrest1_suf hlen_bound hlinks
        (fun hnone => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, htag2_eq]
          dsimp only; rw [hnone]; rfl))
        hacc hst hFit (by omega) (by omega) s0 _ _ R post hpost hpost_env hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
        (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
        (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
        (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
        (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
        (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
        (by
          dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
            Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          try simp only [wp_norm, arm64_norm]
          try sep_ac_rfl) ?_
      intro w0' ch' rest2 evs_ch sf P' hmf hlinks2 hacc2 hst2 hFit2 hle2 hsuf2
      exact hnext w0' ⟨optVn, some ch', inner⟩ rest2 evs_ch sf P' hle2 hsuf2
        (by rw [show BitVec.ofNat 32 2 = 2#32 from rfl, htag2_eq]
            dsimp only; rw [hmf]; rfl)
        (by dsimp only; exact Nat.le_trans hlinks2 hlinks)
        (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
        (hacc2.mono_fuel (by omega)) hst2
        (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit2)
    · by_cases htag1 : tag = 1
      · subst htag1
        rcases curSt with ⟨optVn, optCh, inner⟩
        have htag1_eq := pqRatchetState_mergeField_tag1 ⟨optVn, optCh, inner⟩ iwt rest1 100
        rw [decodeState_codecWireTypeToProto_eq] at htag1_eq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 184#64)
        wp_steps 6
        apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        refine decodeState_vn_entry_53554_placed_ofEnv
          (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16)
          (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
          hc.toDecodeStateCalleeContractsPlaced (bytesMerge3Det_of_contractsPlacedX hc)
          x st0 st w0 optVn optCh inner rest1 iwt
          hrest1_le hrest1_suf hlen_bound (Nat.le_refl _) (by omega)
          (fun hnone => herr_of_none (by
            rw [show BitVec.ofNat 32 1 = 1#32 from rfl, htag1_eq]
            dsimp only; rw [hnone]; rfl))
          s0 _ _ R post hpost
          (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
          (fun evs_err herr_loop => by
            have htot := hacc.append herr_loop
            refine ⟨evs_acc ++ evs_err,
              hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
            rw [M.stepEvents_append, hst])
          hs0A
          (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
          (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
          (by
            dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            try simp only [wp_norm, arm64_norm]
            try sep_ac_rfl) ?_
        intro vn' rest2 evs_vn sf P' hmf hvn_loop hle2 hsuf2
        have hvn_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_vn :=
          hvn_loop.mono_fuel (by omega)
        have hFit' : FitsEnv M lim (M.stepEvents evs_vn st)
            (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split hvn_step
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        exact hnext w0 ⟨some vn', optCh, inner⟩ rest2 evs_vn sf P' hle2 hsuf2
          (by rw [show BitVec.ofNat 32 1 = 1#32 from rfl, htag1_eq]
              dsimp only; rw [hmf]; rfl)
          (by dsimp only at hlinks ⊢; omega)
          (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
          (hacc.append hvn_step) (by rw [M.stepEvents_append, hst]) hFit'
      · -- tag ≥ 4
        have ⟨_, _, _, _, hbeq3, hbne3⟩ := tag_cmp32_of_gt (c := 3) (by omega) htag29
        have ⟨_, _, _, _, hbeq2, hbne2⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
        have ⟨_, _, _, _, hbeq1, hbne1⟩ := tag_cmp32_of_gt (c := 1) (by omega) htag29
        have htw32 := tag_setWidth32_ofNat tag
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 456#64)
        wp_steps 6
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [wp_norm, arm64_norm, hrun])
        refine decodeState_outer_skip_53664_placed_ofEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
          hc.toDecodeStateCalleeContractsPlaced x st0 st w0 curSt rest1 iwt tag
          (by omega) hrest1_le hrest1_suf hlen_bound
          (fun hnone => herr_of_none (by
            have ho := pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100
            rw [decodeState_codecWireTypeToProto_eq] at ho
            rw [ho, hnone]; rfl))
          s0 _ _ R post hpost
          (decodeStateLoop_head (fuel := rem - 1)
            (fun _ h => DecodeStateIterEnv.of_skipField3 h)
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
          (fun evs_sf evs_f _ hsf_env hf_evs => by
            have hsf_l : DecodeStateLoopEnv 1 x.st.bytes.length
                (2 * x.st.bytes.length + 16) evs_sf :=
              DecodeStateLoopEnv.single (fuel := 0) (DecodeStateIterEnv.of_skipField3 hsf_env)
            have hf_l : DecodeStateLoopEnv 1 x.st.bytes.length
                (2 * x.st.bytes.length + 16) evs_f :=
              DecodeStateLoopEnv.single (fuel := 0) (.deallocs hf_evs)
            have htot := (hacc.append hsf_l).append hf_l
            refine ⟨(evs_acc ++ evs_sf) ++ evs_f,
              hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
            rw [M.stepEvents_append, M.stepEvents_append, hst])
          hs0A
          (by dsimp only [decodeStatePlacedEntry]
              simp only [wp_norm, arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
          (by simp only [wp_norm, arm64_norm, hx1, htw32])
          (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
          (by
            dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            try simp only [wp_norm, arm64_norm]
            try sep_ac_rfl) ?_
        intro rest2 evs_sf sf P' hsf hevs_sf hle2 hsuf2
        have hnil_sf : evs_sf = [] := skipField3Env_ok_nil hsf hevs_sf
        have hsf_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_sf := by
          rw [hnil_sf]; exact .nil
        have hFit' : FitsEnv M lim (M.stepEvents evs_sf st)
            (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split hsf_step
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        have ho := pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100
        rw [decodeState_codecWireTypeToProto_eq] at ho
        exact hnext w0 curSt rest2 evs_sf sf P' hle2 hsuf2
          (by rw [ho, hsf]; rfl)
          (by omega)
          (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
          (hacc.append hsf_step) (by rw [M.stepEvents_append, hst]) hFit'

theorem decodeState_outer_dispatch_5353c_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (curSt.chain.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (hpoly : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault curSt).innerState rest1.length ≤
      2 * x.st.bytes.length + 16)
    (herr_of_none :
      (match (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption with
       | none => none
       | some (st', rest2) => mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 8 * rest1.length + 24 ≤ rem)
    (hf : f + 8 * rest1.length + 24 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      (st'.chain.getD default).links.length + rest2.length ≤ 2 * x.st.bytes.length + 4 →
      optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 →
      DecodeStateLoopEnv (f + 8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_outer_dispatch_5353c_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 curSt rest1 tag iwt htag1_le htag29 hrest1_le hrest1_suf
    hlen_bound hlinks hpoly herr_of_none hacc hst hFit hrem hf s0 s P R post hpost
    (fun _ h => h) hs0A hpc hrun hsp htr hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    hP hnext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudgetAux
