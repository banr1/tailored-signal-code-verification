/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateVnPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Canonical Guarded-Tight Entry Execution for `spqr::decode_state` (`Block 325`)

Composes empty-input handling, prologue `+0 -> +116`, optional Fields 1 (`version_negotiation`),
2 (`chain`), and 3 (`V1State`), outer latch exit `+1576 -> +1676`, and `Ok` epilogue on
canonical `encodeState pb` wire inputs under `SpqrTightEvs (23 + v1Ops) 1307216 79236`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeKey encodeMessage encodeOptMessage encodeState mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (VecArg withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter suffix_trans)
open CryptoVerification.SpqrV1.Prost.BytesMerge (protoWireTypeToCodec)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (V1StateMergeGhost codecWireTypeToProto mergeLoopBin v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateSavedAt decodeStateStackX decodeState_nonempty_frame_split none3Cap
   optChainPBCapOkAt optProtoPqRatchetInnerCapOkAt optVersionNegotiationPBCapOkAt
   pqRatchetState_default_eq protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono
   scratch_688_split_48 sp_sub_1392_aligned stackAt_decodeState_entry_split
   vecArgRestAt vecArg_split_bytes)
open CryptoVerification.SpqrV1Sync.Codec (loopsTo_v1State mergeMessage_encode)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
  (e2a_fitsEnv_tight_split e2a_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget
  (E2aEpochDirCanonicalOk e2a_ValidChainPB e2a_ch_outer_field2_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateVnPlacedBudget
  (e2a_outer_key_decode_cl e2a_vn_outer_field1_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced SepWPpIPlaced.of_sepWP decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
  (decodeState_empty_53ae0_placed_ofEnv decodeState_ok_exit_53b28_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepClPlacedBudget
  (decodeState_v1_entry_535d4_cl_placed_ofEnv pqRatchetStateV1MsgPtr pqRatchetStateV1OrDefault)

def e2a_ValidVersionNegotiationPB (m : VersionNegotiationPB) : Prop :=
  m.authKey.length ≤ 32

/-! ## 1. Pure Canonical Codec & Wire Decomposition Helpers -/

private def e2a_innerBytes : Option PqRatchetState.Inner → Bytes
  | none => []
  | some (.v1 v1) => encodeMessage V1State.encodeRaw 3#32 v1

private theorem e2a_encodeState_decomp (pb : PqRatchetState) :
    encodeState pb =
      encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 pb.versionNegotiation ++
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) := by
  cases pb with
  | mk vn ch inner =>
    cases inner with
    | none =>
      simp [encodeState, PqRatchetState.encode, PqRatchetState.encodeRaw, e2a_innerBytes,
        List.append_assoc]
    | some inr =>
      cases inr with
      | v1 v1 =>
        simp [encodeState, PqRatchetState.encode, PqRatchetState.encodeRaw,
          PqRatchetState.Inner.encode, e2a_innerBytes, List.append_assoc]

private theorem e2a_encodeMessage_v1_eq (v1 : V1State) :
    encodeMessage V1State.encodeRaw 3#32 v1 =
      encodeKey 3#32 .lengthDelimited ++ e2a_lenPrefixed (V1State.encodeRaw v1) [] := by
  simp [encodeMessage, e2a_lenPrefixed, List.append_assoc]

private theorem e2a_encodeKey_2_eq :
    encodeKey 2#32 .lengthDelimited = [0x12#8] := by
  decide

private theorem e2a_encodeKey_3_eq :
    encodeKey 3#32 .lengthDelimited = [0x1a#8] := by
  decide

private theorem e2a_encodeMessage_chain_ne_nil (ch : ChainPB) :
    encodeMessage ChainPB.encodeRaw 2#32 ch ≠ [] := by
  simp [encodeMessage, e2a_encodeKey_2_eq]

private theorem e2a_encodeMessage_v1_ne_nil (v1 : V1State) :
    encodeMessage V1State.encodeRaw 3#32 v1 ≠ [] := by
  rw [e2a_encodeMessage_v1_eq, e2a_encodeKey_3_eq]
  simp

private theorem e2a_inner_eq_none_of_bytes_nil {inner : Option PqRatchetState.Inner}
    (h : e2a_innerBytes inner = []) : inner = none := by
  cases inner with
  | none => rfl
  | some inr =>
    cases inr with
    | v1 v1 => exact absurd h (e2a_encodeMessage_v1_ne_nil v1)

private theorem e2a_chain_eq_none_of_bytes_nil {optCh : Option ChainPB}
    (h : encodeOptMessage ChainPB.encodeRaw 2#32 optCh = []) : optCh = none := by
  cases optCh with
  | none => rfl
  | some ch => exact absurd h (e2a_encodeMessage_chain_ne_nil ch)

private theorem e2a_v1_mergeMessage_ok (v1 : V1State)
    (hlen : (V1State.encodeRaw v1).length < 2 ^ 64) :
    mergeMessage V1State.mergeField .lengthDelimited default
      (e2a_lenPrefixed (V1State.encodeRaw v1) []) 100 = .ok (v1, []) := by
  unfold e2a_lenPrefixed
  rw [List.append_assoc]
  exact mergeMessage_encode V1State.mergeField 3 V1State.encodeRaw default v1 100 []
    (loopsTo_v1State v1 hlen) hlen (by decide)

private theorem e2a_pqRatchetState_tag3_merge_ok
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB) (v1 : V1State)
    (hlen : (V1State.encodeRaw v1).length < 2 ^ 64) :
    (PqRatchetState.mergeField ⟨optVn, optCh, none⟩ 3#32
        (codecWireTypeToProto .lengthDelimited)
        (e2a_lenPrefixed (V1State.encodeRaw v1) []) 100).toOption =
      some (⟨optVn, optCh, some (.v1 v1)⟩, []) := by
  have hm := e2a_v1_mergeMessage_ok v1 hlen
  have h1 : (3#32 == 1#32) = false := by decide
  have h2 : (3#32 == 2#32) = false := by decide
  have h3 : (3#32 == 3#32) = true := by decide
  simp only [codecWireTypeToProto, PqRatchetState.mergeField, PqRatchetState.Inner.merge,
    h1, h2, h3, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [hm]
  rfl

private theorem e2a_len_cbz64_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at hnat
  change n % 18446744073709551616 = 0 at hnat
  omega

/-! ## 2. Machine Stepping Helpers (Latch `+1576`, Field 3 `+116 -> +1576`, Prologue `+0 -> +116`) -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

private def localVecU8Heap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem vecArg_expose_len (A : RustAlloc) (st : VecArg) :
    st.at A ⊢
      (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      localVecU8Heap A st.cap st.ptr st.bytes := by
  unfold VecArg.at vecU8At vecHeader localVecU8Heap
  exact Entails.of_eq (by sep_ac_rfl)

private theorem vecArg_fold_len (A : RustAlloc) (st : VecArg) :
    (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      localVecU8Heap A st.cap st.ptr st.bytes ⊢
      st.at A := by
  unfold VecArg.at vecU8At vecHeader localVecU8Heap
  exact Entails.of_eq (by sep_ac_rfl)

private theorem nonempty_prologue_frame_assemble (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (st : VecArg) :
    ((sp - 1056#64) ↦₆₄ st.ptr) ∗
      ((sp - 1048#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      (st.ptr ↦ₛ st.bytes) ∗
      ((sp - 1040#64) ↦₆₄ (-1#64)) ∗ memRegion (sp - 1032#64) 40 ∗
      ((sp - 992#64) ↦₆₄ (-1#64)) ∗ memRegion (sp - 984#64) 72 ∗
      ((sp - 912#64) ↦₆₄ (-3#64)) ∗ memRegion (sp - 904#64) 216 ⊢
      sliceCursorAfter (sp - 1056#64) st.ptr st.bytes st.bytes ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) st.bytes.length ⟨none, none, none⟩ := by
  unfold sliceCursorAfter protoPqRatchetStateCapOkAt
    optVersionNegotiationPBCapOkAt optChainPBCapOkAt optProtoPqRatchetInnerCapOkAt
    noneCap none3Cap
  dsimp only
  have hsub0 : st.bytes.length - st.bytes.length = 0 := Nat.sub_self _
  have hptr0 : st.ptr + BitVec.ofNat 64 0 = st.ptr := by simp
  have ha1048 : (sp - 1056#64) + 8#64 = sp - 1048#64 := by bv_omega
  have ha1032 : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
  have ha992 : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
  have ha984 : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
  have ha912 : (sp - 1040#64) + 128#64 = sp - 912#64 := by bv_omega
  have ha904 : (sp - 912#64) + 8#64 = sp - 904#64 := by bv_omega
  rw [hsub0, hptr0, ha1048, ha1032, ha992, ha984, ha912, ha904]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem decodeState_nonempty_frame_split_s0 (sp0 : BitVec 64) :
    ((sp0 - 1392#64) ↦₆₄ 0#64) ∗ memRegion (sp0 - 1384#64) 1288 ⊢
      memRegion (sp0 - 1392#64) 336 ∗
      memRegion (sp0 - 1032#64) 40 ∗
      memRegion (sp0 - 984#64) 72 ∗
      memRegion (sp0 - 904#64) 216 ∗
      memRegion (sp0 - 688#64) 352 ∗
      memRegion (sp0 - 328#64) 224 ∗
      memRegion (sp0 - 104#64) 8 ∗
      (∃∗ bRef : BitVec 64, ∃∗ in0 : BitVec 64, ∃∗ ch0 : BitVec 64,
       ∃∗ vn0 : BitVec 64, ∃∗ cLen : BitVec 64, ∃∗ cPtr : BitVec 64,
        ((sp0 - 1056#64) ↦₆₄ cPtr) ∗ ((sp0 - 1048#64) ↦₆₄ cLen) ∗
        ((sp0 - 1040#64) ↦₆₄ vn0) ∗ ((sp0 - 992#64) ↦₆₄ ch0) ∗
        ((sp0 - 912#64) ↦₆₄ in0) ∗ ((sp0 - 336#64) ↦₆₄ bRef)) := by
  have hsplit := decodeState_nonempty_frame_split (sp0 - 1392#64) 0#64
  have h1 : sp0 - 1392#64 + 8#64 = sp0 - 1384#64 := bv_sub_add_lit sp0 1392 8
  have h2 : sp0 - 1392#64 + 360#64 = sp0 - 1032#64 := bv_sub_add_lit sp0 1392 360
  have h3 : sp0 - 1392#64 + 408#64 = sp0 - 984#64 := bv_sub_add_lit sp0 1392 408
  have h4 : sp0 - 1392#64 + 488#64 = sp0 - 904#64 := bv_sub_add_lit sp0 1392 488
  have h5 : sp0 - 1392#64 + 704#64 = sp0 - 688#64 := bv_sub_add_lit sp0 1392 704
  have h6 : sp0 - 1392#64 + 1064#64 = sp0 - 328#64 := bv_sub_add_lit sp0 1392 1064
  have h7 : sp0 - 1392#64 + 1288#64 = sp0 - 104#64 := bv_sub_add_lit sp0 1392 1288
  have h8 : sp0 - 1392#64 + 336#64 = sp0 - 1056#64 := bv_sub_add_lit sp0 1392 336
  have h9 : sp0 - 1392#64 + 344#64 = sp0 - 1048#64 := bv_sub_add_lit sp0 1392 344
  have h10 : sp0 - 1392#64 + 352#64 = sp0 - 1040#64 := bv_sub_add_lit sp0 1392 352
  have h11 : sp0 - 1392#64 + 400#64 = sp0 - 992#64 := bv_sub_add_lit sp0 1392 400
  have h12 : sp0 - 1392#64 + 480#64 = sp0 - 912#64 := bv_sub_add_lit sp0 1392 480
  have h13 : sp0 - 1392#64 + 1056#64 = sp0 - 336#64 := bv_sub_add_lit sp0 1392 1056
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] at hsplit
  exact hsplit

private theorem e2a_prologue_52_to_116_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 : M.σ)
    {s0 s : State} {P R : SepProp}
    {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 52#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = x.st.ptr)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 x.st.bytes.length)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      vecArgRestAt A.repAlloc x.st ∗
      memRegion (s0.sp - 1384#64) 1288 ∗
      ((s0.sp - 1392#64) ↦₆₄ 0#64) ∗
      v1StateJumpTablesPlacedAt ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st0 s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
    (hnext : ∀ (w0_scr : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 116#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes x.st.bytes ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) x.st.bytes.length
          ⟨none, none, none⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st0 x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 116#64)
  refine SepWP.fold (decodeState_nonempty_frame_split_s0 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool ((blkPl_325).base + 116#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (nonempty_prologue_frame_assemble H_inner A.repAlloc s0.sp x.st)
    (by sep_focus) ?_
  refine SepWP.fold (scratch_688_split_48 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  rename_i w0_scr
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun])
  exact hnext w0_scr _ _
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      unfold decodeStateLoopCommonPlaced
      simp only [wp_norm, arm64_norm, hsp, hx29]
      sep_ac_rfl)

private theorem e2a_entry_to_116_or_ret_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 : M.σ) (s0 : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hnil_env : PostEnv x [])
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st0 s0 ∗
      stackAt s0.sp decodeStateStackX)
    (hnext : x.st.bytes ≠ [] → ∀ (w0_scr : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 116#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes x.st.bytes ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) x.st.bytes.length
          ⟨none, none, none⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st0 x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  rw [stackAt_decodeState_entry_split s0.sp]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases hbs_nil : x.st.bytes = []
  · have hlen0 : BitVec.ofNat 64 x.st.bytes.length = 0#64 := by rw [hbs_nil]; rfl
    apply SepWPpIPlaced.of_sepWPp
    apply SepWPp.of_sepWP_ret
    wp_pull_exists
    unfold decodeStateSavedAt
    refine SepWP.fold (vecArg_expose_len A.repAlloc x.st) (by sep_focus) ?_
    wp_steps_sync_pool ((blkPl_325).base + 1604#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (vecArg_fold_len A.repAlloc x.st) (by sep_focus) ?_
    exact decodeState_empty_53ae0_placed_ofEnv x st0 st0 0#64 hbs_nil s0 _ _ R post hpost
      ⟨[], hnil_env, rfl⟩
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc, hx0, hlen0])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm])
      hs0A
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hx8])
      (by unfold decodeStateSavedAt; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
  · have hpos0 : 0 < x.st.bytes.length := List.length_pos_of_ne_nil hbs_nil
    have hcbz : (BitVec.ofNat 64 x.st.bytes.length == 0#64) = false :=
      e2a_len_cbz64_false hpos0 hlen_bound
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 52#64)
    wp_pull_exists
    unfold decodeStateSavedAt
    refine SepWP.fold (vecArg_split_bytes A.repAlloc x.st hbs_nil) (by sep_focus) ?_
    unfold vecArgRestAt
    wp_focus_pure; intro hpure_st
    wp_steps_sync_pool ((blkPl_325).base + 52#64)
    try simp only [State.setMem_setMem]
    have hfold_rest :
        (x.st.v ↦₆₄ x.st.cap) ∗ ((x.st.v + 8#64) ↦₆₄ x.st.ptr) ∗
          ((x.st.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.bytes.length) ∗
          A.repAlloc.live x.st.ptr x.st.cap.toNat 1 ∗
          memRegion (x.st.ptr + BitVec.ofNat 64 x.st.bytes.length)
            (x.st.cap.toNat - x.st.bytes.length) ⊢
          vecArgRestAt A.repAlloc x.st := by
      unfold vecArgRestAt
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (Entails.pure_right hpure_st (Entails.refl _)))))
      sep_ac_rfl
    refine SepWP.fold hfold_rest (by sep_focus) ?_
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, hpc, hx0, hcbz])
      (by simp only [wp_norm, arm64_norm, hrun])
    exact e2a_prologue_52_to_116_cl x st0 hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc, hx0, hcbz])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx8])
      (by simp only [wp_norm, arm64_norm])
      (by unfold decodeStateSavedAt; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      (hnext hbs_nil)

private theorem e2a_latch_exit_53ac4_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (pb curSt : PqRatchetState) (hok : spqrDecodeState x.st.bytes = .ok pb)
    (st0 st : M.σ) (evs_fin : List AllocEvent) (w0 : BitVec 64) (cur : Bytes)
    (hcur_nil : cur = []) (hcurSt : curSt = pb)
    (hevs_post : PostEnv x evs_fin) (hst : M.stepEvents evs_fin st0 = st)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1576#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cur.length)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst cur
  cases hcurSt
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    List.length_nil] at hpc hx20 ⊢
  apply SepWPpIPlaced.of_sepWPp
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_325).base + 1676#64)
  try simp only [State.setMem_setMem]
  exact decodeState_ok_exit_53b28_cl_placed_ofEnv hc.toDecodeStateCalleeContractsClPlaced
    x st0 st w0 pb hok s0 _ _ R post hpost
    ⟨evs_fin, hevs_post, hst⟩ hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc, hx20])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx22])
    (by
      dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

private theorem e2a_latch_cont_53ac4_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64) (curSt : PqRatchetState) (cur : Bytes)
    (hcur_ne : cur ≠ []) (hcur_le : cur.length ≤ x.st.bytes.length)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1576#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cur.length)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 116#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hpos : 0 < cur.length := List.length_pos_of_ne_nil hcur_ne
  have hcbz : (BitVec.ofNat 64 cur.length == 0#64) = false :=
    e2a_len_cbz64_false hpos (by omega)
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 116#64)
  wp_steps_sync_pool ((blkPl_325).base + 116#64)
  try simp only [State.setMem_setMem]
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hpc, hx20, hcbz])
    (by simp only [wp_norm, arm64_norm, hrun])
  exact hnext _ _
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc, hx20, hcbz])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx21])
    (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23])
    (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25])
    (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm, hx27])
    (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl)

private theorem e2a_v1_outer_field3_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB) (v1 : V1State)
    (hv1_tight_v1 : ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes)
        (evs : List AllocEvent),
      V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
        e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
      SpqrTightEvs v1Ops 731332 2560 evs)
    {cur : Bytes} (hcur_eq : cur = encodeMessage V1State.encodeRaw 3#32 v1)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs v1Ops 731332 2560))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, optCh, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs v1Ops 731332 2560 evs_v1 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 ([] : Bytes).length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) ([] : Bytes).length
          ⟨optVn, optCh, some (.v1 v1)⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  let rest1 : Bytes := e2a_lenPrefixed (V1State.encodeRaw v1) []
  have hcur_key : cur = encodeKey 3#32 .lengthDelimited ++ rest1 := by
    rw [hcur_eq, e2a_encodeMessage_v1_eq]
  have hraw_lt64 : (V1State.encodeRaw v1).length < 2 ^ 64 := by
    have : (V1State.encodeRaw v1).length ≤ cur.length := by
      rw [hcur_key]
      simp only [rest1, e2a_lenPrefixed, List.length_append]
      omega
    omega
  have hmerge_ok := e2a_pqRatchetState_tag3_merge_ok optVn optCh v1 hraw_lt64
  have hfit_nil : FitsEnv M lim st (fun evs => evs = []) :=
    fun evs he => by subst he; exact hFit [] (SpqrTightEvs.nil v1Ops 731332 2560)
  refine e2a_outer_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
    hc.toDecodeStateCalleeContractsClPlaced x st0 st
    (((s0.sp - 688#64) ↦₆₄ w0) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, optCh, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
    3#32 .lengthDelimited hcur_key (by decide) (by decide)
    hcur_le hcur_suf hlen_bound hfit_nil hs0A
    hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 P1 hlt1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
    hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
  have hle1_cur : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  subst hP1
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
    WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
  have hx1_gpr : s1.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3 := hx1_1
  have hx0_gpr : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := hx0_1
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 312#64)
  refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
    (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
    (st := ⟨optVn, optCh, none⟩) hle1_cur) (by sep_focus) ?_
  wp_steps 2
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
  refine decodeState_v1_entry_535d4_cl_placed_ofEnv
    (V1PreEnv := V1Env) (V1PostEnv := V1Env)
    (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
    hc.toDecodeStateCalleeContractsClPlaced hv1_call
    x st0 st w0 ⟨optVn, optCh, none⟩ rest1 .lengthDelimited
    hrest1_le hrest1_suf hlen_bound
    (fun hnone => by rw [hmerge_ok] at hnone; cases hnone)
    s0 _ _ R post hpost
    (fun _ => hFit.mono fun evs hevs =>
      hv1_tight_v1 (pqRatchetStateV1MsgPtr s0.sp ⟨optVn, optCh, none⟩)
        (s0.sp - 336#64) (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) [] evs hevs)
    (fun _ _ _ hnone => by rw [hmerge_ok] at hnone; cases hnone)
    (fun _ _ _ _ _ hnone => by rw [hmerge_ok] at hnone; cases hnone)
    hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, hx0_gpr])
    (by simp only [wp_norm, arm64_norm, hx19_1])
    (by simp only [wp_norm, arm64_norm, hx21_1])
    (by simp only [wp_norm, arm64_norm, hx22_1])
    (by simp only [wp_norm, arm64_norm, hx23_1])
    (by simp only [wp_norm, arm64_norm, hx24_1])
    (by simp only [wp_norm, arm64_norm, hx25_1])
    (by simp only [wp_norm, arm64_norm, hx26_1])
    (by simp only [wp_norm, arm64_norm, hx27_1])
    (by simp only [wp_norm, arm64_norm, hx28_1])
    (by simp only [wp_norm, arm64_norm, hx29_1])
    (by
      dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      try simp only [wp_norm, arm64_norm]
      sep_ac_rfl) ?_
  intro w0' st' rest2 evs_v1 sf P' hmf _ hevs_v1 _ _
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
    hx29_2 hP2
  rw [hmerge_ok] at hmf
  injection hmf with hmf'
  injection hmf' with hst'_eq hrest2_eq
  subst hst'_eq hrest2_eq
  have htight_v1 : SpqrTightEvs v1Ops 731332 2560 evs_v1 :=
    hv1_tight_v1 (pqRatchetStateV1MsgPtr s0.sp ⟨optVn, optCh, none⟩)
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) [] evs_v1 hevs_v1
  exact hdone w0' evs_v1 sf P' htight_v1
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
    hx29_2 hP2

/-! ## 3. Backwards Stage Composition (`Stage 3 -> Stage 2 -> Stage 1 -> Entry`) -/

private theorem e2a_stage3_at_116 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    (x : DecodeStateGhost) (pb : PqRatchetState) (hok : spqrDecodeState x.st.bytes = .ok pb)
    (hpost_env : ∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs)
    (hv1_tight : ∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs)
    (st0 st : M.σ) (evs12 : List AllocEvent) (w0 : BitVec 64)
    (h12 : SpqrTightEvs 23 563001 79236 evs12)
    (hst12 : M.stepEvents evs12 st0 = st)
    (hc3_ne : e2a_innerBytes pb.inner ≠ [])
    (hc3_le : (e2a_innerBytes pb.inner).length ≤ x.st.bytes.length)
    (hc3_suf : IsDropSuffix x.st.bytes (e2a_innerBytes pb.inner))
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit3 : FitsEnv M lim st (SpqrTightEvs v1Ops 731332 2560))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes (e2a_innerBytes pb.inner) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64)
        (e2a_innerBytes pb.inner).length ⟨pb.versionNegotiation, pb.chain, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  cases hin : pb.inner with
  | none =>
    rw [hin] at hc3_ne
    exact absurd rfl hc3_ne
  | some inr =>
    cases inr with
    | v1 v1 =>
      have hc3_eq : e2a_innerBytes pb.inner = encodeMessage V1State.encodeRaw 3#32 v1 := by
        rw [hin]; rfl
      refine e2a_v1_outer_field3_cl_placed (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc hv1_call x st0 st w0 pb.versionNegotiation pb.chain v1
        (hv1_tight v1 hin) hc3_eq hc3_le hc3_suf hlen_bound hFit3 hpost hs0A
        hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
      intro w0' evs3 sf P' h3
        hpc' hrun' hsp' htr' hx19' hx20' _ hx22' _ _ _ _ _ _ _ hP'
      have hpb_eq : (⟨pb.versionNegotiation, pb.chain, some (.v1 v1)⟩ : PqRatchetState) = pb := by
        cases pb; simp at hin; subst hin; rfl
      have htot : SpqrTightEvs (23 + v1Ops) 1307216 79236 (evs12 ++ evs3) :=
        (h12.append h3).mono (by omega) (by decide) (by decide)
      have hst_tot : M.stepEvents (evs12 ++ evs3) st0 = M.stepEvents evs3 st := by
        rw [M.stepEvents_append, hst12]
      exact e2a_latch_exit_53ac4_cl hc x pb _ hok st0 (M.stepEvents evs3 st) (evs12 ++ evs3)
        w0' [] rfl hpb_eq (hpost_env _ htot) hst_tot hpost hs0A
        hpc' hrun' hsp' htr' hx19' hx20' hx22' hP'

private theorem e2a_after_stage2_at_1576 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    (x : DecodeStateGhost) (pb : PqRatchetState) (hok : spqrDecodeState x.st.bytes = .ok pb)
    (hpost_env : ∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs)
    (hv1_tight : ∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs)
    (st0 st : M.σ) (evs12 : List AllocEvent) (w0 : BitVec 64)
    (h12 : SpqrTightEvs 23 563001 79236 evs12)
    (hst12 : M.stepEvents evs12 st0 = st)
    (hc3_le : (e2a_innerBytes pb.inner).length ≤ x.st.bytes.length)
    (hc3_suf : IsDropSuffix x.st.bytes (e2a_innerBytes pb.inner))
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit3 : FitsEnv M lim st (SpqrTightEvs v1Ops 731332 2560))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1576#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (e2a_innerBytes pb.inner).length)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes (e2a_innerBytes pb.inner) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64)
        (e2a_innerBytes pb.inner).length ⟨pb.versionNegotiation, pb.chain, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hc3 : e2a_innerBytes pb.inner = []
  · have hin_none : pb.inner = none := e2a_inner_eq_none_of_bytes_nil hc3
    have hpb_eq : (⟨pb.versionNegotiation, pb.chain, none⟩ : PqRatchetState) = pb := by
      cases pb; simp at hin_none; subst hin_none; rfl
    have htot : SpqrTightEvs (23 + v1Ops) 1307216 79236 evs12 :=
      h12.mono (by omega) (by decide) (by decide)
    exact e2a_latch_exit_53ac4_cl hc x pb _ hok st0 st evs12 w0 _ hc3 hpb_eq
      (hpost_env _ htot) hst12 hpost hs0A hpc hrun hsp htr hx19 hx20 hx22 hP
  · refine e2a_latch_cont_53ac4_cl x st0 st w0 _ _ hc3 hc3_le hlen_bound hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro sf P' hpc' hrun' hsp' htr' hx19' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28'
      hx29' hP'
    exact e2a_stage3_at_116 hc hv1_call x pb hok hpost_env hv1_tight st0 st evs12 w0
      h12 hst12 hc3 hc3_le hc3_suf hlen_bound hFit3 hpost hs0A
      hpc' hrun' hsp' htr' hx19' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'

private theorem e2a_stage23_at_116 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2aEpochDirCanonicalOk A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    (x : DecodeStateGhost) (pb : PqRatchetState) (hok : spqrDecodeState x.st.bytes = .ok pb)
    (hpost_env : ∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs)
    (hch : ∀ ch, pb.chain = some ch → e2a_ValidChainPB ch)
    (hv1_tight : ∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs)
    (st0 st : M.σ) (evs1 : List AllocEvent) (w0 : BitVec 64)
    (h1 : SpqrTightEvs 2 1476 32 evs1)
    (hst1 : M.stepEvents evs1 st0 = st)
    (hc23_ne : encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner ≠ [])
    (hc23_le :
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length ≤
        x.st.bytes.length)
    (hc23_suf : IsDropSuffix x.st.bytes
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner))
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit23 : FitsEnv M lim st (SpqrTightEvs (21 + v1Ops) (561525 + 731332) 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64)
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length
        ⟨pb.versionNegotiation, none, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hFit23_max : FitsEnv M lim st
      (SpqrTightEvs (21 + v1Ops) (561525 + 731332) (max 79236 2560)) :=
    hFit23.mono fun _ hevs => hevs.mono (Nat.le_refl _) (Nat.le_refl _) (by decide)
  cases hch_opt : pb.chain with
  | none =>
    have hc2_nil : encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain = [] := by
      rw [hch_opt]; rfl
    rw [hc2_nil, List.nil_append] at hc23_ne hc23_le hc23_suf hP
    have hst_eq : (⟨pb.versionNegotiation, none, none⟩ : PqRatchetState) =
        ⟨pb.versionNegotiation, pb.chain, none⟩ := by
      rw [hch_opt]
    rw [hst_eq] at hP
    have hFit3 : FitsEnv M lim st (SpqrTightEvs v1Ops 731332 2560) :=
      e2a_fitsEnv_tight_split (SpqrTightEvs.nil 21 561525 79236) hFit23_max
    have h12 : SpqrTightEvs 23 563001 79236 evs1 :=
      h1.mono (by decide) (by decide) (by decide)
    exact e2a_stage3_at_116 hc hv1_call x pb hok hpost_env hv1_tight st0 st evs1 w0
      h12 hst1 hc23_ne hc23_le hc23_suf hlen_bound hFit3 hpost hs0A
      hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
  | some ch =>
    have hcur_eq :
        encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner =
          encodeMessage ChainPB.encodeRaw 2#32 ch ++ e2a_innerBytes pb.inner := by
      rw [hch_opt]; rfl
    have hFit2 : FitsEnv M lim st (SpqrTightEvs 21 561525 79236) :=
      hFit23.mono fun _ hevs => hevs.mono (by omega) (by omega) (by decide)
    refine e2a_ch_outer_field2_cl_placed (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc hEpochDir x st0 st w0 pb.versionNegotiation ch (hch ch hch_opt) none
      hcur_eq hc23_le hc23_suf hlen_bound hFit2 hpost hs0A
      hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro w0' evs2 sf P' h2 hc3_le hc3_suf
      hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
    have hst_eq : (⟨pb.versionNegotiation, some ch, none⟩ : PqRatchetState) =
        ⟨pb.versionNegotiation, pb.chain, none⟩ := by
      rw [hch_opt]
    rw [hst_eq] at hP'
    have hFit3 : FitsEnv M lim (M.stepEvents evs2 st) (SpqrTightEvs v1Ops 731332 2560) :=
      e2a_fitsEnv_tight_split h2 hFit23_max
    have h12 : SpqrTightEvs 23 563001 79236 (evs1 ++ evs2) :=
      (h1.append h2).mono (by decide) (by decide) (by decide)
    have hst12 : M.stepEvents (evs1 ++ evs2) st0 = M.stepEvents evs2 st := by
      rw [M.stepEvents_append, hst1]
    exact e2a_after_stage2_at_1576 hc hv1_call x pb hok hpost_env hv1_tight
      st0 (M.stepEvents evs2 st) (evs1 ++ evs2) w0'
      h12 hst12 hc3_le hc3_suf hlen_bound hFit3 hpost hs0A
      hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'

private theorem e2a_after_stage1_at_1576 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2aEpochDirCanonicalOk A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    (x : DecodeStateGhost) (pb : PqRatchetState) (hok : spqrDecodeState x.st.bytes = .ok pb)
    (hpost_env : ∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs)
    (hch : ∀ ch, pb.chain = some ch → e2a_ValidChainPB ch)
    (hv1_tight : ∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs)
    (st0 st : M.σ) (evs1 : List AllocEvent) (w0 : BitVec 64)
    (h1 : SpqrTightEvs 2 1476 32 evs1)
    (hst1 : M.stepEvents evs1 st0 = st)
    (hc23_le :
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length ≤
        x.st.bytes.length)
    (hc23_suf : IsDropSuffix x.st.bytes
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner))
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit23 : FitsEnv M lim st (SpqrTightEvs (21 + v1Ops) (561525 + 731332) 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1576#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64)
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length
        ⟨pb.versionNegotiation, none, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hc23 :
      encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner = []
  · obtain ⟨hc2, hc3⟩ := List.append_eq_nil_iff.mp hc23
    have hch_none : pb.chain = none := e2a_chain_eq_none_of_bytes_nil hc2
    have hin_none : pb.inner = none := e2a_inner_eq_none_of_bytes_nil hc3
    have hpb_eq : (⟨pb.versionNegotiation, none, none⟩ : PqRatchetState) = pb := by
      cases pb; simp at hch_none hin_none; subst hch_none hin_none; rfl
    have htot : SpqrTightEvs (23 + v1Ops) 1307216 79236 evs1 :=
      h1.mono (by omega) (by decide) (by decide)
    exact e2a_latch_exit_53ac4_cl hc x pb _ hok st0 st evs1 w0 _ hc23 hpb_eq
      (hpost_env _ htot) hst1 hpost hs0A hpc hrun hsp htr hx19 hx20 hx22 hP
  · refine e2a_latch_cont_53ac4_cl x st0 st w0 _ _ hc23 hc23_le hlen_bound hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro sf P' hpc' hrun' hsp' htr' hx19' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28'
      hx29' hP'
    exact e2a_stage23_at_116 hc hEpochDir hv1_call x pb hok hpost_env hch hv1_tight
      st0 st evs1 w0 h1 hst1 hc23 hc23_le hc23_suf hlen_bound hFit23 hpost hs0A
      hpc' hrun' hsp' htr' hx19' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'

/-! ## 4. Main Canonical Block-325 Entry Theorem -/

/-- Canonical Block `325` (`spqr::decode_state`) full execution from entry `+0` on
`x.st.bytes = encodeState pb` under `SpqrTightEvs (23 + v1Ops) 1307216 79236`. -/
theorem e2a_decodeState_entry_canonical_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {v1Ops : Nat} {V1Env : V1StateMergeGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2aEpochDirCanonicalOk A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)))
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    (x : DecodeStateGhost) (pb : PqRatchetState) (st0 : M.σ) (s0 : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs)
    (hbs : x.st.bytes = encodeState pb)
    (hok : spqrDecodeState x.st.bytes = .ok pb)
    (hvn : ∀ vn, pb.versionNegotiation = some vn → e2a_ValidVersionNegotiationPB vn)
    (hch : ∀ ch, pb.chain = some ch → e2a_ValidChainPB ch)
    (hv1_tight : ∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs)
    (hs0A : s0.spAligned = true)
    (hpc : s0.pc = decodeStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hx0 : s0.readReg64 .x0 = x.st.v)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st0 (SpqrTightEvs (23 + v1Ops) 1307216 79236))
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st0 s0 ∗
      stackAt s0.sp decodeStateStackX) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  refine e2a_entry_to_116_or_ret_cl x st0 s0 P R post hpost
    (hpost_env [] (SpqrTightEvs.nil (23 + v1Ops) 1307216 79236))
    hs0A hpc hrun hx8 hx0 hlen_bound hP ?_
  intro hbs_nil w0_scr s1 P1
    hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    hP1
  have hbs_decomp : x.st.bytes =
      encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 pb.versionNegotiation ++
      (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) := by
    rw [hbs, e2a_encodeState_decomp]
  have hFit123 : FitsEnv M lim st0
      (SpqrTightEvs (2 + (21 + v1Ops)) (1476 + (561525 + 731332)) (max 32 79236)) :=
    hFit.mono fun _ hevs => hevs.mono (by omega) (by decide) (by decide)
  have hcur0_le : x.st.bytes.length ≤ x.st.bytes.length := Nat.le_refl _
  have hcur0_suf : IsDropSuffix x.st.bytes x.st.bytes := by unfold IsDropSuffix; simp
  cases hvn_opt : pb.versionNegotiation with
  | none =>
    have hc1_nil :
        encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 pb.versionNegotiation = [] := by
      rw [hvn_opt]; rfl
    rw [hc1_nil, List.nil_append] at hbs_decomp
    have hc23_ne :
        encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner ≠ [] := by
      rw [← hbs_decomp]; exact hbs_nil
    have hc23_le :
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length ≤
          x.st.bytes.length := by
      rw [← hbs_decomp]
    have hc23_suf : IsDropSuffix x.st.bytes
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) := by
      rw [← hbs_decomp]; exact hcur0_suf
    have hFit23 : FitsEnv M lim st0 (SpqrTightEvs (21 + v1Ops) (561525 + 731332) 79236) :=
      e2a_fitsEnv_tight_split (SpqrTightEvs.nil 2 1476 32) hFit123
    have hP1' : P1 = ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes
          (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64)
          (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner).length
          ⟨pb.versionNegotiation, none, none⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st0 x s0 s1 := by
      rw [← hbs_decomp, hvn_opt]
      exact hP1
    exact e2a_stage23_at_116 hc hEpochDir hv1_call x pb hok hpost_env hch hv1_tight
      st0 st0 [] w0_scr (SpqrTightEvs.nil 2 1476 32) rfl
      hc23_ne hc23_le hc23_suf hlen_bound hFit23 hpost hs0A
      hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      hP1'
  | some vn =>
    have hcur_eq : x.st.bytes =
        encodeMessage VersionNegotiationPB.encodeRaw 1#32 vn ++
        (encodeOptMessage ChainPB.encodeRaw 2#32 pb.chain ++ e2a_innerBytes pb.inner) := by
      rw [hbs_decomp, hvn_opt]; rfl
    have hFit1 : FitsEnv M lim st0 (SpqrTightEvs 2 1476 32) :=
      hFit.mono fun _ hevs => hevs.mono (by omega) (by decide) (by decide)
    refine e2a_vn_outer_field1_cl_placed (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
      hc x st0 st0 w0_scr vn (hvn vn hvn_opt) none none
      hcur_eq hcur0_le hcur0_suf hlen_bound hFit1 hpost hs0A
      hpc1 hrun1 hsp1 htr1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      hP1 ?_
    intro evs1 sf P' h1 hc23_le hc23_suf
      hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
    have hst_eq : (⟨some vn, none, none⟩ : PqRatchetState) =
        ⟨pb.versionNegotiation, none, none⟩ := by
      rw [hvn_opt]
    rw [hst_eq] at hP'
    have hFit23 : FitsEnv M lim (M.stepEvents evs1 st0)
        (SpqrTightEvs (21 + v1Ops) (561525 + 731332) 79236) :=
      e2a_fitsEnv_tight_split h1 hFit123
    exact e2a_after_stage1_at_1576 hc hEpochDir hv1_call x pb hok hpost_env hch hv1_tight
      st0 (M.stepEvents evs1 st0) evs1 w0_scr h1 rfl hc23_le hc23_suf hlen_bound hFit23
      hpost hs0A
      hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudgetAux
