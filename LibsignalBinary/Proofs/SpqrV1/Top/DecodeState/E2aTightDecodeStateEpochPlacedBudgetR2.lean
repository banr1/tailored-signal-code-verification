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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChain
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Field
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import ProofLib.SepLogic.WPp

/-!
# Canonical Guarded-Tight `ChainEpochPB::merge` (`+600 -> +624`, Block `325`)

Proves `e2ar2_epoch_merge_tight_536f4`: canonical delimited `ChainEpochPB::merge` entry at `+600`
reaches `+624` under `SpqrTightEvs 6 183420 79236` (`send` `(2, 1476, 32)` + `recv`
`(4, 181944, 79236)`), parameterized over monotone outer state `V_state : Nat → SepProp`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateEpochPlacedBudgetR2

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainEpochPB EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeKey encodeMessage encodeOptMessage encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost EpochDirectionMergeGhost TraceVRegs V1InnerHeapPred
   bv_len_sub_limit chainEpochPBCapOkAt chainEpochPBCapOkAt_mono cmp_len_limit_of_eq
   cmp_len_limit_of_gt decodeStatePlacedEntry decodeStatePlacedProg
   epochDirectionMergeStack epochDirectionPBCapOkAt epochDirectionPB_default_eq
   key_and7_of_wt_some key_lsr3_32_eq key_lsr32_eq_zero_of_lt len_ult_of_ge
   optEpochDirectionPBCapOkAt optEpochDirectionPBCapOkAt_mono sp_sub_1392_aligned
   stackAt_of_callee stackAt_to_callee tag_cbz32_false tag_cbz64_false
   tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 vecU8At_nil_zero_one wt_setWidth8 wt_ult6)
open CryptoVerification.SpqrV1Sync.Codec
  (LoopsTo loopsTo_epochDirection mergeMessage_encode proto_encodeVarint_length)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
  (e2a_decodeKey_encodeKey e2a_decodeVarint2Env_eq_nil e2a_decodeVarint_lenPrefixed
   e2a_fitsEnv_decodeVarint2_of_some e2a_fitsEnv_tight_split e2a_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
  (chainEpochPBCapOkAt_eq optEpochDirectionPBCapOkAt_none optEpochDirectionPBCapOkAt_some
   optEpochDirectionPB_none_split48)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_decodeVarint2_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem pool_setMem_writeReg64 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (r : Reg) (v : BitVec 64) (m : Memory) :
    A.pool lim st ((s.writeReg64 r v).setMem m) = A.pool lim st (s.setMem m) := by
  have h : (s.writeReg64 r v).setMem m = (s.setMem m).writeReg64 r v := by cases s; cases r <;> rfl
  rw [h, RustCliAllocBudget.pool_writeReg64_norm]

private theorem pool_setMem_writeReg32 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (r : Reg) (v : BitVec 32) (m : Memory) :
    A.pool lim st ((s.writeReg32 r v).setMem m) = A.pool lim st (s.setMem m) := by
  have h : (s.writeReg32 r v).setMem m = (s.setMem m).writeReg32 r v := by cases s; cases r <;> rfl
  rw [h, RustCliAllocBudget.pool_writeReg32_norm]

private theorem pool_setMem_setPC {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) (m : Memory) :
    A.pool lim st ((s.setPC pc).setMem m) = A.pool lim st (s.setMem m) := by
  have h : (s.setPC pc).setMem m = (s.setMem m).setPC pc := by cases s; rfl
  rw [h, RustCliAllocBudget.pool_setPC_norm]

private theorem pool_setMem_setPState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ps : PState) (m : Memory) :
    A.pool lim st ((s.setPState ps).setMem m) = A.pool lim st (s.setMem m) := by
  have h : (s.setPState ps).setMem m = (s.setMem m).setPState ps := by cases s; rfl
  rw [h, RustCliAllocBudget.pool_setPState_norm]

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm,
    pool_setMem_writeReg64, pool_setMem_writeReg32, pool_setMem_setPC, pool_setMem_setPState])

theorem e2ar2_rebind_state [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ s' : State, s' = s → SepWPpIPlaced prog ret s' P Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  h s rfl

/-! ## 1. Canonical Validity Predicates, Wire Helpers, & Block-299 Seam -/

def e2ar2_ValidEpochDirPB (maxPrev : Nat) (m : EpochDirectionPB) : Prop :=
  m.next.length ≤ 32 ∧ m.prev.length ≤ maxPrev

def e2ar2_ValidChainEpochPB (m : ChainEpochPB) : Prop :=
  (∀ d, m.send = some d → e2ar2_ValidEpochDirPB 0 d) ∧
  (∀ d, m.recv = some d → e2ar2_ValidEpochDirPB 79236 d)

def e2ar2_epochDirectionZeroCapAt (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    SepProp :=
  (∃∗ p1 : BitVec 64, vecU8At A a 0#64 p1 d.next) ∗
  (∃∗ p2 : BitVec 64, vecU8At A (a + 0x18#64) 0#64 p2 d.prev) ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4

def E2ar2EpochDirCanonicalOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  ∀ (maxPrev ops cum maxReq : Nat),
    ((maxPrev = 0 ∧ ops = 2 ∧ cum = 1476 ∧ maxReq = 32) ∨
     (maxPrev = 79236 ∧ ops = 4 ∧ cum = 181944 ∧ maxReq = 79236)) →
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)) (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        { pre := fun (x, st) s =>
            ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
              s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
              x.bs.length < 2 ^ 63 ∧
              codecWireTypeToProto x.wt =
                CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited ∧
              x.msg = default ∧
              (∃ pb rest, e2ar2_ValidEpochDirPB maxPrev pb ∧
                x.bs = e2a_lenPrefixed (EpochDirectionPB.encodeRaw pb) rest) ∧
              FitsEnv M lim st (SpqrTightEvs ops cum maxReq)⌝ ∗
            e2ar2_epochDirectionZeroCapAt A.repAlloc x.msgPtr x.msg ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
            A.pool lim st s ∗ stackAt s.sp epochDirectionMergeStack
          post := (epochDirectionMergeSpecOfEnv A lim
            (fun _ => SpqrTightEvs ops cum maxReq) (fun _ => SpqrTightEvs ops cum maxReq)).post })

theorem e2ar2_encodeVarint_pos (v : BitVec 64) : 0 < (encodeVarint v).length :=
  (proto_encodeVarint_length v).1

theorem e2ar2_encodeKey_pos (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    0 < (encodeKey tag wt).length := by
  unfold encodeKey
  exact e2ar2_encodeVarint_pos _

theorem e2ar2_isDropSuffix_of_append {full pre suf : Bytes}
    (hle : (pre ++ suf).length ≤ full.length)
    (hsuf : IsDropSuffix full (pre ++ suf)) :
    suf.length ≤ full.length ∧ IsDropSuffix full suf := by
  have hsuf_le : suf.length ≤ (pre ++ suf).length := by simp
  refine ⟨Nat.le_trans hsuf_le hle, suffix_trans hle hsuf hsuf_le ?_⟩
  simp [IsDropSuffix, Nat.add_sub_cancel, List.drop_left]

theorem e2ar2_raw_lt_of_lenPrefixed_lt {raw rest : Bytes}
    (hlt : (e2a_lenPrefixed raw rest).length < 2 ^ 63) :
    raw.length < 2 ^ 64 := by
  unfold e2a_lenPrefixed at hlt
  simp only [List.length_append] at hlt
  omega

theorem e2ar2_encodeMessage_eq_key_lenPrefixed {N : Type} (encodeRaw : N → Bytes)
    (tag : BitVec 32) (n : N) (rest : Bytes) :
    encodeMessage encodeRaw tag n ++ rest =
      encodeKey tag .lengthDelimited ++ e2a_lenPrefixed (encodeRaw n) rest := by
  unfold encodeMessage e2a_lenPrefixed
  simp [List.append_assoc]

theorem e2ar2_encodeOptMessage_some {N : Type} (encodeRaw : N → Bytes)
    (tag : BitVec 32) (n : N) (rest : Bytes) :
    encodeOptMessage encodeRaw tag (some n) ++ rest =
      encodeKey tag .lengthDelimited ++ e2a_lenPrefixed (encodeRaw n) rest :=
  e2ar2_encodeMessage_eq_key_lenPrefixed encodeRaw tag n rest

theorem e2ar2_encodeOptMessage_none {N : Type} (encodeRaw : N → Bytes) (tag : BitVec 32) :
    encodeOptMessage encodeRaw tag none = [] :=
  rfl

theorem e2ar2_mergeMessage_lenPrefixed {N : Type}
    (mfN : CryptoVerification.SpqrV1Sync.Codec.MergeFieldFn N)
    (dN : Nat) (encodeRaw : N → Bytes) (n₀ n : N) (depth : Nat) (rest : Bytes)
    (hsub : LoopsTo mfN dN n₀ (encodeRaw n) n)
    (hlen : (encodeRaw n).length < 2 ^ 64) (hd : dN < depth) :
    (mergeMessage mfN .lengthDelimited n₀ (e2a_lenPrefixed (encodeRaw n) rest) depth).toOption =
      some (n, rest) := by
  unfold e2a_lenPrefixed
  rw [List.append_assoc, mergeMessage_encode mfN dN encodeRaw n₀ n depth rest hsub hlen hd]
  rfl

theorem e2ar2_mergeMessage_epochDirection_lenPrefixed (m : EpochDirectionPB)
    (rest : Bytes) (depth : Nat) (hd : 0 < depth)
    (hlt : (e2a_lenPrefixed (EpochDirectionPB.encodeRaw m) rest).length < 2 ^ 63) :
    (mergeMessage EpochDirectionPB.mergeField .lengthDelimited default
      (e2a_lenPrefixed (EpochDirectionPB.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar2_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar2_mergeMessage_lenPrefixed EpochDirectionPB.mergeField 0 EpochDirectionPB.encodeRaw
    default m depth rest (loopsTo_epochDirection m hlen) hlen hd

theorem e2ar2_epochDirectionZeroCapAt_default_init (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      ((a + 48#64) ↦₃₂ 0#32) ∗ memRegion (a + 52#64) 4 ⊢
    e2ar2_epochDirectionZeroCapAt A a default := by
  rw [epochDirectionPB_default_eq]
  unfold e2ar2_epochDirectionZeroCapAt
  dsimp only
  have h1 : (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ p1 : BitVec 64, vecU8At A a 0#64 p1 [] :=
    Entails.trans (vecU8At_nil_zero_one A a) (Entails.sepExists_right 1#64 (Entails.refl _))
  have h2 : ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      ∃∗ p2 : BitVec 64, vecU8At A (a + 0x18#64) 0#64 p2 [] := by
    have hb : a + 0x18#64 = a + 24#64 := by bv_omega
    have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
    have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
    rw [hb]
    have h2' := vecU8At_nil_zero_one A (a + 24#64)
    rw [ha1, ha2] at h2'
    exact Entails.trans h2' (Entails.sepExists_right 1#64 (Entails.refl _))
  have hc1 : a + 0x30#64 = a + 48#64 := by bv_omega
  have hc2 : a + 0x34#64 = a + 52#64 := by bv_omega
  rw [hc1, hc2]
  exact sepConj_mono h1 (sepConj_mono_left h2)

/-! ## 2. Canonical Zero-Cap Call Wrapper for `EpochDirectionPB::merge` (`Block 299`) -/

theorem e2ar2_call_epochDirectionMerge_canonical [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    {maxPrev ops cum maxReq : Nat}
    (hcase : (maxPrev = 0 ∧ ops = 2 ∧ cum = 1476 ∧ maxReq = 32) ∨
             (maxPrev = 79236 ∧ ops = 4 ∧ cum = 181944 ∧ maxReq = 79236))
    {ret ret_pc : BitVec 64}
    (msgPtr bufRef slot ptr : BitVec 64)
    (pb : EpochDirectionPB) (bs restAfter : Bytes) (st : M.σ)
    (hvalid : e2ar2_ValidEpochDirPB maxPrev pb)
    (hbs : bs = e2a_lenPrefixed (EpochDirectionPB.encodeRaw pb) restAfter)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 299)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (SpqrTightEvs ops cum maxReq))
    (hP : P = (e2ar2_epochDirectionZeroCapAt A.repAlloc msgPtr default ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (evs : List AllocEvent),
      SpqrTightEvs ops cum maxReq evs →
      restAfter.length ≤ bs.length → IsDropSuffix bs restAfter →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced (decodeStatePlacedProg ext) ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          epochDirectionPBCapOkAt A.repAlloc msgPtr restAfter.length pb ∗
          sliceCursorAfter slot ptr bs restAfter) ∗ F)
        Q Qp) :
    SepWPpIPlaced (decodeStatePlacedProg ext) ret s P Q Qp := by
  have hcall := hEpochDir maxPrev ops cum maxReq hcase
  have hm_ok :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto WireType.lengthDelimited)
        default bs 98).toOption = some (pb, restAfter) := by
    subst hbs
    exact e2ar2_mergeMessage_epochDirection_lenPrefixed pb restAfter 98 (by decide) hlen
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_ed : EpochDirectionMergeGhost :=
    ⟨WireType.lengthDelimited, msgPtr, default, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - epochDirectionMergeStack) ∗ F
  let spec :=
    ({ pre := fun (x : EpochDirectionMergeGhost × M.σ) s =>
          ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.1.wt.toNat ∧
            s.readReg64 .x1 = x.1.msgPtr ∧ s.readReg64 .x2 = x.1.bufRef ∧
            x.1.bs.length < 2 ^ 63 ∧
            codecWireTypeToProto x.1.wt =
              CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited ∧
            x.1.msg = default ∧
            (∃ pb rest, e2ar2_ValidEpochDirPB maxPrev pb ∧
              x.1.bs = e2a_lenPrefixed (EpochDirectionPB.encodeRaw pb) rest) ∧
            FitsEnv M lim x.2 (SpqrTightEvs ops cum maxReq)⌝ ∗
          e2ar2_epochDirectionZeroCapAt A.repAlloc x.1.msgPtr x.1.msg ∗
          (x.1.bufRef ↦₆₄ x.1.slot) ∗ sliceCursorAt x.1.slot x.1.ptr x.1.bs ∗
          A.pool lim x.2 s ∗ stackAt s.sp epochDirectionMergeStack
       post := (epochDirectionMergeSpecOfEnv A lim
          (fun _ => SpqrTightEvs ops cum maxReq)
          (fun _ => SpqrTightEvs ops cum maxReq)).post } :
      Spec (EpochDirectionMergeGhost × M.σ))
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre (x_ed, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded, spec, x_ed]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, rfl, rfl, ⟨pb, restAfter, hvalid, hbs⟩, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur epochDirectionMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  dsimp only [decodeStatePlacedProg] at hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_ed, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ spec.post (x_ed, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [spec, epochDirectionMergeSpecOfEnv, x_ed] at hpost
    rw [hsp, hm_ok] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜SpqrTightEvs ops cum maxReq evs⌝ ∗
        (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - epochDirectionMergeStack) ∗
              stackAt sp_cur epochDirectionMergeStack) ∗
            epochDirectionPBCapOkAt A.repAlloc msgPtr restAfter.length pb ∗
            sliceCursorAfter slot ptr bs restAfter) ∗ F) ∗ R')) := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
    have hbs_split :
        bs = (encodeVarint (BitVec.ofNat 64 (EpochDirectionPB.encodeRaw pb).length) ++
          EpochDirectionPB.encodeRaw pb) ++ restAfter := by
      rw [hbs]
    have ⟨hle, hsuf⟩ := e2ar2_isDropSuffix_of_append
      (full := bs)
      (pre := encodeVarint (BitVec.ofNat 64 (EpochDirectionPB.encodeRaw pb).length) ++
        EpochDirectionPB.encodeRaw pb)
      (suf := restAfter)
      (by rw [← hbs_split])
      (by rw [← hbs_split]; simp [IsDropSuffix])
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm evs hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
        (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [spec, epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [spec, epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [spec, epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## 3. Canonical `ChainEpochPB` Field Key Step (`+984 -> +1036`) -/

theorem e2ar2_epoch_step_key_984 [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ops cum maxReq : Nat}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (V_state : Nat → SepProp) (hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2)
    (curEpoch : ChainEpochPB)
    (tag limitEpoch : Nat) (htag_lo : 1 ≤ tag) (htag_hi : tag ≤ 2)
    (cur rest1 : Bytes)
    (hcur_eq : cur = encodeKey (BitVec.ofNat 32 tag) .lengthDelimited ++ rest1)
    (hlim_le : limitEpoch ≤ rest1.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs ops cum maxReq))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      V_state cur.length ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (sf : State) (P' : SepProp),
      rest1.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 1036#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      sf.readReg64 .x1 = BitVec.ofNat 64 tag →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
        V_state rest1.length ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hcur_eq
  let cur := encodeKey (BitVec.ofNat 32 tag) .lengthDelimited ++ rest1
  change cur.length ≤ x.st.bytes.length at hcur_le
  change IsDropSuffix x.st.bytes cur at hcur_suf
  have htag32_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdk := e2a_decodeKey_encodeKey (BitVec.ofNat 32 tag) .lengthDelimited rest1
    (by rw [htag32_toNat]; exact htag_lo) (by rw [htag32_toNat]; omega)
  let key : BitVec 64 := (((BitVec.ofNat 32 tag) <<< 3) |||
    (CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited).toU32).zeroExtend 64
  rcases hdk with ⟨hdv_key, hkey_nat, hk_lt, hwt_some, hdiv_tag, htag_ge1⟩
  change decodeVarint cur = some (key, rest1) at hdv_key
  rw [htag32_toNat] at hkey_nat hdiv_tag
  have hk_pos := e2ar2_encodeKey_pos (BitVec.ofNat 32 tag) .lengthDelimited
  have hlt_r1 : rest1.length < cur.length := by
    dsimp only [cur]
    rw [List.length_append]
    omega
  have hgt : ¬ cur.length ≤ limitEpoch := by omega
  have ⟨hult, hule⟩ := cmp_len_limit_of_gt hgt (by omega)
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 996#64)
  wp_steps 3
  have hcur_fold :
      ((s0.sp - 1056#64) ↦₆₄ (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length))) ∗
        ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
        (x.st.ptr ↦ₛ x.st.bytes) ⊢
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur := by
    dsimp only [sliceCursorAfter]
    have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
    rw [hsp1048]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.fold hcur_fold (by sep_focus) ?_
  apply SepWP.done
    (by dsimp only [cur] at hult hule; simp only [wp_norm, arm64_norm, hult, hule, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hdv_call := hc.decodeVarint2
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStateLoopCommonPlaced] at hdv_call ⊢
  refine e2ar2_rebind_state fun s_step hs_step => ?_
  have hpool_eq : A.pool lim st s = A.pool lim st s_step := by rw [hs_step]; pool_reg_norm
  rw [hpool_eq]; subst hs_step
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps 2
  apply SepWP.done
    (by dsimp only [cur] at hult hule; simp only [wp_norm, arm64_norm, hult, hule, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur st
    (ret_pc := (blkPl_325).base + 1004#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := e2a_fitsEnv_decodeVarint2_of_some hdv_key hFit)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 key' rest1' evs_dv hdv hevs_dv hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
    have hevs_nil := e2a_decodeVarint2Env_eq_nil hdv_key hevs_dv
    subst hevs_nil
    rw [hdv_key] at hdv
    injection hdv with hpair
    injection hpair with hkey_eq hrest_eq
    subst hkey_eq hrest_eq
    simp only [M.stepEvents_nil]
    have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
    have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
    have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
    simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk_lt
    change WireType.ofNat? (key.toNat % 8) = some WireType.lengthDelimited at hwt_some
    have hand7 : key &&& 7#64 = BitVec.ofNat 64 WireType.lengthDelimited.toNat :=
      key_and7_of_wt_some hwt_some
    have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 WireType.lengthDelimited
    have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 tag := by
      rw [← hdiv_tag]
      exact key_lsr3_32_eq hk_lt
    have htag29 : tag < 2 ^ 29 := by omega
    have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 tag) = BitVec.ofNat 64 tag :=
      tag_zeroExtend64_ofNat32 htag29
    have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 tag) = BitVec.ofNat 32 tag :=
      tag_setWidth32_ofNat tag
    have hcbz64 := tag_cbz64_false htag_lo htag29
    have hcbz32 := tag_cbz32_false htag_lo htag29
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1036#64)
    wp_steps 8
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hcur_le hcur_suf hle1) (by sep_focus) ?_
    refine SepWP.fold (hV_mono hle1) (by sep_focus) ?_
    refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 688#64)
      (rem1 := cur.length) (rem2 := rest1.length) (ep := curEpoch) hle1) (by sep_focus) ?_
    apply SepWP.done
      (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze,
            htw32, hcbz64, hcbz32])
      (by simp only [arm64_norm, hrun1])
    exact hnext _ _ hrest1_le hrest1_suf
      (by dsimp only [decodeStatePlacedEntry]
          simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze,
            htw32, hcbz64, hcbz32])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, hx0_0, hx1_key, hand7])
      (by simp only [arm64_norm, hx1_key, hlsr3, hze])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
  · intro _ _ hdv
    rw [hdv_key] at hdv
    cases hdv

/-! ## 4. Optional `send` (Tag 1) & `recv` (Tag 2) Steps (`+984 -> +984`) -/

theorem e2ar2_epoch_send_opt [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (V_state : Nat → SepProp) (hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2)
    (optSend : Option EpochDirectionPB)
    (hvalid : ∀ d, optSend = some d → e2ar2_ValidEpochDirPB 0 d)
    (limitEpoch : Nat) (cur restMid : Bytes)
    (hcur_eq : cur = encodeOptMessage EpochDirectionPB.encodeRaw 1#32 optSend ++ restMid)
    (hlim_le : limitEpoch ≤ restMid.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      V_state cur.length ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length ⟨none, none⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_send : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 2 1476 32 evs_send →
      restMid.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes restMid →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restMid ∗
        V_state restMid.length ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restMid.length ⟨optSend, none⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_send st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  rcases optSend with _ | d
  · rw [e2ar2_encodeOptMessage_none, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone [] s P (SpqrTightEvs.nil 2 1476 32) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [M.stepEvents_nil]; exact hP)
  · have hd_valid : e2ar2_ValidEpochDirPB 0 d := hvalid d rfl
    rw [e2ar2_encodeOptMessage_some] at hcur_eq
    let rest1 := e2a_lenPrefixed (EpochDirectionPB.encodeRaw d) restMid
    have hlim_le1 : limitEpoch ≤ rest1.length := by
      dsimp only [rest1]
      unfold e2a_lenPrefixed
      simp only [List.length_append]
      omega
    refine e2ar2_epoch_step_key_984 (v20 := v20) hc x st0 st V_state hV_mono ⟨none, none⟩
      1 limitEpoch (by decide) (by decide) cur rest1
      hcur_eq hlim_le1 hcur_le hcur_suf hlen_bound hFit
      s0 s P R post hpost hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro s1 P1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hwt8 := wt_setWidth8 WireType.lengthDelimited
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1108#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    refine e2ar2_rebind_state fun s2 hs2 => ?_
    have hpool2 : A.pool lim st s1 = A.pool lim st s2 := by
      rw [hs2]; pool_reg_norm
    have hpc2 : s2.pc = (blkPl_325).base + 1108#64 := by rw [hs2]; simp only [arm64_norm, hx1_1]
    have hrun2 : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, hrun1]
    have hsp2 : s2.sp = s0.sp - 1392#64 := by rw [hs2]; simp only [arm64_norm, hsp1]
    have htr2 : TraceVRegs s2 s0 := by rw [hs2]; simp only [arm64_norm, htr1]
    have hx0_2 : (s2.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat := by
      rw [hs2]; simp only [arm64_norm, hx0_1, hwt8]
    have hx19_2 : s2.readReg64 .x19 = x.outPtr := by rw [hs2]; simp only [arm64_norm, hx19_1]
    have hx20_2 : s2.readReg64 .x20 = v20 := by rw [hs2]; simp only [arm64_norm, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = 0x8000000000000006#64 := by
      rw [hs2]; simp only [arm64_norm, hx21_1]
    have hx22_2 : s2.readReg64 .x22 = s0.sp - 1040#64 := by
      rw [hs2]; simp only [arm64_norm, hx22_1]
    have hx23_2 : s2.readReg64 .x23 = -1#64 := by rw [hs2]; simp only [arm64_norm, hx23_1]
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 912#64 := by
      rw [hs2]; simp only [arm64_norm, hx24_1]
    have hx25_2 : s2.readReg64 .x25 = s0.sp - 688#64 := by
      rw [hs2]; simp only [arm64_norm, hx25_1]
    have hx26_2 : s2.readReg64 .x26 = -2#64 := by rw [hs2]; simp only [arm64_norm, hx26_1]
    have hx27_2 : s2.readReg64 .x27 = BitVec.ofNat 64 limitEpoch := by
      rw [hs2]; simp only [arm64_norm, hx27_1]
    have hx28_2 : s2.readReg64 .x28 = 1#64 := by rw [hs2]; simp only [arm64_norm, hx28_1]
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := by rw [hs2]; simp only [arm64_norm, hx29_1]
    have hspA2 : s2.spAligned = true := by rw [State.spAligned, hsp2]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStateLoopCommonPlaced]
    rw [hpool2]; clear hs2 hpool2
    rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1144#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 688#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps_sync_pool ((blkPl_325).base + 1144#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold
      (e2ar2_epochDirectionZeroCapAt_default_init A.repAlloc (s0.sp - 688#64))
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    pool_reg_norm
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
    wp_steps 3
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    have hsp2c0 : s0.sp - 1392#64 + 704#64 = s0.sp - 688#64 := by bv_omega
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine e2ar2_call_epochDirectionMerge_canonical hEpochDir
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      (s0.sp - 688#64) (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
      d rest1 restMid st hd_valid rfl
      (ret_pc := (blkPl_325).base + 1156#64)
      (hpc := by simp only [wp_norm, arm64_norm])
      (hrun := by simp only [wp_norm, arm64_norm, hrun2])
      (hsp := by simp only [wp_norm, arm64_norm, hsp2])
      (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm])
      (htr := by simp only [wp_norm, arm64_norm] at htr2 ⊢; exact htr2)
      (hx0 := by simp only [wp_norm, arm64_norm] at hx0_2 ⊢; exact hx0_2)
      (hx1 := by simp only [wp_norm, arm64_norm, hsp2, hsp2c0])
      (hx2 := by
        have hx29' := hx29_2
        simp only [wp_norm, arm64_norm] at hx29'
        simp only [wp_norm, arm64_norm, hx29', hx29_f0])
      (hlen := by omega)
      (hfits := hFit)
      (hP := by pool_reg_norm; sep_focus) ?_
    intro s4 evs_ed hevs_ed hle2 hsuf2 hpc4 hrun4 hsp4 htr4 hcs4 hx0_0
    have hrestMid_le : restMid.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
    have hrestMid_suf : IsDropSuffix x.st.bytes restMid := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4,
      hx28_4, hx29_4, hvregs_4⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4
    simp only [arm64_norm, wp_norm] at hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (hV_mono hle2) (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 632#64)
      (rem1 := rest1.length) (rem2 := restMid.length) (opt := none) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_0]) (by simp only [arm64_norm, hrun4])
    exact hdone evs_ed _ _ hevs_ed hrestMid_le hrestMid_suf
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0])
      (by simp only [arm64_norm, hrun4]) (by simp only [arm64_norm, hsp4])
      (by simp only [arm64_norm, htr4])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)

theorem e2ar2_epoch_recv_opt [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (V_state : Nat → SepProp) (hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2)
    (optSend optRecv : Option EpochDirectionPB)
    (hvalid : ∀ d, optRecv = some d → e2ar2_ValidEpochDirPB 79236 d)
    (limitEpoch : Nat) (cur restAfter : Bytes)
    (hcur_eq : cur = encodeOptMessage EpochDirectionPB.encodeRaw 2#32 optRecv ++ restAfter)
    (hlim_le : limitEpoch ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 4 181944 79236))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      V_state cur.length ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length ⟨optSend, none⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_recv : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 4 181944 79236 evs_recv →
      restAfter.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        V_state restAfter.length ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restAfter.length ⟨optSend, optRecv⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_recv st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  rcases optRecv with _ | d
  · rw [e2ar2_encodeOptMessage_none, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone [] s P (SpqrTightEvs.nil 4 181944 79236) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [M.stepEvents_nil]; exact hP)
  · have hd_valid : e2ar2_ValidEpochDirPB 79236 d := hvalid d rfl
    rw [e2ar2_encodeOptMessage_some] at hcur_eq
    let rest1 := e2a_lenPrefixed (EpochDirectionPB.encodeRaw d) restAfter
    have hlim_le1 : limitEpoch ≤ rest1.length := by
      dsimp only [rest1]
      unfold e2a_lenPrefixed
      simp only [List.length_append]
      omega
    refine e2ar2_epoch_step_key_984 (v20 := v20) hc x st0 st V_state hV_mono ⟨optSend, none⟩
      2 limitEpoch (by decide) (by decide) cur rest1
      hcur_eq hlim_le1 hcur_le hcur_suf hlen_bound hFit
      s0 s P R post hpost hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro s1 P1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hwt8 := wt_setWidth8 WireType.lengthDelimited
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1052#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    refine e2ar2_rebind_state fun s2 hs2 => ?_
    have hpool2 : A.pool lim st s1 = A.pool lim st s2 := by
      rw [hs2]; pool_reg_norm
    have hpc2 : s2.pc = (blkPl_325).base + 1052#64 := by rw [hs2]; simp only [arm64_norm, hx1_1]
    have hrun2 : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, hrun1]
    have hsp2 : s2.sp = s0.sp - 1392#64 := by rw [hs2]; simp only [arm64_norm, hsp1]
    have htr2 : TraceVRegs s2 s0 := by rw [hs2]; simp only [arm64_norm, htr1]
    have hx0_2 : (s2.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat := by
      rw [hs2]; simp only [arm64_norm, hx0_1, hwt8]
    have hx19_2 : s2.readReg64 .x19 = x.outPtr := by rw [hs2]; simp only [arm64_norm, hx19_1]
    have hx20_2 : s2.readReg64 .x20 = v20 := by rw [hs2]; simp only [arm64_norm, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = 0x8000000000000006#64 := by
      rw [hs2]; simp only [arm64_norm, hx21_1]
    have hx22_2 : s2.readReg64 .x22 = s0.sp - 1040#64 := by
      rw [hs2]; simp only [arm64_norm, hx22_1]
    have hx23_2 : s2.readReg64 .x23 = -1#64 := by rw [hs2]; simp only [arm64_norm, hx23_1]
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 912#64 := by
      rw [hs2]; simp only [arm64_norm, hx24_1]
    have hx25_2 : s2.readReg64 .x25 = s0.sp - 688#64 := by
      rw [hs2]; simp only [arm64_norm, hx25_1]
    have hx26_2 : s2.readReg64 .x26 = -2#64 := by rw [hs2]; simp only [arm64_norm, hx26_1]
    have hx27_2 : s2.readReg64 .x27 = BitVec.ofNat 64 limitEpoch := by
      rw [hs2]; simp only [arm64_norm, hx27_1]
    have hx28_2 : s2.readReg64 .x28 = 1#64 := by rw [hs2]; simp only [arm64_norm, hx28_1]
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := by rw [hs2]; simp only [arm64_norm, hx29_1]
    have hspA2 : s2.spAligned = true := by rw [State.spAligned, hsp2]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStateLoopCommonPlaced]
    rw [hpool2]; clear hs2 hpool2
    rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1088#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 632#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps_sync_pool ((blkPl_325).base + 1088#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold
      (e2ar2_epochDirectionZeroCapAt_default_init A.repAlloc (s0.sp - 632#64))
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    pool_reg_norm
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
    wp_steps 3
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    have hx25_38 : s0.sp - 688#64 + 56#64 = s0.sp - 632#64 := by bv_omega
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine e2ar2_call_epochDirectionMerge_canonical hEpochDir
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
      (s0.sp - 632#64) (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
      d rest1 restAfter st hd_valid rfl
      (ret_pc := (blkPl_325).base + 1100#64)
      (hpc := by simp only [wp_norm, arm64_norm])
      (hrun := by simp only [wp_norm, arm64_norm, hrun2])
      (hsp := by simp only [wp_norm, arm64_norm, hsp2])
      (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm])
      (htr := by simp only [wp_norm, arm64_norm] at htr2 ⊢; exact htr2)
      (hx0 := by simp only [wp_norm, arm64_norm] at hx0_2 ⊢; exact hx0_2)
      (hx1 := by
        have hx25' := hx25_2
        simp only [wp_norm, arm64_norm] at hx25'
        simp only [wp_norm, arm64_norm, hx25', hx25_38])
      (hx2 := by
        have hx29' := hx29_2
        simp only [wp_norm, arm64_norm] at hx29'
        simp only [wp_norm, arm64_norm, hx29', hx29_f0])
      (hlen := by omega)
      (hfits := hFit)
      (hP := by pool_reg_norm; sep_focus) ?_
    intro s4 evs_ed hevs_ed hle2 hsuf2 hpc4 hrun4 hsp4 htr4 hcs4 hx0_0
    have hrestAfter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
    have hrestAfter_suf : IsDropSuffix x.st.bytes restAfter :=
      suffix_trans hrest1_le hrest1_suf hle2 hsuf2
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4,
      hx28_4, hx29_4, hvregs_4⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4
    simp only [arm64_norm, wp_norm] at hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (hV_mono hle2) (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 688#64)
      (rem1 := rest1.length) (rem2 := restAfter.length) (opt := optSend) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_0]) (by simp only [arm64_norm, hrun4])
    exact hdone evs_ed _ _ hevs_ed hrestAfter_le hrestAfter_suf
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0])
      (by simp only [arm64_norm, hrun4]) (by simp only [arm64_norm, hsp4])
      (by simp only [arm64_norm, htr4])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)

/-! ## 5. Delimited `ChainEpochPB::merge` Entry (`+600 -> +624`) under `SpqrTightEvs 6 183420 79236` -/

private theorem e2ar2_epoch_scratch_split_recv_240 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      ∃∗ w_recv : BitVec 64,
        memRegion (sp - 680#64) 48 ∗
        ((sp - 632#64) ↦₆₄ w_recv) ∗
        memRegion (sp - 624#64) 48 ∗
        memRegion (sp - 576#64) 240 := by
  have hs1 := ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
    (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 288)
    (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have hs3 := ProofLib.memRegion_split' (b := sp - 624#64) (n := 48) (k := 240)
    (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  have hj := ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
    (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  rw [hs1, hs2, hs3, ProofLib.memRegion_eight (sp - 632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_recv
  refine Entails.sepExists_right w_recv ?_
  rw [hj]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2ar2_chainEpochPBCapOkAt_default_init (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) :
    ((sp - 688#64) ↦₆₄ -1#64) ∗ memRegion (sp - 680#64) 48 ∗
      ((sp - 632#64) ↦₆₄ -1#64) ∗ memRegion (sp - 624#64) 48 ⊢
      chainEpochPBCapOkAt A (sp - 688#64) remLen default := by
  rw [show (default : ChainEpochPB) = { send := none, recv := none } from rfl,
    chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none, optEpochDirectionPBCapOkAt_none]
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 632#64 + 8#64 = sp - 624#64 := by bv_omega
  have hnc : (-1#64 : BitVec 64) = noneCap := rfl
  rw [ha1, ha2, hnc]
  exact Entails.of_eq (by sep_ac_rfl)

theorem e2ar2_epoch_merge_tight_536f4 [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (V_state : Nat → SepProp) (hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2)
    (ep : ChainEpochPB) (hep : e2ar2_ValidChainEpochPB ep)
    (rest1 restAfter : Bytes)
    (hrest1_eq : rest1 = e2a_lenPrefixed (ChainEpochPB.encodeRaw ep) restAfter)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 6 183420 79236))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      V_state rest1.length ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_em : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 6 183420 79236 evs_em →
      restAfter.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 624#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        V_state restAfter.length ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restAfter.length ep ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  have hraw_lt : (ChainEpochPB.encodeRaw ep).length < 2 ^ 64 := by
    subst hrest1_eq
    unfold e2a_lenPrefixed at hrest1_le
    simp only [List.length_append] at hrest1_le
    omega
  obtain ⟨hdv_canon, hlen64_nat⟩ :=
    e2a_decodeVarint_lenPrefixed (raw := ChainEpochPB.encodeRaw ep) (rest := restAfter) hraw_lt
  rw [← hrest1_eq] at hdv_canon
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  refine SepWP.fold (e2ar2_epoch_scratch_split_recv_240 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (e2ar2_chainEpochPBCapOkAt_default_init A.repAlloc s0.sp rest1.length)
    (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 616#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := e2a_fitsEnv_decodeVarint2_of_some hdv_canon hFit)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 len64 rest2 evs_dv hdv hevs_dv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_len
    have hevs_nil := e2a_decodeVarint2Env_eq_nil hdv_canon hevs_dv
    subst hevs_nil
    rw [hdv_canon] at hdv
    injection hdv with hpair
    injection hpair with hlen_eq hrest2_eq
    subst hlen_eq hrest2_eq
    simp only [M.stepEvents_nil]
    let rest2 := ChainEpochPB.encodeRaw ep ++ restAfter
    change rest2.length < rest1.length at hlt2
    change IsDropSuffix rest1 rest2 at hsuf2
    have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
    have hrest2_le : rest2.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
    have hrest2_suf : IsDropSuffix x.st.bytes rest2 := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
    simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hlt_len : ¬ rest2.length < (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length).toNat := by
      rw [hlen64_nat]
      dsimp only [rest2]
      rw [List.length_append]
      omega
    have hlim_eq :
        rest2.length - (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length).toNat =
          restAfter.length := by
      rw [hlen64_nat]
      dsimp only [rest2]
      rw [List.length_append, Nat.add_sub_cancel_left]
    have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
    have hsub_lim := bv_len_sub_limit hlt_len
    rw [hlim_eq] at hsub_lim
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    dsimp only [sliceCursorAfter]
    wp_steps 4
    refine SepWP.fold (hV_mono hle2) (by sep_focus) ?_
    refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A.repAlloc)
      (a := s0.sp - 688#64) (rem1 := rest1.length) (rem2 := rest2.length)
      (ep := default) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
      (by simp only [arm64_norm, hrun1])
    let restMid := encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv ++ restAfter
    have hrest2_split :
        rest2 = encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send ++ restMid := by
      dsimp only [rest2, restMid]
      unfold ChainEpochPB.encodeRaw
      rw [List.append_assoc]
    have hlim_mid : restAfter.length ≤ restMid.length := by
      dsimp only [restMid]
      simp
    have hFit_send : FitsEnv M lim st (SpqrTightEvs 2 1476 32) :=
      hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
    refine e2ar2_epoch_send_opt (v20 := v20) hc hEpochDir x st0 st V_state hV_mono
      ep.send hep.1 restAfter.length rest2 restMid hrest2_split hlim_mid hrest2_le hrest2_suf
      hlen_bound hFit_send s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsub_lim, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by
        show _ = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
          V_state rest2.length ∗
          chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length default ∗
          memRegion (s0.sp - 576#64) 240 ∗ _
        dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]
        rw [hsp1048]
        pool_reg_norm
        sep_ac_rfl) ?_
    intro evs_send s_mid P_mid hevs_send hmid_le hmid_suf
      hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m
      hx27_m hx28_m hx29_m hP_mid
    have hFit_recv : FitsEnv M lim (M.stepEvents evs_send st) (SpqrTightEvs 4 181944 79236) :=
      e2a_fitsEnv_tight_split hevs_send hFit
    refine e2ar2_epoch_recv_opt (v20 := v20) hc hEpochDir x st0 (M.stepEvents evs_send st)
      V_state hV_mono ep.send ep.recv hep.2 restAfter.length restMid restAfter rfl
      (Nat.le_refl _) hmid_le hmid_suf hlen_bound hFit_recv s0 s_mid P_mid R post hpost hs0A
      hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m
      hx27_m hx28_m hx29_m hP_mid ?_
    intro evs_recv s_end P_end hevs_recv hafter_le hafter_suf
      hpc_e hrun_e hsp_e htr_e hx19_e hx20_e hx21_e hx22_e hx23_e hx24_e hx25_e hx26_e
      hx27_e hx28_e hx29_e hP_end
    subst hP_end
    have hep_eq : (⟨ep.send, ep.recv⟩ : ChainEpochPB) = ep := by cases ep; rfl
    rw [hep_eq]
    have ⟨hult_eq, hule_eq, hbeq_eq⟩ := cmp_len_limit_of_eq (rfl : restAfter.length = restAfter.length)
    dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc_e ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 624#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hult_eq, hule_eq, hbeq_eq])
      (by simp only [arm64_norm, hrun_e])
    have hevs_ep : SpqrTightEvs 6 183420 79236 (evs_send ++ evs_recv) :=
      hevs_send.append hevs_recv
    exact hdone (evs_send ++ evs_recv) _ _ hevs_ep hafter_le hafter_suf
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult_eq, hule_eq, hbeq_eq])
      (by simp only [arm64_norm, hrun_e]) (by simp only [arm64_norm, hsp_e])
      (by simp only [arm64_norm, htr_e])
      (by simp only [arm64_norm, hx19_e]) (by simp only [arm64_norm, hx20_e])
      (by simp only [arm64_norm, hx21_e]) (by simp only [arm64_norm, hx22_e])
      (by simp only [arm64_norm, hx23_e]) (by simp only [arm64_norm, hx24_e])
      (by simp only [arm64_norm, hx25_e]) (by simp only [arm64_norm, hx26_e])
      (by simp only [arm64_norm, hx28_e]) (by simp only [arm64_norm, hx29_e])
      (by
        rw [M.stepEvents_append]
        dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
        pool_reg_norm)
  · intro _ _ hdv
    rw [hdv_canon] at hdv
    cases hdv

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateEpochPlacedBudgetR2
