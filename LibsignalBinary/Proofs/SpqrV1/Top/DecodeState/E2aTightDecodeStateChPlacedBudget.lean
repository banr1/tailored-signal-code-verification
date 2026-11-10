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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudgetAux
import ProofLib.SepLogic.WPp

/-!
# Canonical Guarded-Tight `ChainPB` Outer Field-2 Verification (`Block 325`)

Defines canonical validity predicates (`e2a_ValidEpochDirPB`, `e2a_ValidChainEpochPB`,
`e2a_ValidChainPB`) and proves `e2a_ch_outer_field2_cl_placed`: outer Field 2 (`chain = some ch`)
steps `+116 -> +1576` under `SpqrTightEvs 21 561525 79236` while preserving `x27 = 8#64`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainEpochPB ChainPB EpochDirectionPB PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   epochDirectionMergeStack protoPqRatchetStateCapOkAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux (e2a_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)

/-! ## 1. Canonical Validity Predicates & Block-299 Seam (`E2aEpochDirCanonicalOk`) -/

def e2a_ValidEpochDirPB (maxPrev : Nat) (m : EpochDirectionPB) : Prop :=
  m.next.length ≤ 32 ∧ m.prev.length ≤ maxPrev

def e2a_ValidChainEpochPB (m : ChainEpochPB) : Prop :=
  (∀ d, m.send = some d → e2a_ValidEpochDirPB 0 d) ∧
  (∀ d, m.recv = some d → e2a_ValidEpochDirPB 79236 d)

def e2a_ValidChainPB (m : ChainPB) : Prop :=
  m.links.length ≤ 3 ∧ m.nextRoot.length ≤ 32 ∧ ∀ ep ∈ m.links, e2a_ValidChainEpochPB ep

def e2a_epochDirectionZeroCapAt (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  (∃∗ p1 : BitVec 64, vecU8At A a 0#64 p1 d.next) ∗
  (∃∗ p2 : BitVec 64, vecU8At A (a + 0x18#64) 0#64 p2 d.prev) ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4

def E2aEpochDirCanonicalOk [LibsignalPlacement] {M : AllocCostModel}
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
              codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
              (∃ pb rest, e2a_ValidEpochDirPB maxPrev pb ∧
                x.bs = e2a_lenPrefixed (EpochDirectionPB.encodeRaw pb) rest) ∧
              FitsEnv M lim st (SpqrTightEvs ops cum maxReq)⌝ ∗
            e2a_epochDirectionZeroCapAt A.repAlloc x.msgPtr x.msg ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
            A.pool lim st s ∗ stackAt s.sp epochDirectionMergeStack
          post := (epochDirectionMergeSpecOfEnv A lim
            (fun _ => SpqrTightEvs ops cum maxReq) (fun _ => SpqrTightEvs ops cum maxReq)).post })

/-! ## 2. Canonical Outer Field 2 (`PqRatchetState::chain`, `+116 -> +1576`) -/

/-- Canonical outer Field 2 (`PqRatchetState.chain = some ch`, `e2a_ValidChainPB ch`)
stepping from `+116` (`curSt = ⟨optVn, none, inner⟩`,
`cur = encodeMessage ChainPB.encodeRaw 2#32 ch ++ rest`) to `+1576`
(`curSt' = ⟨optVn, some ch, inner⟩`, `rest`), emitting `evs_ch` under
`SpqrTightEvs 21 561525 79236` and preserving `.x27 = 8#64`. -/
theorem e2a_ch_outer_field2_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2aEpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (hch : e2a_ValidChainPB ch)
    (inner : Option PqRatchetState.Inner)
    {cur rest : Bytes}
    (hcur_eq : cur = encodeMessage ChainPB.encodeRaw 2#32 ch ++ rest)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 21 561525 79236))
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
        ⟨optVn, none, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 21 561525 79236 evs_ch →
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  exact
    LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudgetAux.e2ar_ch_outer_field2_body_cl
      hc hEpochDir x st0 st w0 optVn ch hch.1 hch.2.1 hch.2.2 inner hcur_eq hcur_le hcur_suf
      hlen_bound hFit hpost hs0A hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
      hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget
