/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Basic-Block Step Lemmas for `encode<PolynomialEncoder> [local#3]` (Block `456`)

Defines budget-threaded placed contract propositions and proves `VmPreserved`-threaded basic-block
steppers on CLI Block `456` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchet.Prost (sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Poly (ProtoPolynomialEncoderGhost)
open CryptoVerification.SpqrV1.Auth (vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyEncoderElemsAt stackAt_msgEnc48_repeated)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPC_456 blkPl_456 lsProg_456)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
  (encodePolyEncoderPinnedSpec encodePolyEncoderPinnedSpecX
   encodePolyEncoderSpec encodePolyEncoderSpecX)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Budget-Threaded Placed Contract Propositions for Block `456` -/

def EncodePolyEncoder1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_456 H) (blkPl_456).base
    (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpec A lim))

def EncodePolyEncoder1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_456 H) (blkPl_456).base
    (withLsCodeLoaded lsmpl (encodePolyEncoderSpec A lim))

def EncodePolyEncoder1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_456 H) (blkPl_456).base
    (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecX A lim))

def EncodePolyEncoder1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_456 H) (blkPl_456).base
    (withLsCodeLoaded lsmpl (encodePolyEncoderSpecX A lim))

abbrev EncodePolyEncoder1PlacedPlacedOkX := @EncodePolyEncoder1PlacedOkX

def EncodePolyEncoder1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodePolyEncoder1PinnedPlacedOk A lim (Rust.withPanics ext)

def EncodePolyEncoder1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodePolyEncoder1PlacedOk A lim (Rust.withPanics ext)

def EncodePolyEncoder1PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodePolyEncoder1PinnedPlacedOkX A lim (Rust.withPanics ext)

def EncodePolyEncoder1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodePolyEncoder1PlacedOkX A lim (Rust.withPanics ext)

/-! ## 2. Relocatable `VmPreserved`-Threaded Step Lemmas for Block `456` (`lsProg_456 H`) -/

/-- Prologue (`+0x000..+0x014`, offsets `0..20`) on Block `456`:
allocates the 48-byte stack frame, saves `x29, x30, x21, x20, x19`, sets `x19 = v`,
and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prologue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (H : String → Option (State → State)) (encA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_456).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = (blkPl_456).base + 20#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 20#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv =>
        SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ sv3
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv)
            hvm)))

/-- Header tag push (`+0x028..+0x040`, offsets `40..64`) on Block `456`:
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, `lengthDelimited`) to `buf`,
sets `x0 = encA`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_push_hdr_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 64#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 64#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv =>
        SepWPp.weaken_pre
          (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv)
            hvm)))

/-- `mov x1, x19` at `+0x044..+0x048` (offsets `68..72`) on Block `456`, establishing `VmPreserved s sm`. -/
theorem step_polyEncoder_mov_x1_x19_68_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (val encA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 68#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 72#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 72#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv =>
        hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv)
          hvm))

/-- `idx` load and zero check (`+0x04c..+0x054`, offsets `76..84`) on Block `456`:
loads `w0 = [x20, #0x30]` (`pb.idx`), branches to `+128` if `pb.idx == 0#32`
else falls through to `+84`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_check_idx_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (encA v sp : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 76#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + (if pb.idx == 0#32 then 128#64 else 84#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP; dsimp only [polyEncoderElemsAt]
  cases hidx : (pb.idx == 0#32)
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hidx]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 84#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hidx]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 128#64)
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))

/-- `idx` tag push (`+0x064..+0x07c`, offsets `100..124`) on Block `456`:
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`,
sets `x1 = v`, preserves `x0 = pb.idx.zeroExtend 64`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_push_idx_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialEncoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 100#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 124#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 124#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv =>
        SepWPp.weaken_pre
          (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv)
            hvm)))

/-- `pts` argument setup (`+0x080..+0x08c`, offsets `128..140`) on Block `456`:
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 2#32`, `x3 = v`,
and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prep_pts_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (encA v sp : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 128#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 140#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg32 .x0 = 2#32 → sm.readReg64 .x1 = g.pts.ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → sm.readReg64 .x3 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP; dsimp only [polyEncoderElemsAt]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 140#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv =>
        SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv)
            hvm)))

/-- `polys` argument setup + frame restore (`+0x090..+0x0a8`, offsets `144..168`) on Block `456`:
loads `x1 = g.polys.ptr`, `x2 = BitVec.ofNat 64 pb.polys.length`, sets `w0 = 3#32`, `x3 = v`,
restores the 48-byte stack frame (`sp = sp`, `lr = s0.readReg64 .lr`) arriving at
`+168` (`b encode_repeated` tailcall), and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prep_polys_epilogue_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (encA v sp sv3 : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 144#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 168#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr → sm.readReg32 .x0 = 3#32 →
      sm.readReg64 .x1 = g.polys.ptr → sm.readReg64 .x2 = BitVec.ofNat 64 pb.polys.length →
      sm.readReg64 .x3 = v → CalleeSavedPreserved s0 sm → MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 168#64)
  by_vm_steps (
    wp_steps
    exact sepWP_done_tpidr_placed
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (fun hvm hinv1 =>
        SepWPp.weaken_pre
          (by dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by epochEncLen_cc_close)
            ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩
            hvm)))

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
