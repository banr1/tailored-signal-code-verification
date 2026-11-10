/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications and Call Helpers for `encode_repeated`

Defines deterministic multi-byte `Vec<u8>` growth transitions (`reserveStep`, `pushBytesStep`,
`encodeRepeatedStep`), `VecU8ReserveChain` bridges, `encodeVarintDetSpecOf`,
`encodeRepeatedSpecOf`, and generic call steppers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeBytesField)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedStackOf repeatedBytesSliceAt
   encodeRepeatedBytes encodeRepeatedBytes_cons
   encodeBytesField_some_length encodeKey_lengthDelimited_eq
   stackAt_encodeVarint_eq_doReserve sp_sub_80_aligned
   EncRepeatedCalleeSaved withEncRepeatedCS)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep encodeVarintEvents EncodeVarintEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (sepWPp_call_cs_noPanic encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
  (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_one_eq_pushByteStep reserveStep_of_spare reserveStep_of_need
   reserveStep_of_need_doReserveEvents reserveStep_fst_ge
   pushBytesStep pushBytesStep_snd_eq pushBytesStep_of_spare
   encodeRepeatedElemStep encodeRepeatedStep encodeRepeatedElemStep_of_spare
   encodeRepeatedStep_of_spare)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep pushBytesStep encodeRepeatedElemStep encodeRepeatedStep)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8ReserveChain VecU8EncodeEnv vecU8ReserveCap)

/-! ## Deterministic `reserveStep`, `pushBytesStep`, and `encodeRepeatedStep` -/

theorem reserveStep_fst_ge_need (cap len additional : Nat) :
    len + additional ≤ (reserveStep cap len additional).1 := by
  unfold reserveStep
  split_ifs with h <;> simp only [reserveCap] <;> omega

theorem pushByteStep_fst_ge (cap len : Nat) :
    cap ≤ (pushByteStep cap len).1 := by
  rw [← reserveStep_one_eq_pushByteStep]
  exact reserveStep_fst_ge cap len 1

theorem pushBytesStep_fst_ge :
    ∀ (n cap len : Nat), cap ≤ (pushBytesStep n cap len).1
  | 0, _, _ => Nat.le_refl _
  | n + 1, cap, len =>
    Nat.le_trans (pushByteStep_fst_ge cap len)
      (pushBytesStep_fst_ge n (pushByteStep cap len).1 (len + 1))

theorem pushBytesStep_add :
    ∀ (m n cap len : Nat),
      pushBytesStep (m + n) cap len =
        let s1 := pushBytesStep m cap len
        let s2 := pushBytesStep n s1.1 (len + m)
        (s2.1, s1.2 ++ s2.2)
  | 0, n, cap, len => by
    simp only [Nat.zero_add, Nat.add_zero, pushBytesStep, List.nil_append]
  | m + 1, n, cap, len => by
    rw [Nat.succ_add]
    simp only [pushBytesStep]
    rw [pushBytesStep_add m n (pushByteStep cap len).1 (len + 1)]
    have hlen : len + 1 + m = len + (m + 1) := by omega
    simp only [hlen, List.append_assoc]

theorem encodeRepeatedElemStep_fst_ge (tag cap len : Nat) (elemBs : List (BitVec 8)) :
    cap ≤ (encodeRepeatedElemStep tag cap len elemBs).1 := by
  dsimp only [encodeRepeatedElemStep]
  exact Nat.le_trans (pushBytesStep_fst_ge _ _ _)
    (Nat.le_trans (pushBytesStep_fst_ge _ _ _) (reserveStep_fst_ge _ _ _))

theorem encodeRepeatedStep_fst_ge (tag : Nat) :
    ∀ (cap len : Nat) (elems : List (List (BitVec 8))),
      cap ≤ (encodeRepeatedStep tag cap len elems).1
  | _, _, [] => Nat.le_refl _
  | cap, len, elemBs :: rest =>
    Nat.le_trans (encodeRepeatedElemStep_fst_ge tag cap len elemBs)
      (encodeRepeatedStep_fst_ge tag _ _ rest)

/-- Deterministic `AllocEvent` list emitted by `encode_repeated` on `x`. -/
def encodeRepeatedEvents (x : EncodeRepeatedGhost) : List AllocEvent :=
  (encodeRepeatedStep x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd)).2

def EncodeRepeatedEnv (x : EncodeRepeatedGhost) (evs : List AllocEvent) : Prop :=
  evs = encodeRepeatedEvents x

theorem encodeRepeatedEnv_events (x : EncodeRepeatedGhost) :
    EncodeRepeatedEnv x (encodeRepeatedEvents x) := rfl

theorem encodeRepeatedEvents_of_spare {x : EncodeRepeatedGhost}
    (h : x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat) :
    encodeRepeatedEvents x = [] := by
  unfold encodeRepeatedEvents
  rw [encodeRepeatedStep_of_spare x.tag x.cap.toNat x.bs.length _ h]

theorem fitsEnv_encodeRepeated_of_spare {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : EncodeRepeatedGhost}
    (h : x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat) :
    FitsEnv M lim st (EncodeRepeatedEnv x) :=
  FitsEnv.eq_iff.mpr (by rw [encodeRepeatedEvents_of_spare h]; trivial)

theorem encodeRepeatedEnv_eq_nil_of_spare {x : EncodeRepeatedGhost} {evs : List AllocEvent}
    (h : x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat)
    (hev : EncodeRepeatedEnv x evs) : evs = [] :=
  hev.trans (encodeRepeatedEvents_of_spare h)

/-! ## `VecU8ReserveChain` Bridges -/

theorem vecU8ReserveChain_reserveStep {cap len additional finalLen : Nat}
    (hle : len + additional ≤ finalLen) :
    VecU8ReserveChain cap (reserveStep cap len additional).1 finalLen
      (reserveStep cap len additional).2 := by
  by_cases h : len + additional ≤ cap
  · rw [reserveStep_of_spare h]
    exact .nil cap finalLen
  · rw [reserveStep_of_need h]
    have hcap_eq : reserveCap cap len additional = vecU8ReserveCap cap len additional := rfl
    rw [hcap_eq]
    exact VecU8ReserveChain.single_reserve (by omega) hle

theorem vecU8ReserveChain_pushByteStep {cap len finalLen : Nat}
    (hle : len + 1 ≤ finalLen) :
    VecU8ReserveChain cap (pushByteStep cap len).1 finalLen (pushByteStep cap len).2 := by
  rw [← reserveStep_one_eq_pushByteStep]
  exact vecU8ReserveChain_reserveStep hle

theorem vecU8ReserveChain_pushBytesStep :
    ∀ (n cap len finalLen : Nat),
      len + n ≤ finalLen →
      VecU8ReserveChain cap (pushBytesStep n cap len).1 finalLen (pushBytesStep n cap len).2
  | 0, cap, _, finalLen, _ => .nil cap finalLen
  | n + 1, cap, len, finalLen, hle => by
    simp only [pushBytesStep]
    exact (vecU8ReserveChain_pushByteStep (by omega)).trans (Nat.le_refl _)
      (vecU8ReserveChain_pushBytesStep n (pushByteStep cap len).1 (len + 1) finalLen (by omega))

theorem vecU8ReserveChain_encodeRepeatedElemStep {tag cap len finalLen : Nat}
    {elemBs : List (BitVec 8)}
    (hle : len + (encodeBytesField tag (some elemBs)).length ≤ finalLen) :
    VecU8ReserveChain cap (encodeRepeatedElemStep tag cap len elemBs).1 finalLen
      (encodeRepeatedElemStep tag cap len elemBs).2 := by
  rw [encodeBytesField_some_length, encodeKey_lengthDelimited_eq] at hle
  dsimp only [encodeRepeatedElemStep]
  have h1 := vecU8ReserveChain_pushBytesStep
    (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length cap len finalLen (by omega)
  have h2 := vecU8ReserveChain_pushBytesStep
    (encodeVarint (BitVec.ofNat 64 elemBs.length)).length
    (pushBytesStep (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length cap len).1
    (len + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length) finalLen (by omega)
  have h3 := vecU8ReserveChain_reserveStep (cap :=
      (pushBytesStep (encodeVarint (BitVec.ofNat 64 elemBs.length)).length
        (pushBytesStep (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length cap len).1
        (len + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length)).1)
    (len := len + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
      (encodeVarint (BitVec.ofNat 64 elemBs.length)).length)
    (additional := elemBs.length) (finalLen := finalLen) (by omega)
  exact (h1.trans (Nat.le_refl _) h2).trans (Nat.le_refl _) h3

theorem vecU8ReserveChain_encodeRepeatedStep (tag : Nat) :
    ∀ (cap len finalLen : Nat) (elems : List (List (BitVec 8))),
      len + (encodeRepeatedBytes tag elems).length ≤ finalLen →
      VecU8ReserveChain cap (encodeRepeatedStep tag cap len elems).1 finalLen
        (encodeRepeatedStep tag cap len elems).2
  | cap, _, finalLen, [], _ => .nil cap finalLen
  | cap, len, finalLen, elemBs :: rest, hle => by
    rw [encodeRepeatedBytes_cons, List.length_append] at hle
    simp only [encodeRepeatedStep]
    exact (vecU8ReserveChain_encodeRepeatedElemStep (by omega)).trans (Nat.le_refl _)
      (vecU8ReserveChain_encodeRepeatedStep tag _ _ finalLen rest (by omega))

theorem vecU8EncodeEnv_of_encodeRepeatedEnv {x : EncodeRepeatedGhost} {finalLen : Nat}
    {evs : List AllocEvent}
    (hle : x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ finalLen)
    (hev : EncodeRepeatedEnv x evs) :
    VecU8EncodeEnv x.cap.toNat finalLen evs := by
  rw [hev]
  exact ⟨_, vecU8ReserveChain_encodeRepeatedStep x.tag x.cap.toNat x.bs.length finalLen _ hle⟩

/-! ## Deterministic-Capacity `encodeVarintDetSpec*` and `encodeRepeatedSpec*` -/

/-- `encodeVarintFitSpecOf` refined with exact post-call capacity
`cap'.toNat = (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1`,
enabling multi-call deterministic event composition (`encodeRepeatedStep`,
`encodePolyEncoderEvents`) and `VecU8ReserveChain` composition. -/
def encodeVarintDetSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := (encodeVarintFitSpecOf resStack A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr) ∧
          cap'.toNat = (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x30 + resStack)

def encodeVarintDetSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) :=
  encodeVarintDetSpecOf doReserveStack A lim

def encodeVarintDetSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) :=
  encodeVarintDetSpecOf doReserveStackX A lim

theorem subroutine_ok_encodeVarintFit_of_det {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (encodeVarintDetSpecOf resStack A lim)) :
    subroutine_ok prog entry (encodeVarintFitSpecOf resStack A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun (x, st) R s0 sf hq => ?_)
  dsimp only [encodeVarintDetSpecOf] at hq
  dsimp only [encodeVarintFitSpecOf, encodeVarintSpecOf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨evs, cap', ptr', htr, ⟨hle, hpres, _⟩, hmem⟩
  exact ⟨evs, cap', ptr', htr, ⟨hle, hpres⟩, hmem⟩

theorem subroutine_ok_withLsCodeLoaded_encodeVarintFit_of_det [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A lim)) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun (x, st) R s0 sf hq => ?_)
  dsimp only [withLsCodeLoaded, encodeVarintDetSpecOf] at hq
  dsimp only [withLsCodeLoaded, encodeVarintFitSpecOf, encodeVarintSpecOf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨evs, cap', ptr', htr, ⟨hle, hpres, _⟩, hmem⟩
  exact ⟨evs, cap', ptr', htr, ⟨hle, hpres⟩, hmem⟩

/-- Budget-threaded specification of `prost::encoding::bytes::encode_repeated::<Vec<u8>, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodeRepeatedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeRepeatedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 58 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeRepeatedEnv x)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeRepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr) ∧
          cap'.toNat =
            (encodeRepeatedStep x.tag x.cap.toNat x.bs.length (x.elems.map Prod.snd)).1⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr'
            (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeRepeatedEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (encodeRepeatedStackOf resStack)

def encodeRepeatedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeRepeatedGhost × M.σ) :=
  encodeRepeatedSpecOf doReserveStack A lim

def encodeRepeatedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeRepeatedGhost × M.σ) :=
  encodeRepeatedSpecOf doReserveStackX A lim

/-- `encodeRepeatedSpecOf` relaxed to `x.elems.length < 2 ^ 59` (for `encode_repeated [local#2]`
and `PolynomialEncoder::encode`). -/
def encodeRepeated59DetSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeRepeatedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeRepeatedEnv x)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeRepeatedStackOf resStack)
  post := (encodeRepeatedSpecOf resStack A lim).post

/-! ## Generic Call Steppers (`EncRepeatedCalleeSaved`) -/

theorem step_memcpy_call_gen {prog : Program} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8)) (curSt : M.σ)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim curSt sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_noPanic (x := (dst, src, bs)) (F := A.pool lim curSt s ∗ F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_encode_varint_det_call_gen {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withEncRepeatedCS s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withEncRepeatedCS, encodeVarintDetSpecOf, encodeVarintFitSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, encodeVarintDetSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    refine SepWPp.weaken_pre (P' :=
      ⌜sm.trace = s.trace⌝ ∗
      ⌜curCap.toNat ≤ nextCap.toNat ∧
        (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
          nextCap = curCap ∧ nextPtr = curPtr) ∧
        nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1⌝ ∗
      ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
      ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents evs curSt) sm ∗
        stackAt (sp - 80#64) (0x30 + resStack)) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun ⟨hge, hpres, hcap_det⟩ =>
      SepWPp.pure_elim fun hev => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hev_eq : evs = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 := by
      rw [hev, encodeVarintEvents, pushBytesStep_snd_eq]
    rw [hev_eq]
    exact hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
      (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call))
      hge hpres hcap_det

theorem step_encode_varint_call_gen {resStack : Nat} {prog : Program}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withEncRepeatedCS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    refine SepWPp.weaken_pre (P' :=
      ⌜sm.trace = s.trace⌝ ∗
      ⌜curCap.toNat ≤ nextCap.toNat ∧
        (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
          nextCap = curCap ∧ nextPtr = curPtr)⌝ ∗
      ⌜EncodeVarintEnv (EncodeVarintGhost.mk val v curCap curPtr curBs) evs⌝ ∗
      ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents evs curSt) sm ∗
        stackAt (sp - 80#64) (0x30 + resStack)) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun ⟨hge, hpres⟩ =>
      SepWPp.pure_elim fun hev => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hev_eq : evs = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2 := by
      rw [hev, encodeVarintEvents, pushBytesStep_snd_eq]
    rw [hev_eq]
    exact hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
      (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres

theorem step_do_reserve2_call_gen {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCS s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCS, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, doReserve2SpecOf, doReserveSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun newPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_do_reserve7_call_gen {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCS s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine sepWPp_call_cs_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, doReserveSpecOf]
    rw [hsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun newPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
