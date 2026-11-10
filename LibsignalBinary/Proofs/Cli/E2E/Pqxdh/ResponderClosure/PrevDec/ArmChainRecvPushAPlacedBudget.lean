/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Placed Tag 7 (`receiver_chains`) `grow_one` Pre/Post Bridges

Proves budget-threaded `[LibsignalPlacement]` `growOneChainSpecX` precondition and postcondition
bridges splitting the grown 104-byte `receiver_chains` buffer and advancing `A.pool` by
`growOne104Events cap`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (maxReceiverChains)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env finishGrowStackX growOne104Events growOne104SpecX growOneChainSpecX
  growOneChainStackX
)

set_option maxHeartbeats 400000 in
theorem growOne_plain_pre_eq_q_ext {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (q cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = q) :
    (growOneChainSpecX M A lim).pre ((q + 0x978#64, cap, ptr, bs), st) s =
    ⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool lim st s ∗
      stackAt q growOneChainStackX) := by
  unfold growOneChainSpecX growOne104SpecX
  dsimp only
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  have hpure :
      (s.readReg64 .x0 = q + 0x978#64 ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧ FitsEnv M lim st (GrowOne104Env cap)) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 ∧ FitsEnv M lim st (GrowOne104Env cap)) :=
    propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h3, by omega, h5⟩,
             fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h3, by omega, h5⟩⟩
  rw [hpure, e50, hsp, h0]

theorem growOne_lscl_pre_eq_q_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (q cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = q) :
    (withLsCl lsmpl (growOneChainSpecX M A lim)).pre ((q + 0x978#64, cap, ptr, bs), st) s =
    (⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        A.pool lim st s ∗
        stackAt q growOneChainStackX)) ∗
    ⌜LibsignalCodeLoaded lsmpl s.mem⌝ := by
  dsimp only [withLsCl]
  rw [growOne_plain_pre_eq_q_ext A lim st q cap ptr bs s hsp]

set_option maxHeartbeats 400000 in
theorem growOne_plain_post_elim_sp_q_ext {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (q cap ptr : BitVec 64)
    (cs : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = q)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    (growOneChainSpecX M A lim).post ((q + 0x978#64, cap, ptr, bs), st) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap') ∗ ((q + 0x980#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        A.pool lim (M.stepEvents (growOne104Events cap) st) sf ∗
        stackAt q growOneChainStackX := by
  unfold growOneChainSpecX growOne104SpecX
  dsimp only
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  set newCap : Nat := max (2 * cap.toNat) 4
  set cap' : BitVec 64 := BitVec.ofNat 64 newCap
  have h5 : maxReceiverChains = 5 := rfl
  have hcap'_toNat : cap'.toNat = newCap := by
    dsimp only [cap', newCap]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt_cap' : cs.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hsp, h0]
  change _ ⊢ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ stackAt q (464 + finishGrowStackX)
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hlt_cap', hcap'_lt, hp'⟩ ?_
  have hlive_eq : A.live p' (newCap * 104) 8 = A.live p' (cap'.toNat * 104) 8 := by
    rw [hcap'_toNat]
  have hrem : (newCap - cap.toNat) * 104 =
      104 + (cap'.toNat - (cs.length + 1)) * 104 := by
    have : newCap - cap.toNat = 1 + (cap'.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbs_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (cs.length * 104) := by
    rw [hbs, hfull]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      p' + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hlive_eq, hbs_eq, hrem,
      memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by sep_ac_rfl)

theorem growOne_lscl_post_elim_sp_q_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (q cap ptr : BitVec 64)
    (cs : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = q)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    (withLsCl lsmpl (growOneChainSpecX M A lim)).post
        ((q + 0x978#64, cap, ptr, bs), st) s_pre sf ⊢
      ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap') ∗ ((q + 0x980#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        A.pool lim (M.stepEvents (growOne104Events cap) st) sf ∗
        stackAt q growOneChainStackX := by
  dsimp only [withLsCl]
  exact sepConj_mono_right
    (growOne_plain_post_elim_sp_q_ext A lim st q cap ptr cs bs s_pre sf hsp hfull hlt5 hbs)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget
