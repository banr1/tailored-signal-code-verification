/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Budget-Threaded Relocatable Drop Glue Proof for `SignalMessage`

Proves the `RustCliAllocBudget M` contract `dropSignalMessageSpecPlaced` for
`core::ptr::drop_glue::<SignalMessage>` under `[LibsignalPlacement]` and transfers it to caller
blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage macLength)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At vecU8At_entails_dealloc)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SignalMessageGhost boxU8At optBoxU8At signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block sepWP_seq_lscro
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (
  blkLib_554 blkPl_554 instIsLsBlockProg_554 lsProg_554
)
open CryptoVerification.SignalSession.Cli.RunProofs (DropSignalMessageGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.DropSignalMessageHelpers (
  stackAt_split_ge subroutine_ok_frame_weaken
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget (
  dropSignalMessageSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Budget-threaded `[LibsignalPlacement]` specification for `drop_glue::<SignalMessage>`. -/
def dropSignalMessageSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSignalMessageGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl { dropSignalMessageSpec M A lim stk with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ signalMessageAt A.repAlloc x.g x.a x.m ∗
        A.pool lim st s ∗ stackAt s.sp stk }

section DropSignalMessagePlacedBudgetHelpers

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)

private theorem freeOnlyPool_step_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs : List AllocEvent)
    (hevs : ∀ ev ∈ evs, ∃ al sz, ev = .free al sz) (sz al : Nat) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right (evs ++ rustDeallocEvents sz al) ?_
  rw [M.stepEvents_append]
  refine Entails.pure_right ?_ (Entails.refl _)
  intro ev hmem
  rcases List.mem_append.mp hmem with h1 | h2
  · exact hevs ev h1
  · simp only [rustDeallocEvents, List.mem_singleton] at h2
    exact ⟨al, sz, h2⟩

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs : List AllocEvent)
    (hevs : ∀ ev ∈ evs, ∃ al sz, ev = .free al sz) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem ofNat_beq_zero_false_sm_placed {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_toNat_eq_sm_placed {n : Nat} (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem stackAt_smDrop_split_placed (sp : BitVec 64) :
    stackAt sp (32 + extHookStack) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  simpa only [Nat.add_comm 32 extHookStack] using
    ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottom_placed (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← ProofLib.stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = 32 + extHookStack from Nat.add_comm _ _,
      ← stackAt_smDrop_split_placed sp]

private theorem cells4_entails_stack_bottom_placed (sp fp lr x19 w3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottom_placed sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x19 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem sm_tail_post_weaken_placed (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ (memRegion a 120 ∗ memRegion (sp - 16416#64) 32) ⊢
      memRegion a 120 ∗ pool ∗ stackAt sp (32 + extHookStack) := by
  rw [stackAt_smDrop_split_placed sp, ← tail_stack_32_from_bottom_placed sp]
  exact Entails.of_eq (by sep_ac_rfl)

private def deallocOptPlaced (A : RustAlloc) (sz ptr : BitVec 64) : SepProp :=
  if (sz == 0#64) = true then emp
  else ⌜0 < sz.toNat ∧ sz.toNat < 2 ^ 63⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat

private theorem deallocOptPlaced_eq (A : RustAlloc) (sz ptr : BitVec 64) :
    deallocOptPlaced A sz ptr =
      if (sz == 0#64) = true then emp
      else ⌜0 < sz.toNat ∧ sz.toNat < 2 ^ 63⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat :=
  rfl

private theorem sep_pull_third_sm_placed (P Q R S : SepProp) : P ∗ Q ∗ R ∗ S = R ∗ P ∗ Q ∗ S := by
  sep_ac_rfl

private theorem vecU8At_entails_deallocOpt_placed (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      deallocOptPlaced A cap ptr := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader deallocOptPlaced
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases hc : cap = 0
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
    exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)

private theorem boxU8At_entails_deallocOpt_placed (A : RustAlloc) (a ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      deallocOptPlaced A (BitVec.ofNat 64 bs.length) ptr := by
  unfold boxU8At deallocOptPlaced
  rw [sep_pull_third_sm_placed]
  apply Entails.pure_left; rintro ⟨_, hlt⟩
  cases bs with
  | nil =>
    simp only [List.length_nil, beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  | cons b tl =>
    have hpos : 0 < (b :: tl).length := Nat.succ_pos _
    have hlt64 : (b :: tl).length < 2 ^ 64 := by omega
    have hbeq : (BitVec.ofNat 64 (b :: tl).length == 0#64) = false :=
      ofNat_beq_zero_false_sm_placed hpos hlt64
    have htonat : (BitVec.ofNat 64 (b :: tl).length).toNat = (b :: tl).length :=
      ofNat_toNat_eq_sm_placed hlt64
    simp only [List.cons_ne_nil, ↓reduceIte, hbeq, Bool.false_eq_true, htonat]
    exact sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨hpos, hlt⟩
        (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: tl)))))

private theorem optBoxU8At_entails_deallocOpt_placed (A : RustAlloc) (a ptr : BitVec 64)
    (mbs : Option (List (BitVec 8))) :
    optBoxU8At A a ptr mbs ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        deallocOptPlaced A (if (w0 == 0#64) = true then 0#64 else w1) w0 := by
  cases mbs with
  | none =>
    unfold optBoxU8At deallocOptPlaced
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1 ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    unfold optBoxU8At
    have hne : boxU8At A a ptr bs ⊢ ⌜(ptr == 0#64) = false⌝ ∗ boxU8At A a ptr bs := by
      unfold boxU8At
      nth_rw 1 [sep_pull_third_sm_placed]
      apply Entails.pure_left; intro hp
      exact Entails.pure_right (beq_false_of_ne hp.1)
        (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hp (Entails.refl _))))
    refine Entails.trans hne ?_
    apply Entails.pure_left; intro hp0
    refine Entails.trans (boxU8At_entails_deallocOpt_placed A a ptr bs) ?_
    refine Entails.sepExists_right ptr (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_)
    simp only [hp0, Bool.false_eq_true, ↓reduceIte]
    exact Entails.refl _

private theorem boxU8At_serialized_expose_placed (A : RustAlloc) (a ptr : BitVec 64)
    (bs : List (BitVec 8)) (hmin : macLength + 1 ≤ bs.length) :
    boxU8At A a ptr bs ⊢
      ⌜(BitVec.ofNat 64 bs.length == 0#64) = false ∧
        0 < (BitVec.ofNat 64 bs.length).toNat ∧
        (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗
      memRegion ptr (BitVec.ofNat 64 bs.length).toNat := by
  unfold boxU8At
  rw [sep_pull_third_sm_placed]
  apply Entails.pure_left; rintro ⟨_, hlt⟩
  have hpos : 0 < bs.length := by omega
  have hlt64 : bs.length < 2 ^ 64 := by omega
  have hne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hbeq : (BitVec.ofNat 64 bs.length == 0#64) = false := ofNat_beq_zero_false_sm_placed hpos hlt64
  have htonat : (BitVec.ofNat 64 bs.length).toNat = bs.length := ofNat_toNat_eq_sm_placed hlt64
  simp only [hne, ↓reduceIte, htonat]
  exact Entails.pure_right ⟨hbeq, hpos, hlt⟩
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr bs))))

@[reducible]
private def smHeadersAtPlaced (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64) : SepProp :=
  (a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
  ((a + 40#64) ↦₆₄ serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
  memRegion (a + 56#64) 32 ∗
  ((a + 88#64) ↦₆₄ w0) ∗ ((a + 96#64) ↦₆₄ w1) ∗
  memRegion (a + 104#64) 16

private theorem smHeadersAt_entails_memRegion_120_placed
    (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64) :
    smHeadersAtPlaced a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ⊢ memRegion a 120 := by
  unfold smHeadersAtPlaced
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 112) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 104) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 96) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 88) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 80) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 72) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 64) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 32) (k := 32) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 24) (b' := a + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 96#64) (n := 8) (k := 16) (b' := a + 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (Entails.refl _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))))))

private theorem signalMessageAt_expose_placed (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A g a m ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜(BitVec.ofNat 64 m.serialized.length == 0#64) = false ∧
          0 < (BitVec.ofNat 64 m.serialized.length).toNat ∧
          (BitVec.ofNat 64 m.serialized.length).toNat < 2 ^ 63⌝ ∗
        smHeadersAtPlaced a g.pqCap g.pqPtr g.ctPtr (BitVec.ofNat 64 m.ciphertext.length)
          g.serPtr (BitVec.ofNat 64 m.serialized.length) w0 w1 ∗
        deallocOptPlaced A (BitVec.ofNat 64 m.ciphertext.length) g.ctPtr ∗
        deallocOptPlaced A g.pqCap g.pqPtr ∗
        deallocOptPlaced A (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
        A.live g.serPtr (BitVec.ofNat 64 m.serialized.length).toNat 1 ∗
        memRegion g.serPtr (BitVec.ofNat 64 m.serialized.length).toNat := by
  unfold signalMessageAt
  apply Entails.pure_left; rintro ⟨hmin, _, _, _, _⟩
  have hpq := vecU8At_entails_deallocOpt_placed A a g.pqCap g.pqPtr m.pqRatchet
  have hct := boxU8At_entails_deallocOpt_placed A (a + 24#64) g.ctPtr m.ciphertext
  have hser := boxU8At_serialized_expose_placed A (a + 40#64) g.serPtr m.serialized hmin
  have hsrk : ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ⊢ memRegion (a + 56#64) 32 := by
    simpa only [m.senderRatchetKey.bytes.toList_length] using
      ProofLib.pointsToBytes_entails_memRegion (a + 56#64) m.senderRatchetKey.bytes.toList
  have haddr := optBoxU8At_entails_deallocOpt_placed A (a + 88#64) g.addrPtr m.addresses
  have htail :
      ((a + 104#64) ↦₃₂ m.counter) ∗
      (((a + 108#64) ↦₃₂ m.previousCounter) ∗
      (((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7)) ⊢
      memRegion (a + 104#64) 16 := by
    rw [ProofLib.memRegion_split' (b := a + 104#64) (n := 4) (k := 12) (b' := a + 108#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 108#64) (n := 4) (k := 8) (b' := a + 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 112#64) (n := 1) (k := 7) (b' := a + 113#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)))
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h48 : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
  have h96 : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
  rw [h32] at hct
  rw [h48] at hser
  simp only [h96] at haddr
  refine Entails.trans
    (sepConj_mono hpq
      (sepConj_mono hct
        (sepConj_mono hser
          (sepConj_mono hsrk
            (sepConj_mono haddr htail))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_)
  dsimp only [smHeadersAtPlaced]
  exact Entails.of_eq (by sep_ac_rfl)

@[reducible]
private def Saved32PreservedPlaced (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
  s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem seq_clean32_placed [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  refine sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hent, hQ⟩ hcrl_m
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hcrl_m hQ)

private theorem sm_tail_pre_weaken_placed
    (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64)
    (live pool : SepProp) (sp fp lr x19 w3 : BitVec 64) :
    smHeadersAtPlaced a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
      live ∗ pool ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    pool ∗ live ∗ stackAt sp extHookStack ∗
      (memRegion a 120 ∗ memRegion (sp - 16416#64) 32) := by
  have ha := smHeadersAt_entails_memRegion_120_placed a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1
  have hst := cells4_entails_stack_bottom_placed sp fp lr x19 w3
  have hreord :
      (smHeadersAtPlaced a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
        live ∗ pool ∗
        stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3)) =
      (smHeadersAtPlaced a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
        (live ∗ pool ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3)))) := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono ha (sepConj_mono_right (sepConj_mono_right hst))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private def dropSignalMessageFreePoolSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSignalMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ signalMessageAt A.repAlloc x.g x.a x.m ∗
      A.pool lim st s ∗ stackAt s.sp (32 + extHookStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 120 ∗
      freeOnlyPool A lim st sf ∗ stackAt s0.sp (32 + extHookStack)

set_option maxHeartbeats 1600000 in
private theorem cliDropSignalMessage_freePool_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_554 H) (blkPl_554).base
      (withLsCodeRoLoaded lsmpl (dropSignalMessageFreePoolSpec M A lim)) := by
  unfold withLsCodeRoLoaded dropSignalMessageFreePoolSpec
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_554 H) hA
  clear hA
  dsimp only [withLsCodeRoLoaded, lsProg_554, RustCliAllocBudget.live, ↓reduceIte] at hdealloc ⊢
  wp_init x s0
  rcases x with ⟨⟨a, g, msg⟩, st⟩
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  subst ‹s0.readReg64 _ = a›
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 32#64 (by assumption)
  nth_rw 1 [stackAt_smDrop_split_placed s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i st0 st1 st2 w3
  refine SepWP.weaken_pre
    (sepConj_mono (signalMessageAt_expose_placed A.repAlloc g (s0.readReg64 (Reg.gpr 0#5)) msg)
      (sepConj_mono_left (freeOnlyPool_intro_nil A lim st s0))) ?_
  wp_pull_exists
  rename_i w0 w1
  refine SepWP.pure_elim ?_
  rintro ⟨hser_ne0, hser_pos, hser_lt⟩
  let Hdrs : SepProp :=
    smHeadersAtPlaced (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
      g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
      g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1
  let SavedSlots : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ w3)
  refine seq_clean32_placed
    (mid := (blkPl_554).base +
      (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 0 + 4#64))
    (P_mid := fun sm =>
      Hdrs ∗
      deallocOptPlaced A.repAlloc g.pqCap g.pqPtr ∗
      deallocOptPlaced A.repAlloc (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
      A.repAlloc.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
      memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
    (Q := fun sm =>
      Saved32PreservedPlaced s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
    hcrl0 ?_ ?_
  · dsimp only [Hdrs, SavedSlots, smHeadersAtPlaced]
    conv => arg 4; dsimp only [freeOnlyPool]
    wp_pull_exists; rename_i evs0
    refine SepWP.focus_pure (by sep_focus) fun hevs0 => ?_
    nth_rw 1 [deallocOptPlaced_eq]
    by_cases hct : (BitVec.ofNat 64 msg.ciphertext.length == 0#64) = true <;>
      simp only [hct, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    · wp_steps_sync_pool ((blkPl_554).base +
        (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 0 + 4#64))
      apply SepWP.fold (freeOnlyPool_keep A lim st _ evs0 hevs0) (by sep_focus)
      wp_done
    · refine SepWP.focus_pure (by sep_focus) fun h => ?_
      obtain ⟨hpos, hlt⟩ := h
      have hrlay : RustLayoutOk (BitVec.ofNat 64 msg.ciphertext.length).toNat 1 :=
        ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_c0, hro_c0⟩
      wp_call hdealloc (g.ctPtr, (BitVec.ofNat 64 msg.ciphertext.length).toNat, 1, M.stepEvents evs0 st)
      apply SepWP.fold
        (freeOnlyPool_step_dealloc A lim st _ evs0 hevs0
          (BitVec.ofNat 64 msg.ciphertext.length).toNat 1)
        (by sep_focus)
      wp_done
  · intro s1 hpc1 hrun1 hcrl1
      ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean32_placed
      (mid := (blkPl_554).base +
        (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 1 + 4#64))
      (P_mid := fun sm =>
        Hdrs ∗
        deallocOptPlaced A.repAlloc (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
        A.repAlloc.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
        memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
      (Q := fun sm =>
        Saved32PreservedPlaced s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
      hcrl1 ?_ ?_
    · dsimp only [Hdrs, smHeadersAtPlaced]
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs1
      refine SepWP.focus_pure (by sep_focus) fun hevs1 => ?_
      nth_rw 1 [deallocOptPlaced_eq]
      by_cases hpq : (g.pqCap == 0#64) = true <;>
        simp only [hpq, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps_sync_pool ((blkPl_554).base +
          (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 1 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs1 hevs1) (by sep_focus)
        wp_done
      · refine SepWP.focus_pure (by sep_focus) fun h => ?_
        obtain ⟨hpos, hlt⟩ := h
        have hrlay : RustLayoutOk g.pqCap.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_c1, hro_c1⟩
        wp_call hdealloc (g.pqPtr, g.pqCap.toNat, 1, M.stepEvents evs1 st)
        try rw [hsp_1]
        apply SepWP.fold
          (freeOnlyPool_step_dealloc A lim st _ evs1 hevs1 g.pqCap.toNat 1)
          (by sep_focus)
        wp_done
    · intro s2 hpc2 hrun2 hcrl2
        ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean32_placed
        (mid := (blkPl_554).base +
          (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 2 + 4#64))
        (P_mid := fun sm =>
          Hdrs ∗
          A.repAlloc.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
          memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
          freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
        (Q := fun sm =>
          Saved32PreservedPlaced s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
        hcrl2 ?_ ?_
      · dsimp only [Hdrs, smHeadersAtPlaced]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs2
        refine SepWP.focus_pure (by sep_focus) fun hevs2 => ?_
        nth_rw 1 [deallocOptPlaced_eq]
        by_cases hw0 : (w0 == 0#64) = true
        · simp only [hw0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
          wp_steps_sync_pool ((blkPl_554).base +
            (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 2 + 4#64))
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs2 hevs2) (by sep_focus)
          wp_done
        · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
          by_cases hw1 : (w1 == 0#64) = true <;>
            simp only [hw1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
          · wp_steps_sync_pool ((blkPl_554).base +
              (reloc_call_off% (blkLib_554).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 2 + 4#64))
            apply SepWP.fold (freeOnlyPool_keep A lim st _ evs2 hevs2) (by sep_focus)
            wp_done
          · refine SepWP.focus_pure (by sep_focus) fun h => ?_
            obtain ⟨hpos, hlt⟩ := h
            have hrlay : RustLayoutOk w1.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
            apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl2
            wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            rintro ⟨hcl_c2, hro_c2⟩
            wp_call hdealloc (w0, w1.toNat, 1, M.stepEvents evs2 st)
            try rw [hsp_2]
            apply SepWP.fold
              (freeOnlyPool_step_dealloc A lim st _ evs2 hevs2 w1.toNat 1)
              (by sep_focus)
            wp_done
      · intro s3 hpc3 hrun3 hcrl3
          ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        conv => arg 4; dsimp only [Hdrs, SavedSlots, smHeadersAtPlaced, freeOnlyPool]
        wp_pull_exists; rename_i evs3
        refine SepWP.focus_pure (by sep_focus) fun hevs3 => ?_
        have hrlay_ser : RustLayoutOk (BitVec.ofNat 64 msg.serialized.length).toNat 1 :=
          ⟨⟨hser_pos, hpow1, by omega⟩, hal1⟩
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl3
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (by dsimp only [smHeadersAtPlaced]; sep_ac_rfl))
            (sm_tail_pre_weaken_placed (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
              g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
              g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1
              (A.repAlloc.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
                memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat)
              _ s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 19#5)) w3)) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_tail, hro_tail⟩
        wp_call hdealloc
          (g.serPtr, (BitVec.ofNat 64 msg.serialized.length).toNat, 1, M.stepEvents evs3 st)
        apply SepWP.fold
          (freeOnlyPool_step_dealloc A lim st _ evs3 hevs3
            (BitVec.ofNat 64 msg.serialized.length).toNat 1)
          (by sep_focus)
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (by sep_ac_rfl))
            (sm_tail_post_weaken_placed (s0.readReg64 (Reg.gpr 0#5)) _ s0.sp)) ?_
        wp_done

theorem cliDropSignalMessage_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_554 H) (blkPl_554).base
      (dropSignalMessageSpecPlaced M A lim (32 + extHookStack)) := by
  refine subroutine_ok_frame_weaken (F := fun _ _ => emp)
    (cliDropSignalMessage_freePool_placed_ok hA) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · rintro ⟨x, st⟩ s0
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded,
      dropSignalMessageSpec, dropSignalMessageFreePoolSpec]
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨x, st⟩ s0 sf
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded,
      dropSignalMessageSpec, dropSignalMessageFreePoolSpec, freeOnlyPool]
    rw [sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro evs
    refine Entails.sepExists_right evs ?_
    have hord :
        ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 120 ∗
          (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp (32 + extHookStack) =
        ⌜sf.trace = s0.trace⌝ ∗ (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗
          (memRegion x.a 120 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (32 + extHookStack))) := by
      sep_ac_rfl
    rw [hord]
    apply Entails.pure_left; intro htr
    apply Entails.pure_left; intro hevs
    exact Entails.pure_right ⟨htr, hevs⟩ (Entails.refl _)
  · intro _ _ _
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded]
    exact Entails.pure_left False.elim

end DropSignalMessagePlacedBudgetHelpers

/-- Proves the budget-threaded `dropSignalMessageSpecPlaced` contract at stack budgets `32 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropSignalMessage_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_554 H) (blkPl_554).base
      (dropSignalMessageSpecPlaced M A lim stk) := by
  refine subroutine_ok_frame_weaken
    (F := fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)))
    (cliDropSignalMessage_exact_placed_ok hA) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded, dropSignalMessageSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded, dropSignalMessageSpec]
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro evs
    refine Entails.sepExists_right evs ?_
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro _ _ _
    dsimp only [dropSignalMessageSpecPlaced, withLsCodeRoLoaded, dropSignalMessageSpec]
    exact Entails.pure_left False.elim

/-- Transfers `cliDropSignalMessage_placed_ok` to any caller block `i < 619`. -/
theorem cliDropSignalMessage_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_554).base
      (dropSignalMessageSpecPlaced M A lim stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_554 H) i 554 H
    hcaller (instIsLsBlockProg_554 H) (blkPl_554).base _
    (cliDropSignalMessage_placed_ok hA stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessagePlacedBudget
