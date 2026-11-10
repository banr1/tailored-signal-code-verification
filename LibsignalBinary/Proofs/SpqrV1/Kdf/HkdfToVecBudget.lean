/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `spqr::kdf::hkdf_to_vec`

Relocatable `[LibsignalPlacement]` budget-threaded specification and proof for
`spqr::kdf::hkdf_to_vec` (Block `378`) under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_378 blkPC_378 blkPl_378 lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack noAllocShimSpec sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (HkdfFn)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf (HkdfToVecGhost spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk VmPreserved
   rustAllocEvents rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Allocator Event Envelope and Budget-Threaded Specification -/

/-- Exact allocator event sequence of `spqr::kdf::hkdf_to_vec`: one zeroed allocation of
    `okmLen` bytes at alignment `1`. -/
def HkdfToVecEnv (okmLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents okmLen 1

/-- Budget-threaded specification of `spqr::kdf::hkdf_to_vec` (Block `378`, 47 instructions):
    total correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) under
    `FitsEnv M lim st (HkdfToVecEnv x.okmLen)`. -/
def hkdfToVecSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hkdf : HkdfFn) : Spec (HkdfToVecGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outVec ∧
      s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
      s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
      s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
      s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
      x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
      32 ≤ x.info.length ∧ x.info.length < 55 ∧
      (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96) ∧
      FitsEnv M lim st (HkdfToVecEnv x.okmLen)⌝ ∗
      memRegion x.outVec 24 ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜(hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧ sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.outVec (hkdf x.salt x.ikm x.info x.okmLen) ∗
      bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      (∃∗ evs : List AllocEvent, ⌜HkdfToVecEnv x.okmLen evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp extHookStack

abbrev hkdfToVecSpqrSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hkdf : HkdfFn) : Spec (HkdfToVecGhost × M.σ) :=
  hkdfToVecSpec M A lim hkdf

/-! ## Local Separation-Logic and Arithmetic Helpers -/

private theorem memRegion_zero (a : BitVec 64) : memRegion a 0 = emp := by
  have hb := IsBlock.pointsToBytes a []
  rw [pointsToBytes_nil] at hb
  exact IsBlock.eq (IsBlock.memRegion a 0) hb
    fun _ => ⟨fun _ => ⟨by simp, by simp⟩, fun _ => trivial⟩

private theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

private theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

private theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

private theorem stackAt_hkdfToVec (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12192 ∗
        stackAt (sp - 96#64) allocHookStack ∗
        cells (sp - 96#64) 12 := by
  have h1 : stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12192 ∗ stackAt sp (allocHookStack + 96) :=
    ProofLib.stackAt_split_bottom sp (allocHookStack + 96) 12192 (by decide)
  have h2 : stackAt sp (allocHookStack + 96) =
      stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 :=
    stackAt_split_cells sp 4096 12 (by decide)
  rw [h1, h2]

private theorem stackAt_hkdfToVec_fold (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - 16384#64) 12192 ∗
      stackAt (sp - 96#64) allocHookStack ∗
      ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
      ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
      ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
      ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
      stackAt sp extHookStack := by
  rw [stackAt_hkdfToVec sp]
  cells_unfold
  refine Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.sepExists_right v10
          (Entails.sepExists_right v11 (Entails.refl _))))))))))))

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        (a ↦₆₄ u2) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem zeroed_entails_memRegion (ptr : BitVec 64) (n : Nat) :
    (ptr ↦ₛ List.replicate n 0#8) ⊢ memRegion ptr n := by
  have h := pointsToBytes_entails_memRegion ptr (List.replicate n 0#8)
  rwa [List.length_replicate] at h

private theorem vecU8_exact_entails (A : RustAlloc) (v ptr : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hpos : 0 < n) (hle : n ≤ 8160) (hlen : bs.length = n) (hptr : ptr ≠ 0) :
    (v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr n 1 ∗ (ptr ↦ₛ bs) ⊢
      vecU8 A v bs := by
  unfold vecU8
  refine Entails.sepExists_right (BitVec.ofNat 64 n) (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  have hcap_toNat : (BitVec.ofNat 64 n).toNat = n :=
    Nat.mod_eq_of_lt (by omega)
  have hcap_ne : BitVec.ofNat 64 n ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hcap_toNat] at this
    change n = 0 at this
    omega
  simp only [hlen, hcap_ne, ↓reduceIte, hcap_toNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [show (v ↦₆₄ BitVec.ofNat 64 n ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ⌜n ≤ n ∧ n < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ A.live ptr n 1 ∗ (ptr ↦ₛ bs) =
    ⌜n ≤ n ∧ n < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr n 1 ∗ (ptr ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨Nat.le_refl n, by omega, hptr⟩ (Entails.refl _)

private theorem vecU8_budget_exact_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v ptr : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hpos : 0 < n) (hle : n ≤ 8160) (hlen : bs.length = n) (hptr : ptr ≠ 0) :
    (v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr n 1 ∗ (ptr ↦ₛ bs) ⊢
      vecU8 A.repAlloc v bs :=
  vecU8_exact_entails A.repAlloc v ptr bs n hpos hle hlen hptr

private theorem okmLen_toNat {n : Nat} (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n).toNat = n :=
  Nat.mod_eq_of_lt (by omega)

private theorem okmLen_getLsbD_63 {n : Nat} (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  change (BitVec.ofNat 64 n)[63] = false
  rw [BitVec.getElem_eq_testBit_toNat, okmLen_toNat hle]
  exact Nat.testBit_lt_two_pow (by omega)

private theorem okmLen_ne_zero {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [okmLen_toNat hle] at this
  change n = 0 at this
  omega

private theorem okmLen_beq_zero {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    (BitVec.ofNat 64 n == 0#64) = false :=
  beq_false_of_ne (okmLen_ne_zero hpos hle)

private theorem layoutOk_okmLen {n : Nat} (hpos : 0 < n) (hle : n ≤ 8160) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

private theorem pool_entails_hkdfToVecEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (okmLen : Nat) (st : M.σ) (sf : State) :
    A.pool lim (M.stepEvents (rustAllocEvents okmLen 1) st) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜HkdfToVecEnv okmLen evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right (rustAllocEvents okmLen 1) (Entails.pure_right rfl (Entails.refl _))

/-! ## Multi-Placed `[LibsignalPlacement]` Proof of `spqr::kdf::hkdf_to_vec` (Block `378`) -/

/-- Block `378` (`spqr::kdf::hkdf_to_vec`, 47 instructions) meets
`withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim hkdf)` on `(blkPC_378).rebase (blkPl_378).base H`. -/
theorem hkdf_to_vec_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (hkdf : HkdfFn)
    {H : LibsignalHooks}
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hSlice : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsmpl.base 379) (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec hkdf)))) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (blkPl_378).base (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim hkdf)) := by
  have hspec_eq : withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim hkdf) = {
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x8 = x.outVec ∧
        s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
        s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
        s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
        s.readReg64 .x6 = BitVec.ofNat 64 x.okmLen ∧
        x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
        32 ≤ x.info.length ∧ x.info.length < 55 ∧
        (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96) ∧
        FitsEnv M lim st (HkdfToVecEnv x.okmLen)⌝ ∗
        memRegion x.outVec 24 ∗
        bytesAt x.saltRO x.saltA x.salt ∗
        bytesAt x.ikmRO x.ikmA x.ikm ∗
        bytesAt x.infoRO x.infoA x.info ∗
        A.pool lim st s ∗
        memRegion (s.sp - 16384#64) 12192 ∗
        stackAt (s.sp - 96#64) allocHookStack ∗
        cells (s.sp - 96#64) 12 ∗
        ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
    post := (hkdfToVecSpec M A lim hkdf).post
    onPanic := (hkdfToVecSpec M A lim hkdf).onPanic
  } := by
    unfold withLsCodeRoLoaded
    congr 1
    funext ⟨x, st⟩ s
    simp only [hkdfToVecSpec, stackAt_hkdfToVec, sepConj_assoc]
  rw [hspec_eq]
  clear hspec_eq
  simp only [hkdfToVecSpec, memRegion_24_cells]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsρ spqrRustNoAllocShimSym) (withVmPreserved noAllocShimSpec) :=
    spqr_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_378).rebase (blkPl_378).base H)
      (lsρ spqrRustAllocZeroedSym) (rustCliAllocNoOomSpec M A lim true) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem hZero)
  have hslice_at := hSlice
  simp only [withLsCodeRoLoaded, withVmPreserved, hkdfToSliceSpqrSpec, hkdfToSliceSpec] at hslice_at
  clear hshim hZero hSlice
  wpp_init x_st s0
  obtain ⟨⟨outVec, saltRO, saltA, salt, ikmRO, ikmA, ikm, infoRO, infoA, info, okmLen⟩, st⟩ := x_st
  dsimp only at *
  have hokm_pos : 0 < okmLen := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have hokm_le : okmLen ≤ 8160 := by
    have := ‹okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96›; omega
  have htoNat : (BitVec.ofNat 64 okmLen).toNat = okmLen := okmLen_toNat hokm_le
  have hlsb63 : (BitVec.ofNat 64 okmLen).getLsbD 63 = false := okmLen_getLsbD_63 hokm_le
  have hne0 : BitVec.ofNat 64 okmLen ≠ 0#64 := okmLen_ne_zero hokm_pos hokm_le
  have hbeq0 : (BitVec.ofNat 64 okmLen == 0#64) = false := okmLen_beq_zero hokm_pos hokm_le
  have hlay : LayoutOk okmLen 1 := layoutOk_okmLen hokm_pos hokm_le
  have hpow2 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hrlay : RustLayoutOk okmLen 1 := ⟨hlay, by decide⟩
  have hFit : LibsignalBinary.Heap.FitsEvents M lim st (rustAllocEvents okmLen 1) :=
    ‹FitsEnv M lim st (HkdfToVecEnv okmLen)› (rustAllocEvents okmLen 1) rfl
  apply sepWPp_seq_lscro (mid := (blkPl_378).base + 104#64) ‹LibsignalCodeRoLoaded lsmpl s0.mem›
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_simp_pre [arm64_norm]
  wp_apply
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocZeroedSym)
  wp_simp_pre [arm64_norm]
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfr_1
  have htr_1 : sf_1.trace = s0.trace :=
    ‹LibsignalBinary.Heap.AllocCallPreserved _ _›.2.1.trans ‹sf.trace = s0.trace›
  simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsmpl.base 379) hfr_1
  rw [‹sf.sp = s0.sp - 96#64›]
  wp_steps_sync_pool (lsmpl.base 379)
  wp_simp_pre [arm64_norm]
  apply SepWP.fold (zeroed_entails_memRegion (sf_1.readReg64 (Reg.gpr 0#5)) okmLen) (by sep_focus)
  apply SepWP.fold (stackAt_hkdfToVec_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfr_2
  simp only [arm64_norm] at hfr_2
  have hcl_2 := hfr_2.1
  have hro_2 := hfr_2.2
  apply SepWPp.of_sepWP_ret
  wp_apply
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [arm64_norm]
  apply SepWP.fold (vecU8_budget_exact_entails A outVec (sf_1.readReg64 (Reg.gpr 0#5))
    (hkdf salt ikm info okmLen) okmLen hokm_pos hokm_le
    ‹(hkdf salt ikm info okmLen).length = okmLen› ‹sf_1.readReg64 .x0 ≠ 0#64›) (by sep_focus)
  apply SepWP.fold (pool_entails_hkdfToVecEnv A lim okmLen st _) (by sep_focus)
  wp_done

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
