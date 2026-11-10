/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `signal_session_coins_fill` Bridge for CLI `DhStep`

Proves `cliCoinsFillBudgetPlaced_ok` (`withVmPreserved (coinsFillSpecPlaced stk)`) on block `618`
and specializes the cross-block `hrng` hypothesis for caller blocks `433` and `507`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem
  ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508)
open CryptoVerification.LibsignalTripleRatchet (memcpyName memsetName sessionMemcpyRegionSpec
  sessionMemsetRegionSpec subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434 instIsLsBlockProg_434
  tryDecryptSubStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsFillSpecPlaced coinsLeftPlaced
  coinsLeftSym coinsNextPlaced coinsNextSym tapeAfter2 tapeAfter2_zero_eq)
open CryptoVerification.SignalSession.Coins.Placed (blkLib_eq_618 blkPC_618 blkPC_618_pairStep_0x18
  blkPC_618_pairStep_0x1c blkPl_618 instIsLsBlockProg_618)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux (
  coinsFillAtBudgetPlaced_of_after0_cro coinsFillAtBudgetSpecPlaced coinsFillBudgetSpecPlaced)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_sessionMemcpyRegion_budget_sat
  cliExternsPlaced_sessionMemsetRegion_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec
  sessionMemsetRegionBudgetSpec)

private def vmBase (s : State) :=
  (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail,
    fun (fd : Nat) (_ : 3 ≤ fd) (_ : fd < 2 ^ 31) => s.fs.fds (BitVec.ofNat 64 fd))
private def vmPerm (s : State) := s.mem.perm
private theorem vmBase_perm_of_vmPreserved {s0 sf : State} (h : VmPreserved s0 sf) :
    vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0 := by
  unfold vmBase vmPerm
  exact ⟨Prod.ext h.1.1 (Prod.ext h.1.2.1 (Prod.ext h.1.2.2 (Prod.ext h.2.1
    (funext fun fd => funext fun h1 => funext fun h2 => h.fdsHiFrame fd h1 h2)))),
    funext h.perm_eq⟩
private theorem vmPreserved_of_vmBase_perm {s0 sf : State}
    (hb : vmBase sf = vmBase s0) (hp : vmPerm sf = vmPerm s0) : VmPreserved s0 sf := by
  unfold vmBase at hb; unfold vmPerm at hp
  exact ⟨⟨congrArg Prod.fst hb, congrArg (·.2.1) hb, congrArg (·.2.2.1) hb⟩,
    congrArg (·.2.2.2.1) hb, fun a => congrFun hp a,
    fun fd h1 h2 => congrFun (congrFun (congrFun (congrArg (·.2.2.2.2) hb) fd) h1) h2⟩
private theorem cf_vmPerm_of_nsp {s sm : State} {m : Memory}
    (h : ProofLib.NonSyscallPreserved s (sm.setMem m)) : m.perm = vmPerm s := by
  unfold vmPerm; exact (show (sm.setMem m).mem.perm = m.perm from by cases sm; rfl) ▸ h.2.1

@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_setPC (s : State) (pc : BitVec 64) : vmBase (s.setPC pc) = vmBase s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_setMem (s : State) (m : Memory) : vmBase (s.setMem m) = vmBase s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_setPState (s : State) (ps : PState) : vmBase (s.setPState ps) = vmBase s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : vmBase (s.writeReg64 r v) = vmBase s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : vmBase (s.writeReg32 r v) = vmBase s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) : vmBase (s.writeReg w r v) = vmBase s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) : vmBase (s.writeVReg128 i v) = vmBase s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmBase_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) : vmBase (applyWriteback s wb) = vmBase s := by cases wb <;> [rfl; exact cf_vmBase_writeReg64 s _ _]
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_setPC (s : State) (pc : BitVec 64) : vmPerm (s.setPC pc) = vmPerm s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_setMem (s : State) (m : Memory) : vmPerm (s.setMem m) = m.perm := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_setPState (s : State) (ps : PState) : vmPerm (s.setPState ps) = vmPerm s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : vmPerm (s.writeReg64 r v) = vmPerm s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : vmPerm (s.writeReg32 r v) = vmPerm s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) : vmPerm (s.writeReg w r v) = vmPerm s := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) : vmPerm (s.writeVReg128 i v) = vmPerm s := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓] private theorem cf_vmPerm_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) : vmPerm (applyWriteback s wb) = vmPerm s := by cases wb <;> [rfl; exact cf_vmPerm_writeReg64 s _ _]

attribute [local irreducible] VmPreserved vmBase vmPerm

private def memcpyBudgetFlatSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { pre := sessionMemcpyRegionSpec.pre, post := fun (dst, src, bs) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) }
private theorem subroutine_ok_memcpyBudgetFlat {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a sessionMemcpyRegionBudgetSpec) : subroutine_ok P a memcpyBudgetFlatSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) fun ⟨dst, src, bs⟩ R s0 sf hq => ?_
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyBudgetFlatSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases vmBase_perm_of_vmPreserved hq.1 with ⟨hb, hp⟩; exact ⟨⟨hq.2.1.1, hq.2.1.2, hb, hp⟩, hq.2.2⟩
private def memsetBudgetFlatSpec : Spec (BitVec 64 × BitVec 8 × Nat) :=
  { pre := sessionMemsetRegionSpec.pre, post := fun (dst, byte, len) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0⌝ ∗ (dst ↦ₛ List.replicate len byte) }
private theorem subroutine_ok_memsetBudgetFlat {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a sessionMemsetRegionBudgetSpec) : subroutine_ok P a memsetBudgetFlatSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) fun ⟨dst, byte, len⟩ R s0 sf hq => ?_
  dsimp only [sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec, memsetBudgetFlatSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases vmBase_perm_of_vmPreserved hq.1 with ⟨hb, hp⟩; exact ⟨⟨hq.2.1.1, hq.2.1.2, hb, hp⟩, hq.2.2⟩
private def coinsFillBudgetFlatSpec [LibsignalPlacement] (stk : Nat) : Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) :=
  { pre := (coinsFillSpecPlaced stk).pre, post := fun (dst, len, cur, rest) s0 sf =>
      ⌜sf.trace = s0.trace ∧ vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0⌝ ∗
        (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗ coinsAfterPlaced cur rest (min len rest.length) ∗ stackAt s0.sp stk }
private theorem subroutine_ok_coinsFillBudget_of_flat [LibsignalPlacement] {P : Program} {a : BitVec 64} {stk : Nat}
    (h : subroutine_ok P a (coinsFillBudgetFlatSpec stk)) : subroutine_ok P a (coinsFillBudgetSpecPlaced stk) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) fun ⟨dst, len, cur, rest⟩ R s0 sf hq => ?_
  dsimp only [coinsFillBudgetSpecPlaced, withVmPreserved, coinsFillSpecPlaced, coinsFillBudgetFlatSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; exact ⟨vmPreserved_of_vmBase_perm hq.1.2.1 hq.1.2.2, hq.1.1, hq.2⟩

private theorem csel_min_eq_placed (rem len : Nat) (x1 : BitVec 64) (hrem : rem < 2 ^ 64) (hx1 : x1.toNat = len) :
    (if (BitVec.ofNat 64 rem).ult x1 = true then BitVec.ofNat 64 rem else x1) = BitVec.ofNat 64 (min len rem) := by
  have hx1_bv : x1 = BitVec.ofNat 64 len := by rw [← hx1]; simp
  split <;> rename_i hult <;> simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, hx1, decide_eq_true_eq] at hult
  · rw [show min len rem = rem by omega]
  · rw [show min len rem = len by omega, hx1_bv]
private theorem bv_sub_of_le_placed {a k : Nat} (hk : k ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  conv_lhs => rw [(Nat.sub_add_cancel hk).symm, BitVec.ofNat_add]
  bv_arith
private theorem fill_bytes_eq_placed (rest : List (BitVec 8)) (len : Nat) :
    rest.take (min len rest.length) ++ List.replicate (len - min len rest.length) 0#8 = (rest ++ List.replicate len 0#8).take len := by
  rw [List.take_append]; by_cases hle : len ≤ rest.length
  · rw [show len - min len rest.length = 0 by omega, Nat.min_eq_left hle, show len - rest.length = 0 by omega]; simp
  · have hge : rest.length ≤ len := by omega
    rw [Nat.min_eq_right hge, List.take_length, List.take_of_length_le hge, List.take_replicate, show min (len - rest.length) len = len - rest.length by omega]
private theorem post_merge_placed (dst cur nx lf : BitVec 64) (len : Nat) (rest : List (BitVec 8)) :
    (dst ↦ₛ List.take (min len rest.length) rest) ∗ ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ List.replicate (len - min len rest.length) 0#8) ∗
      (cur ↦ₛ List.take (min len rest.length) rest) ∗ ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ List.drop (min len rest.length) rest) ∗
      (nx ↦₆₄ (cur + BitVec.ofNat 64 (min len rest.length))) ∗ (lf ↦₆₄ BitVec.ofNat 64 (rest.length - min len rest.length)) ⊢
    (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) ∗ tapeAfter2 nx lf cur rest (min len rest.length) := by
  apply Entails.of_eq
  have hdst : (dst ↦ₛ rest.take (min len rest.length)) ∗ ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ List.replicate (len - min len rest.length) 0#8) =
      (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) := by
    rw [← fill_bytes_eq_placed rest len, pointsToBytes_append, List.length_take_of_le (Nat.min_le_right len rest.length)]
  have hcur : (cur ↦ₛ rest) = (cur ↦ₛ List.take (min len rest.length) rest) ∗ ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ List.drop (min len rest.length) rest) := by
    conv_lhs => rw [(List.take_append_drop (min len rest.length) rest).symm]; rw [pointsToBytes_append, List.length_take_of_le (Nat.min_le_right len rest.length)]
  unfold tapeAfter2; rw [← hdst, hcur]; sep_ac_rfl

private theorem stackAt_split_bottom_coins_placed (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]; rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2; rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub, BitVec.sub_add_cancel]
private theorem memRegion_80_words_placed (sp : BitVec 64) :
    memRegion (sp - 80#64) 80 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗ ((sp - 56#64) ↦₆₄ u6) ∗
        ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗ ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗ ((sp - 8#64) ↦₆₄ u0)) := by
  rw [memRegion_split (sp - 80#64) 8 72 (by decide), memRegion_split (sp - 80#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64) 8 56 (by decide), memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide), memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  iterate 10 rw [ProofLib.memRegion_eight]
  rw [show sp - 80#64 + 8#64 = sp - 72#64 by bv_arith, show sp - 72#64 + 8#64 = sp - 64#64 by bv_arith,
    show sp - 64#64 + 8#64 = sp - 56#64 by bv_arith, show sp - 56#64 + 8#64 = sp - 48#64 by bv_arith,
    show sp - 48#64 + 8#64 = sp - 40#64 by bv_arith, show sp - 40#64 + 8#64 = sp - 32#64 by bv_arith,
    show sp - 32#64 + 8#64 = sp - 24#64 by bv_arith, show sp - 24#64 + 8#64 = sp - 16#64 by bv_arith, show sp - 16#64 + 8#64 = sp - 8#64 by bv_arith]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
private theorem stackAt_coinsFill_split_placed (sp : BitVec 64) (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗ ((sp - 56#64) ↦₆₄ u6) ∗
        ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗ ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗ ((sp - 8#64) ↦₆₄ u0)) := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_lhs => rw [heq]; rw [stackAt_split_bottom_coins_placed sp 80 (stk - 80) (by omega), ← heq]; simp only [stackAt, memRegion_80_words_placed]
private theorem stackAt_coinsFill_merge_placed (sp : BitVec 64) (stk : Nat)
    (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      (((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 64#64) ↦₆₄ v7) ∗ ((sp - 56#64) ↦₆₄ v6) ∗
        ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 40#64) ↦₆₄ v4) ∗ ((sp - 32#64) ↦₆₄ v3) ∗ ((sp - 24#64) ↦₆₄ v2) ∗
        ((sp - 16#64) ↦₆₄ v1) ∗ ((sp - 8#64) ↦₆₄ v0)) ⊢ stackAt sp stk := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_rhs => rw [heq]; rw [stackAt_split_bottom_coins_placed sp 80 (stk - 80) (by omega), ← heq]; simp only [stackAt]
  refine sepConj_mono_right ?_; rw [memRegion_80_words_placed sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.refl _))))))))))

section CoinsFillBudgetProof
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem coinsFillBudgetPlaced_ok_of_mem [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memcpyName) sessionMemcpyRegionBudgetSpec)
    (hmemset : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memsetName) sessionMemsetRegionBudgetSpec)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base (coinsFillBudgetSpecPlaced stk) := by
  apply subroutine_ok_coinsFillBudget_of_flat
  have hmc := subroutine_ok_memcpyBudgetFlat hmemcpy; have hms := subroutine_ok_memsetBudgetFlat hmemset
  clear hmemcpy hmemset
  simp only [coinsFillBudgetFlatSpec, coinsFillSpecPlaced, coinsAfterPlaced, tapeAfter2_zero_eq,
    coinsNextPlaced, coinsLeftPlaced, coinsNextSym, coinsLeftSym]
  wp_init x s0; obtain ⟨dst, len, cur, rest⟩ := x; dsimp only at *
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ cur) ∗
          ((cur ↦ₛ rest) ∗ (memRegion dst len ∗ (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ BitVec.ofNat 64 rest.length) ∗
            stackAt s0.sp stk ∗ R)) := Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      have hdisj := IsBlock.disjoint (IsBlock.pointsTo64 (lsρ "libsignal_cli::coins::NEXT.0") cur)
        (IsBlock.pointsToBytes cur rest) (by decide) hpos hmem_disj
      have _ := hdisj.2; have _ := (lsρ "libsignal_cli::coins::NEXT.0" - cur).isLt; omega
    · omega
  set k := min len rest.length
  have hx1 : (s0.readReg64 (Reg.gpr 1#5)).toNat = len := by assumption
  have hlen_lt64 : len < 2 ^ 64 := hx1 ▸ (s0.readReg64 (Reg.gpr 1#5)).isLt
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hcsel := csel_min_eq_placed rest.length len (s0.readReg64 (Reg.gpr 1#5)) hrest_lt64 hx1
  have hrem_sub : BitVec.ofNat 64 rest.length - BitVec.ofNat 64 k = BitVec.ofNat 64 (rest.length - k) := bv_sub_of_le_placed hk_le_rest
  have hlen_sub : s0.readReg64 (Reg.gpr 1#5) - BitVec.ofNat 64 k = BitVec.ofNat 64 (len - k) := by
    rw [(by rw [← hx1]; simp : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 len)]; exact bv_sub_of_le_placed hk_le_len
  have hk_toNat : (BitVec.ofNat 64 k).toNat = (List.take k rest).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hk_le_len hlen_lt64), htake_len]
  have hrem_len_toNat : (BitVec.ofNat 64 (len - k)).toNat = len - k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - k < 2 ^ 64)]
  have hdst_split : memRegion dst len = memRegion dst (rest.take k).length ∗ memRegion (dst + BitVec.ofNat 64 k) (len - k) := by
    (conv_lhs => rw [show len = k + (len - k) by omega]); rw [memRegion_split dst k (len - k) (by omega), htake_len]
  have hcur_split : (cur ↦ₛ rest) = (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
    (conv_lhs => rw [(List.take_append_drop k rest).symm]); rw [pointsToBytes_append, htake_len]
  wp_conv_pre => rw [stackAt_coinsFill_split_placed s0.sp stk hstk hstk']
  wp_pull_exists
  wp_conv_pre => rw [hdst_split, hcur_split]; simp only [sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618 (mid := lsρ memcpyName)
  intro _m_strip1; wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  have hperm1 := cf_vmPerm_of_nsp _hnsp1; wp_call hmc
  have hvmb_sf : vmBase sf = vmBase s0 := by simp only [wp_norm, arm64_norm, *]
  have hvmp_sf : vmPerm sf = vmPerm s0 := by simp only [wp_norm, arm64_norm, *]
  have htr_sf : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
  apply sepWP_seg_ls_vm (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618 (mid := lsρ memsetName)
  intro _m_strip2; wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hperm2 := cf_vmPerm_of_nsp _hnsp2; wp_call hms
  have hvmb_sf1 : vmBase sf_1 = vmBase s0 := by simp only [wp_norm, arm64_norm, *]
  have hvmp_sf1 : vmPerm sf_1 = vmPerm s0 := by simp only [wp_norm, arm64_norm, *]
  have htr_sf1 : sf_1.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
  apply sepWP_seg_ls_vm (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618 (mid := s0.readReg64 Reg.lr)
  intro _m_strip3; wp_steps
  apply SepWP.fold (stackAt_coinsFill_merge_placed s0.sp stk hstk hstk' _ _ _ _ _ _ _ _ _ _) (by sep_focus)
  apply SepWP.fold (post_merge_placed dst cur (lsρ "libsignal_cli::coins::NEXT.0") (lsρ "libsignal_cli::coins::LEFT.0") len rest) (by sep_focus)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
  have hperm3 := cf_vmPerm_of_nsp _hnsp3; wp_done
end CoinsFillBudgetProof

/-- Block `618` (`signal_session_coins_fill`) satisfies `coinsFillBudgetSpecPlaced stk` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliCoinsFillBudgetPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_618).base (coinsFillBudgetSpecPlaced stk) :=
  coinsFillBudgetPlaced_ok_of_mem
    (ls_hook_ok_ultra_of_mem
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG))
    (ls_hook_ok_ultra_of_mem
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG))
    stk hstk hstk'

theorem coinsFill_cro_placed_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok callerProg (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)) := by
  intro cur rest _
  have hcl618 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (cliCoinsFillBudgetPlaced_ok mmpl g W hG tryDecryptSubStack (by decide) (by decide))
  have hcl_caller := ls_subroutine_ok_of_block (callerProg := callerProg) hcl618 hi (by decide)
  exact coinsFillAtBudgetPlaced_of_after0_cro
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcl_caller)

theorem coinsFill_433_cro_placed_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok
        ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact coinsFill_cro_placed_cli mmpl g W hG

theorem coinsFill_507_cro_placed_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok
        ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)) :=
  coinsFill_cro_placed_cli mmpl g W hG

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
