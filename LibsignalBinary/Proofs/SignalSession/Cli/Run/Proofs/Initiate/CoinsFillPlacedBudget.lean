/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `signal_session_coins_fill` Proof

Proves the `VmPreserved`-strengthened `coinsFillSpecPlacedW3` contract for
`signal_session_coins_fill` on block `618` under `[LibsignalPlacement]` and
`SpecsPlacedBudget.AllocContractsFsPlaced A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E (initiateTapeLen)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName memsetName sessionMemcpyRegionSpec sessionMemsetRegionSpec withStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (CoinsFillGhost cliCoinsFillStackPlaced coinsCursorAtPlaced initProgPlaced)
open CryptoVerification.SignalSession.Coins
  (coinsLeftPlaced coinsLeftSym coinsNextPlaced coinsNextSym)
open CryptoVerification.SignalSession.Coins.Placed
  (blkLib_eq_618 blkPC_618 blkPC_618_pairStep_0x18 blkPC_618_pairStep_0x1c blkPl_618)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Relocatable `signal_session_coins_fill` contract preserving `VmPreserved`, `trace`, and `fs`. -/
def coinsFillSpecPlacedW3 [LibsignalPlacement] (stk : Nat) : Spec CoinsFillGhost :=
  withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.len ∧
          x.coins.length < 2 ^ 63 ∧ x.pos + x.len ≤ initiateTapeLen⌝ ∗
          coinsCursorAtPlaced x.p₀ x.coins x.pos ∗
          memRegion x.dst x.len ∗
          stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ VmPreserved s0 sf⌝ ∗
          coinsCursorAtPlaced x.p₀ x.coins (x.pos + x.len) ∗
          (x.dst ↦ₛ ((padCoins x.coins).toList.drop x.pos).take x.len) ∗
          stackAt s0.sp stk
      onPanic := fun _ _ _ => ⌜False⌝
      onOom := fun _ _ _ => ⌜False⌝ }

private theorem cf_stack_split_placed (sp : BitVec 64) {stk : Nat}
    (hge : 80 ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      stackAt (sp - 80#64) (stk - 80) ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp (stk - 80) 10 (by omega)
  have h2 : stk - 80 + 10 * 8 = stk := by omega
  rw [h2] at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [h1, hc10]

private theorem cf_stack_merge_placed (sp : BitVec 64) {stk : Nat}
    (hge : 80 ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    stackAt (sp - 80#64) (stk - 80) ∗
      (((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
       ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
       ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
       ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
       ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) ⊢
      stackAt sp stk := by
  rw [cf_stack_split_placed sp hge hstk64]
  exact sepConj_mono_right
    (Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
          (Entails.sepExists_right v9 (Entails.refl _)))))))))))

private theorem cf_bv_sub {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega

private theorem cf_coins_split (p₀ : BitVec 64) (coins : List (BitVec 8))
    (m k : Nat) (hmk : m + k ≤ coins.length) :
    (p₀ ↦ₛ coins) =
      (p₀ ↦ₛ coins.take m) ∗
      ((p₀ + BitVec.ofNat 64 m) ↦ₛ (coins.drop m).take k) ∗
      ((p₀ + BitVec.ofNat 64 (m + k)) ↦ₛ coins.drop (m + k)) := by
  have heq : coins = coins.take m ++ ((coins.drop m).take k ++ coins.drop (m + k)) := by
    have hdrop : (coins.drop m).drop k = coins.drop (m + k) := List.drop_drop
    rw [← hdrop, List.take_append_drop, List.take_append_drop]
  have hlm : (coins.take m).length = m := by simp; omega
  have hlk : ((coins.drop m).take k).length = k := by simp; omega
  conv => lhs; rw [heq]
  rw [pointsToBytes_append, hlm, pointsToBytes_append, hlk, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem cf_slice_eq (coins : List (BitVec 8)) (pos len : Nat)
    (hpad : pos + len ≤ initiateTapeLen) :
    (coins.drop (min pos coins.length)).take (min (coins.length - min pos coins.length) len) ++
      List.replicate (len - min (coins.length - min pos coins.length) len) 0#8 =
      ((padCoins coins).toList.drop pos).take len := by
  have hpad_list : (padCoins coins).toList =
      coins.take initiateTapeLen ++ List.replicate (initiateTapeLen - coins.length) 0#8 := by
    simp [padCoins]
  apply List.ext_getElem
  · rw [hpad_list]
    simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate,
      initiateTapeLen] at hpad ⊢
    omega
  · intro i h1 h2
    have hi_lt : i < len := by
      rw [hpad_list] at h2
      simp only [List.length_take, List.length_drop, List.length_append,
        List.length_replicate, initiateTapeLen] at h2 hpad
      omega
    simp only [hpad_list, List.getElem_take, List.getElem_drop]
    by_cases hik : i < min (coins.length - min pos coins.length) len
    · have hlt_t : pos + i < (coins.take initiateTapeLen).length := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_left (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop,
        List.getElem_append_left hlt_t, List.getElem_take]
      congr 1; omega
    · have hge_c : (coins.take initiateTapeLen).length ≤ pos + i := by
        simp only [List.length_take]; omega
      rw [List.getElem_append_right (by simp only [List.length_take, List.length_drop]; omega),
        List.getElem_replicate, List.getElem_append_right hge_c, List.getElem_replicate]

private theorem cf_csel_eq (cLen pos len : Nat) (hc : cLen < 2 ^ 64) (hl : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) = true then
      BitVec.ofNat 64 (cLen - min pos cLen)
    else BitVec.ofNat 64 len) =
      BitVec.ofNat 64 (min (cLen - min pos cLen) len) := by
  have hleft : cLen - min pos cLen < 2 ^ 64 := by omega
  have hult : (BitVec.ofNat 64 (cLen - min pos cLen)).ult (BitVec.ofNat 64 len) =
      decide (cLen - min pos cLen < len) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hl]
  rw [hult]
  by_cases hlt : cLen - min pos cLen < len
  · simp [hlt, Nat.min_eq_left (Nat.le_of_lt hlt)]
  · simp [hlt, Nat.min_eq_right (Nat.le_of_not_lt hlt)]

private theorem cf_dst_join (dst : BitVec 64) (coins : List (BitVec 8))
    (pos len : Nat) (hpad : pos + len ≤ initiateTapeLen) (R' : SepProp) :
    (((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ∗ R') =
    ((dst ↦ₛ ((padCoins coins).toList.drop pos).take len) ∗ R') := by
  have hmid : ((coins.drop (min pos coins.length)).take
      (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hmerge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
          List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
        (dst ↦ₛ (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) =
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    rw [sepConj_comm]
    conv => lhs; arg 2; arg 1; arg 2; rw [← hmid]
    rw [← pointsToBytes_append, cf_slice_eq coins pos len hpad]
  rw [← sepConj_assoc, hmerge]

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_setPState (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).fs = s.fs := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_fs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by
  cases wb with
  | none => rfl
  | some p => exact cf_fs_writeReg64 s p.1 p.2

private def vmBase (s : State) :=
  (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail,
    fun (fd : Nat) (_ : 3 ≤ fd) (_ : fd < 2 ^ 31) => s.fs.fds (BitVec.ofNat 64 fd))

private def vmPerm (s : State) :=
  s.mem.perm

private theorem vmBase_perm_of_vmPreserved {s0 sf : State} (h : VmPreserved s0 sf) :
    vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0 := by
  unfold vmBase vmPerm
  exact ⟨Prod.ext h.1.1 (Prod.ext h.1.2.1 (Prod.ext h.1.2.2 (Prod.ext h.2.1
    (funext fun fd => funext fun h1 => funext fun h2 => h.fdsHiFrame fd h1 h2)))),
    funext h.perm_eq⟩

private theorem vmPreserved_of_vmBase_perm {s0 sf : State}
    (hb : vmBase sf = vmBase s0) (hp : vmPerm sf = vmPerm s0) :
    VmPreserved s0 sf := by
  unfold vmBase at hb
  unfold vmPerm at hp
  exact ⟨⟨congrArg Prod.fst hb,
    congrArg (fun x => x.2.1) hb,
    congrArg (fun x => x.2.2.1) hb⟩,
    congrArg (fun x => x.2.2.2.1) hb,
    fun a => congrFun hp a,
    fun fd h1 h2 => congrFun (congrFun (congrFun (congrArg (fun x => x.2.2.2.2) hb) fd) h1) h2⟩

private theorem cf_vmPerm_of_nsp {s sm : State} {m : Memory}
    (h : ProofLib.NonSyscallPreserved s (sm.setMem m)) :
    m.perm = vmPerm s := by
  unfold vmPerm
  exact (show (sm.setMem m).mem.perm = m.perm from by cases sm; rfl) ▸ h.2.1

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_setPC (s : State) (pc : BitVec 64) :
    vmBase (s.setPC pc) = vmBase s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_setMem (s : State) (m : Memory) :
    vmBase (s.setMem m) = vmBase s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_setPState (s : State) (ps : PState) :
    vmBase (s.setPState ps) = vmBase s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmBase (s.writeReg64 r v) = vmBase s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmBase (s.writeReg32 r v) = vmBase s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    vmBase (s.writeReg w r v) = vmBase s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    vmBase (s.writeVReg128 i v) = vmBase s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmBase_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    vmBase (applyWriteback s wb) = vmBase s := by
  cases wb with
  | none => rfl
  | some p => exact cf_vmBase_writeReg64 s p.1 p.2

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_setPC (s : State) (pc : BitVec 64) :
    vmPerm (s.setPC pc) = vmPerm s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_setMem (s : State) (m : Memory) :
    vmPerm (s.setMem m) = m.perm := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_setPState (s : State) (ps : PState) :
    vmPerm (s.setPState ps) = vmPerm s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmPerm (s.writeReg64 r v) = vmPerm s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmPerm (s.writeReg32 r v) = vmPerm s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    vmPerm (s.writeReg w r v) = vmPerm s := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    vmPerm (s.writeVReg128 i v) = vmPerm s := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem cf_vmPerm_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    vmPerm (applyWriteback s wb) = vmPerm s := by
  cases wb with
  | none => rfl
  | some p => exact cf_vmPerm_writeReg64 s p.1 p.2

attribute [local irreducible] VmPreserved vmBase vmPerm

private def memcpyFlatSpec [LibsignalPlacement] (k : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { pre := (withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec k).keepsFs).pre
    post := fun (dst, src, bs) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs ∧
        vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0 ∧
        LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
        (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp k
    onPanic := fun _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

private theorem subroutine_ok_memcpyFlat [LibsignalPlacement] {prog : Program} {a : BitVec 64}
    {k : Nat}
    (h : subroutine_ok prog a
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec k).keepsFs)) :
    subroutine_ok prog a (memcpyFlatSpec k) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) ?_
  rintro ⟨dst, src, bs⟩ R s0 sf hq
  dsimp only [withLsRoCl, Spec.keepsFs, withStack,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyFlatSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨hcrl, hfs, hvm, ⟨hx0, htr⟩, hmem⟩
  rcases vmBase_perm_of_vmPreserved hvm with ⟨hvmb, hvmp⟩
  exact ⟨⟨hx0, htr, hfs, hvmb, hvmp, hcrl⟩, hmem⟩

private def memsetFlatSpec [LibsignalPlacement] (k : Nat) :
    Spec (BitVec 64 × BitVec 8 × Nat) :=
  { pre := (withLsRoCl lsmpl (withStack sessionMemsetRegionSpec k).keepsFs).pre
    post := fun (dst, byte, len) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs ∧
        vmBase sf = vmBase s0 ∧ vmPerm sf = vmPerm s0 ∧
        LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
        (dst ↦ₛ List.replicate len byte) ∗ stackAt s0.sp k
    onPanic := fun _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

private theorem subroutine_ok_memsetFlat [LibsignalPlacement] {prog : Program} {a : BitVec 64}
    {k : Nat}
    (h : subroutine_ok prog a
      (withLsRoCl lsmpl (withStack sessionMemsetRegionBudgetSpec k).keepsFs)) :
    subroutine_ok prog a (memsetFlatSpec k) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) ?_
  rintro ⟨dst, byte, len⟩ R s0 sf hq
  dsimp only [withLsRoCl, Spec.keepsFs, withStack,
    sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec, memsetFlatSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨hcrl, hfs, hvm, ⟨hx0, htr⟩, hmem⟩
  rcases vmBase_perm_of_vmPreserved hvm with ⟨hvmb, hvmp⟩
  exact ⟨⟨hx0, htr, hfs, hvmb, hvmp, hcrl⟩, hmem⟩

set_option maxHeartbeats 800000 in
/-- Proves `coinsFillSpecPlacedW3` on block `618` from `sessionMemcpyRegionBudgetSpec` and `sessionMemsetRegionBudgetSpec`. -/
theorem signal_session_coins_fill_placed_ok_of_mc_ms [LibsignalPlacement]
    {H : LibsignalHooks} {stk : Nat} (hstk : 80 ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hmc : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionBudgetSpec (stk - 80)).keepsFs))
    (hms : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (lsρ memsetName)
      (withLsRoCl lsmpl (withStack sessionMemsetRegionBudgetSpec (stk - 80)).keepsFs)) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base
      (coinsFillSpecPlacedW3 stk) := by
  have hmc' := subroutine_ok_memcpyFlat hmc
  have hms' := subroutine_ok_memsetFlat hms
  clear hmc hms
  simp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded,
    coinsCursorAtPlaced, coinsNextPlaced, coinsLeftPlaced, coinsNextSym, coinsLeftSym]
  wpp_init x s0
  obtain ⟨dst, len, p₀, coins, pos⟩ := x
  dsimp only at *
  have hcoins63 : coins.length < 2 ^ 63 := by assumption
  have hpad : pos + len ≤ initiateTapeLen := by assumption
  have htape : initiateTapeLen = 192 := rfl
  have hc64 : coins.length < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have hleft64 : coins.length - min pos coins.length < 2 ^ 64 := by omega
  have hk64 : min (coins.length - min pos coins.length) len < 2 ^ 64 := by omega
  have hmk_le : min pos coins.length + min (coins.length - min pos coins.length) len ≤
      coins.length := by omega
  have hrem_le64 : len - min (coins.length - min pos coins.length) len ≤ 2 ^ 64 := by omega
  have hmid_len :
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length =
      min (coins.length - min pos coins.length) len := by simp
  have hcsel := cf_csel_eq coins.length pos len hc64 hlen64
  have hnext_bv1 :
      p₀ + BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show min pos coins.length + min (coins.length - min pos coins.length) len =
        min (pos + len) coins.length by omega]
  have hnext_bv2 :
      p₀ + (BitVec.ofNat 64 (min pos coins.length) +
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) =
      p₀ + BitVec.ofNat 64 (min (pos + len) coins.length) := by
    rw [← BitVec.add_assoc, hnext_bv1]
  have hleft_bv :
      BitVec.ofNat 64 (coins.length - min pos coins.length) -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (coins.length - min (pos + len) coins.length) := by
    rw [cf_bv_sub (by omega) hleft64,
      show (coins.length - min pos coins.length) -
          min (coins.length - min pos coins.length) len =
        coins.length - min (pos + len) coins.length by omega]
  have hrem_bv :
      BitVec.ofNat 64 len -
        BitVec.ofNat 64 (min (coins.length - min pos coins.length) len) =
      BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len) :=
    cf_bv_sub (by omega) hlen64
  have htoNat_k :
      (BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)).toNat =
      ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, hmid_len]
  have htoNat_rem :
      (BitVec.ofNat 64 (len - min (coins.length - min pos coins.length) len)).toNat =
      len - min (coins.length - min pos coins.length) len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdst_split : memRegion dst len =
      memRegion dst ((coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)).length ∗
      memRegion (dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len))
        (len - min (coins.length - min pos coins.length) len) := by
    conv =>
      lhs
      rw [show len = min (coins.length - min pos coins.length) len +
        (len - min (coins.length - min pos coins.length) len) by omega]
    rw [ProofLib.memRegion_split dst _ _ (by omega), hmid_len]
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  apply SepWPp.of_sepWP_ret
  wp_conv_pre =>
    rw [cf_stack_split_placed s0.sp hstk hstk64]
  wp_pull_exists
  wp_conv_pre =>
    rw [cf_coins_split p₀ coins (min pos coins.length)
      (min (coins.length - min pos coins.length) len) hmk_le, hdst_split]
    simp only [sepConj_assoc]
  apply SepWP.seq_frozen (fun _ _ hcrl hkf => hcrl.of_keepsFrozen hkf) hcrl0
    (mid := lsρ memcpyName)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618
    (mid := lsρ memcpyName)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  have hperm1 := cf_vmPerm_of_nsp _hnsp1
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun ⟨hcl1, hro1⟩ => ?_
  wp_call hmc'
  have hcrl1' : LibsignalCodeRoLoaded lsmpl sf.mem := by assumption
  have hvmb_sf : vmBase sf = vmBase s0 := by simp only [wp_norm, arm64_norm, *]
  have hvmp_sf : vmPerm sf = vmPerm s0 := by simp only [wp_norm, arm64_norm, *]
  apply SepWP.seq_frozen (fun _ _ hcrl hkf => hcrl.of_keepsFrozen hkf) hcrl1'
    (mid := lsρ memsetName)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618
    (mid := lsρ memsetName)
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hperm2 := cf_vmPerm_of_nsp _hnsp2
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun ⟨hcl2, hro2⟩ => ?_
  wp_call hms'
  have htr_all : sf_1.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
  have hfs_all : sf_1.fs = s0.fs := by simp only [wp_norm, arm64_norm, *]
  have hvmb_sf1 : vmBase sf_1 = vmBase s0 := by simp only [wp_norm, arm64_norm, *]
  have hvmp_sf1 : vmPerm sf_1 = vmPerm s0 := by simp only [wp_norm, arm64_norm, *]
  have hcoins_merge :
      (p₀ ↦ₛ coins.take (min pos coins.length)) ∗
      ((p₀ + BitVec.ofNat 64 (min pos coins.length)) ↦ₛ
        (coins.drop (min pos coins.length)).take
          (min (coins.length - min pos coins.length) len)) ∗
      ((p₀ + BitVec.ofNat 64 (min pos coins.length +
        min (coins.length - min pos coins.length) len)) ↦ₛ
        coins.drop (min pos coins.length +
          min (coins.length - min pos coins.length) len)) ⊢
      (p₀ ↦ₛ coins) :=
    Entails.of_eq (cf_coins_split p₀ coins (min pos coins.length)
      (min (coins.length - min pos coins.length) len) hmk_le).symm
  have hdst_merge :
      ((dst + BitVec.ofNat 64 (min (coins.length - min pos coins.length) len)) ↦ₛ
        List.replicate (len - min (coins.length - min pos coins.length) len) 0#8) ∗
      (dst ↦ₛ (coins.drop (min pos coins.length)).take
        (min (coins.length - min pos coins.length) len)) ⊢
      (dst ↦ₛ ((padCoins coins).toList.drop pos).take len) := by
    have hj := cf_dst_join dst coins pos len hpad emp
    simp only [sepConj_emp] at hj
    exact Entails.of_eq hj
  apply sepWP_seg_ls_vm
    (Q := (blkPC_618).rebase (blkPl_618).base (hooksException H)) blkLib_eq_618
    (mid := s0.readReg64 Reg.lr)
  intro _m_strip3
  wp_steps
  apply SepWP.fold (cf_stack_merge_placed s0.sp hstk hstk64 _ _ _ _ _ _ _ _ _ _) (by sep_focus)
  apply SepWP.fold hcoins_merge (by sep_focus)
  apply SepWP.fold hdst_merge (by sep_focus)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
  have hperm3 := cf_vmPerm_of_nsp _hnsp3
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨fun hmR => ?_, by simp only [wp_norm, arm64_norm, *], ?_⟩
  · simp only [sepConj_assoc] at hmR ⊢
    refine Satisfies.of_entails hmR (Entails.pure_right ?_ ?_)
    · exact ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        vmPreserved_of_vmBase_perm
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])⟩
    · exact Entails.of_eq (by sep_ac_rfl)
  · rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩

/-- Weakens budget `coinsFillSpecPlacedW3` (with `VmPreserved`) to `Initiate.coinsFillSpecPlacedW3`. -/
theorem coinsFill_plain_of_budget [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {stk : Nat}
    (h : subroutine_ok prog entry (coinsFillSpecPlacedW3 stk)) :
    subroutine_ok prog entry
      (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 stk) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) (fun _ _ _ _ hq => ?_)
  dsimp only [coinsFillSpecPlacedW3,
    CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3,
    withLsCodeRoLoaded] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

/-- Proves `coinsFillSpecPlacedW3` on block `618` under `AllocContractsFsPlaced A lim H`. -/
theorem signal_session_coins_fill_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (hstk : cliCoinsFillStackPlaced ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base
      (coinsFillSpecPlacedW3 stk) := by
  have hge : 80 ≤ stk := by unfold cliCoinsFillStackPlaced extHookStack at hstk; omega
  have hstk_ext : extHookStack ≤ stk - 80 := by unfold cliCoinsFillStackPlaced at hstk; omega
  have hstk_le : stk - 80 ≤ 2 ^ 64 := by omega
  exact signal_session_coins_fill_placed_ok_of_mc_ms hge hstk64
    (ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_618).rebase (blkPl_618).base H)
      (hFs.session_memcpy_region (stk - 80) hstk_ext hstk_le))
    (ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_618).rebase (blkPl_618).base H)
      (hFs.session_memset_region (stk - 80) hstk_ext hstk_le))

/-- Transfers `signal_session_coins_fill_placed_ok` to `initProgPlaced mmpl gh W` (`lsProg_521`). -/
theorem signal_session_coins_fill_placed_ok_at_init [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (hFs : AllocContractsFsPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {stk : Nat} (hstk : cliCoinsFillStackPlaced ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsRoCl lsmpl (coinsFillSpecPlacedW3 stk)) := by
  have h618 : subroutine_ok ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 618) (coinsFillSpecPlacedW3 stk) :=
    signal_session_coins_fill_placed_ok hFs hstk hstk64
  have hmono : subroutine_ok ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 stk)) :=
    subroutine_ok_mono h618
      (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2)
      (fun _ _ _ _ hq => hq)
  exact ls_subroutine_ok_rocl_of_block (callerProg := initProgPlaced mmpl gh W) hmono

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
