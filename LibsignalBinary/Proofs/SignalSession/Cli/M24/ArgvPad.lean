/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Strlen
public import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WP.Structural

/-!
# SWAR-Padded Read-Only `argv` Predicates & Honest `strlenSpecROSat` (`Cli/M24/ArgvPad.lean`)

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Additive SWAR-padded read-only `argv` vocabulary, Linux initial-stack duplication lemma keeping
  the SWAR pad from `InitialStackInfo.dup_argv_cstr_padded`, pad-forgetting bridges to the existing
  unpadded `argvAtRO` / `argvAtROP` predicates, and the honest `strlenSpecROSat` specification
  discharged both for the idealized `strlenHook` (`toSat`) and for the real `musl` AArch64 `strlen`
  machine words (`ProofLib.StdStartup.muslStrlenWords`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad

open Arm64 ProofLib
open Arm64.Process (ArgsValid ElfImage ProcessInputs bytesOfString initFsState)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsRoCl)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced strlenHook)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk IsSendOverCap IsStdinOverCap MainCaseB2 MainGhost MainPost MainResult RunAnswer)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (cliExternsPlaced_strlen)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen
  (StrlenSwarPadBound strlen_strlenSpecRO_padRO_withVmPreserved_ok withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (argvAtROP argvAtROPPrefix)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (strlenHook_ro_ok strlenHook_vmPreserved strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (B2MainEntryFacts argvAtRO b2MainEntryPreFine b2MainFrameFine b2MainSpecTightNeedLocksFineAt
   cStrAtRO)
open ProofLib.StdStartup (InitialStackInfo StackLayout muslStrlenWords)

/-! ## 1. SWAR-Padded Read-Only C-String & `argv` Predicates -/

/-- Alias for `HookDischarge.Libc.Strlen.StrlenSwarPadBound`: `8 ≤ (p.toNat + s.length) % 8 + 1 + pad.length`
and `p.toNat + (s.length + 1 + pad.length) < 2 ^ 64`. -/
abbrev StrlenPadOk (p : BitVec 64) (s pad : List (BitVec 8)) : Prop :=
  StrlenSwarPadBound p s pad

/-- Read-only NUL-terminated byte slice `s` at `p` together with SWAR read-ahead padding `pad`
satisfying `StrlenSwarPadBound p s pad` (`p ↦ᵣ (s ++ [0#8] ++ pad)`). -/
@[expose] def cStrAtROPad (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  ∃∗ pad : List (BitVec 8), ⌜StrlenSwarPadBound p s pad⌝ ∗ (p ↦ᵣ (s ++ [0#8] ++ pad))

/-- SWAR-padded read-only C `argv` pointer table at `a` (twin of `CliStrictPlaced.argvAtRO` /
`F3Relink.Startup.argvAtRO`). -/
@[expose] def argvAtROPad : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ᵣ p) ∗ cStrAtROPad p s ∗ argvAtROPad (a + 8#64) ss

/-- SWAR-padded read-only pointer-indexed C `argv` table at `a` (twin of
`B2MainFrameComposeBudget.argvAtROP`). -/
@[expose] def argvAtROPPad : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, (p, s) :: rest => (a ↦₆₄ᵣ p) ∗ cStrAtROPad p s ∗ argvAtROPPad (a + 8#64) rest

/-- SWAR-padded read-only prefix of `argvAtROPPad` without the trailing NUL pointer slot (twin of
`B2MainFrameComposeBudget.argvAtROPPrefix`). -/
@[expose] def argvAtROPPadPrefix : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | _, [] => emp
  | a, (p, s) :: ps => (a ↦₆₄ᵣ p) ∗ cStrAtROPad p s ∗ argvAtROPPadPrefix (a + 8#64) ps

/-- SWAR-padded twin of `CliStrictPlaced.b2MainFrameFine`. -/
@[expose] def b2MainFrameFinePad {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs)
    (s : State) : SepProp :=
  argvAtROPad (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool lim st s ∗ Statics

/-- SWAR-padded twin of `CliStrictPlaced.b2MainEntryPreFine`. -/
@[expose] def b2MainEntryPreFinePad (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (stk : Nat)
    (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  ⌜CodeOk s.mem ∧ stk ≤ s.sp.toNat⌝ ∗ b2MainFrameFinePad A lim st stk Statics i s

/-- SWAR-padded twin of `CliStrictPlaced.b2MainSpecTightNeedLocksFineAt`. -/
@[expose] def b2MainSpecTightNeedLocksFineAtPad (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧
      B2MainEntryFacts inputsOf g.i s ∧ stk ≤ s.sp.toNat⌝ ∗
      b2MainFrameFinePad A lim st stk Statics g.i s
  post := fun g s0 sf =>
    ⌜MainPost g.r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem argvAtROPad_entails_argvAtROPPad (a : BitVec 64) (ss : List (List (BitVec 8))) :
    argvAtROPad a ss ⊢
      ∃∗ ps : List (BitVec 64 × List (BitVec 8)), ⌜ps.map (·.2) = ss⌝ ∗ argvAtROPPad a ps := by
  induction ss generalizing a with
  | nil =>
    exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _))
  | cons s ss ih =>
    simp only [argvAtROPad]
    apply Entails.sepExists_elim
    intro p
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (ih (a + 8#64)))) ?_
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro ps
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) ?_
    apply Entails.pure_left
    rintro rfl
    exact Entails.sepExists_right ((p, s) :: ps)
      (Entails.pure_right rfl (Entails.of_eq (by simp only [argvAtROPPad]; sep_ac_rfl)))

theorem argvAtROPPad_append (a : BitVec 64) (xs ys : List (BitVec 64 × List (BitVec 8))) :
    argvAtROPPad a (xs ++ ys) =
      argvAtROPPadPrefix a xs ∗ argvAtROPPad (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  induction xs generalizing a with
  | nil =>
    simp only [List.nil_append, argvAtROPPadPrefix, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj]
  | cons x xs ih =>
    rcases x with ⟨p, s⟩
    simp only [List.cons_append, argvAtROPPad, argvAtROPPadPrefix, List.length_cons, ih (a + 8#64)]
    have haddr : a + 8#64 + BitVec.ofNat 64 (8 * xs.length) =
        a + BitVec.ofNat 64 (8 * (xs.length + 1)) := by
      have : 8 * (xs.length + 1) = 8 + 8 * xs.length := by omega
      rw [this, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
    sep_ac_rfl

/-! ## 2. Startup `argv` Duplication Keeping the SWAR Pad (`argvTable_dup_argvAtROPad`) -/

/-- Duplicate `argvAtROPad sl.argvTableAddr inputs.argv` out of the initial Linux stack's read-only
`argv` pointer table and `upperStrBytes` region, retaining the SWAR read-ahead padding witness from
`InitialStackInfo.dup_argv_cstr_padded`. -/
theorem argvTable_dup_argvAtROPad {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hinfo : InitialStackInfo img inputs s0) (hargs : ArgsValid inputs) :
    let sl := StackLayout.of img inputs
    ((sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtROPad sl.argvTableAddr inputs.argv ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
  dsimp only
  let sl := StackLayout.of img inputs
  have hlen : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  suffices hgen : ∀ (k : Nat), k ≤ inputs.argv.length →
      (((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtROPad (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) (inputs.argv.drop k) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) by
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.drop_zero] using
      hgen 0 (Nat.zero_le _)
  intro k hk
  induction hd : inputs.argv.length - k generalizing k with
  | zero =>
    have hk_eq : k = inputs.argv.length := by omega
    subst hk_eq
    have hd1 : sl.argvAddrs.drop inputs.argv.length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.drop_length, List.nil_append]
    simp only [argvAtROPad, pointsToWords64RO_cons, pointsToWords64RO_nil, sepConj_emp]
    exact Entails.trans (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm))
      (Entails.of_eq (by sep_ac_rfl))
  | succ rem ih =>
    have hk_lt : k < inputs.argv.length := by omega
    have hk_lt' : k < sl.argvAddrs.length := by omega
    have hd_a : sl.argvAddrs.drop k = sl.argvAddrs[k] :: sl.argvAddrs.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt'
    have hd_v : inputs.argv.drop k = inputs.argv[k] :: inputs.argv.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hd_a, hd_v, List.cons_append]
    simp only [argvAtROPad, pointsToWords64RO_cons]
    have hstep_addr : (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) + 8#64 =
        sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact congrArg (sl.argvTableAddr + BitVec.ofNat 64 ·) (by omega)
    rw [hstep_addr]
    obtain ⟨pad, _hno0, _hpad8, hswar, htop, hdup_str⟩ := hinfo.dup_argv_cstr_padded hargs hk_lt
    have h48_lt : (2 ^ 48 : Nat) < 2 ^ 64 := by decide
    have hpad_ok : StrlenSwarPadBound sl.argvAddrs[k] inputs.argv[k] pad :=
      ⟨hswar, by dsimp only [sl]; omega⟩
    have habs_str : (sl.argvBase ↦ᵣ sl.upperStrBytes) ⊢
        cStrAtROPad sl.argvAddrs[k] inputs.argv[k] ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
      have hdup' : (sl.argvBase ↦ᵣ sl.upperStrBytes) =
          (sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8] ++ pad)) ∗
            (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
        dsimp only [sl]
        exact hdup_str.symm.trans (sepConj_comm _ _)
      exact Entails.trans (Entails.of_eq hdup')
        (sepConj_mono_left (Entails.sepExists_right pad (Entails.pure_right hpad_ok (Entails.refl _))))
    have hih := ih (k + 1) (by omega) (by omega)
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.sepExists_right sl.argvAddrs[k] (Entails.refl _)))
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm))) ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          (cStrAtROPad sl.argvAddrs[k] inputs.argv[k] ∗
            (sl.argvBase ↦ᵣ sl.upperStrBytes))))
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right habs_str))))
      ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        cStrAtROPad sl.argvAddrs[k] inputs.argv[k] ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes)))
      (Entails.of_eq (by sep_ac_rfl))
      ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hih)))
      (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Pad-Forgetting Bridges (`argvAtROPad` / `argvAtROPPad` → `argvAtRO` / `argvAtROP`) -/

theorem cStrAtROPad_entails_exists_frame (p : BitVec 64) (s : List (BitVec 8)) :
    cStrAtROPad p s ⊢ ∃∗ Rpad : SepProp, cStrAtRO p s ∗ Rpad := by
  unfold cStrAtROPad
  apply Entails.sepExists_elim
  intro pad
  apply Entails.pure_left
  intro _hswar
  rw [pointsToBytesRO_append p (s ++ [0#8]) pad]
  exact Entails.sepExists_right ((p + BitVec.ofNat 64 (s ++ [0#8]).length) ↦ᵣ pad)
    (Entails.refl _)

theorem argvAtROPad_entails_argvAtRO_frame (a : BitVec 64) (ss : List (List (BitVec 8))) :
    argvAtROPad a ss ⊢ ∃∗ Rpad : SepProp, argvAtRO a ss ∗ Rpad := by
  induction ss generalizing a with
  | nil =>
    exact Entails.sepExists_right emp (Entails.of_eq (sepConj_emp _).symm)
  | cons s ss ih =>
    simp only [argvAtROPad]
    apply Entails.sepExists_elim
    intro p
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono (cStrAtROPad_entails_exists_frame p s) (ih (a + 8#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro R2
    apply Entails.sepExists_elim; intro R1
    refine Entails.sepExists_right (R1 ∗ R2) ?_
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.sepExists_right p (Entails.refl _)))
    exact Entails.of_eq (by sep_ac_rfl)

theorem argvAtROPPad_entails_argvAtROP_frame (a : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) :
    argvAtROPPad a ps ⊢ ∃∗ Rpad : SepProp, argvAtROP a ps ∗ Rpad := by
  induction ps generalizing a with
  | nil =>
    exact Entails.sepExists_right emp (Entails.of_eq (sepConj_emp _).symm)
  | cons hd rest ih =>
    rcases hd with ⟨p, s⟩
    simp only [argvAtROPPad, argvAtROP]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono (cStrAtROPad_entails_exists_frame p s) (ih (a + 8#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro R2
    apply Entails.sepExists_elim; intro R1
    exact Entails.sepExists_right (R1 ∗ R2) (Entails.of_eq (by sep_ac_rfl))

theorem cStrAtROPad_anyHeap_entails (p : BitVec 64) (s : List (BitVec 8)) :
    cStrAtROPad p s ∗ anyHeap ⊢ cStrAtRO p s ∗ anyHeap := by
  refine Entails.trans (sepConj_mono_left (cStrAtROPad_entails_exists_frame p s)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro Rpad
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem argvAtROPad_anyHeap_entails (a : BitVec 64) (ss : List (List (BitVec 8))) :
    argvAtROPad a ss ∗ anyHeap ⊢ argvAtRO a ss ∗ anyHeap := by
  refine Entails.trans (sepConj_mono_left (argvAtROPad_entails_argvAtRO_frame a ss)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro Rpad
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem argvAtROPPad_anyHeap_entails (a : BitVec 64)
    (ps : List (BitVec 64 × List (BitVec 8))) :
    argvAtROPPad a ps ∗ anyHeap ⊢ argvAtROP a ps ∗ anyHeap := by
  refine Entails.trans (sepConj_mono_left (argvAtROPPad_entails_argvAtROP_frame a ps)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro Rpad
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem b2MainFrameFinePad_entails_frame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) :
    b2MainFrameFinePad A lim st stk Statics i s ⊢
      ∃∗ Rpad : SepProp, b2MainFrameFine A lim st stk Statics i s ∗ Rpad := by
  unfold b2MainFrameFinePad b2MainFrameFine
  refine Entails.trans (sepConj_mono_left (argvAtROPad_entails_argvAtRO_frame _ _)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro Rpad
  exact Entails.sepExists_right Rpad (Entails.of_eq (by sep_ac_rfl))

theorem satisfies_argvAtRO_of_argvAtROPad {m : Memory} {a : BitVec 64}
    {ss : List (List (BitVec 8))} {Fr : SepProp}
    (hm : m ⊨ argvAtROPad a ss ∗ Fr) :
    ∃ Fr' : SepProp, m ⊨ argvAtRO a ss ∗ Fr' := by
  have hm' := Satisfies.mono (sepConj_mono_left (argvAtROPad_entails_argvAtRO_frame a ss)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  rcases hm' with ⟨Rpad, hr⟩
  exact ⟨Rpad ∗ Fr, by rwa [← sepConj_assoc]⟩

theorem sepWPp_forget_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P Rpad : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hoom : ∀ sf, oom sf ∗ Rpad ⊢ oom sf)
    (hwp : SepWPp prog ret s P
      (fun sf Pf => Q sf (Pf ∗ Rpad))
      (fun sf Pf => Qp sf (Pf ∗ Rpad))
      oom) :
    SepWPp prog ret s (P ∗ Rpad) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, hout⟩ := hwp (Rpad ∗ R) hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hQ⟩ | ⟨hpan, Pf, hmf, hQp⟩ | ⟨hoom_s, hmf⟩
  · exact Or.inl ⟨hpc, hrun, Pf ∗ Rpad, by rwa [sepConj_assoc], hQ⟩
  · exact Or.inr (Or.inl ⟨hpan, Pf ∗ Rpad, by rwa [sepConj_assoc], hQp⟩)
  · refine Or.inr (Or.inr ⟨hoom_s, ?_⟩)
    rw [← sepConj_assoc] at hmf
    exact Satisfies.mono (sepConj_mono_left (hoom sf)) hmf

/-- Contravariant `toSat` bridge: any `subroutine_ok` for unpadded
`b2MainSpecTightNeedLocksFineAt` immediately yields `subroutine_ok` for
`b2MainSpecTightNeedLocksFineAtPad` (framing the SWAR pad bytes and absorbing them into `anyHeap`
on normal return and panic). -/
theorem subroutine_ok_b2MainSpecTightNeedLocksFineAtPad_of_unpadded
    {prog : Program} {entry libcAddr : BitVec 64} {CodeOk : Memory → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (h : subroutine_ok prog entry
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf)) :
    subroutine_ok prog entry
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk A lim st stk Statics Run inputsOf) := by
  apply subroutine_ok.of_codeLoaded
  intro g R s0 hpc hrun hpre hsp _hL
  dsimp only [b2MainSpecTightNeedLocksFineAtPad] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hm' := Satisfies.mono
    (sepConj_mono_left (b2MainFrameFinePad_entails_frame A lim st stk Statics g.i s0)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  rcases hm' with ⟨Rpad, hmR⟩
  have hpre' : s0.mem ⊨
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf).pre g s0 ∗
        (Rpad ∗ R) := by
    dsimp only [b2MainSpecTightNeedLocksFineAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by rwa [← sepConj_assoc]⟩
  refine (h.to_outcome g (Rpad ∗ R) s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [b2MainSpecTightNeedLocksFineAt, b2MainSpecTightNeedLocksFineAtPad] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    have eq1 : ((⌜MainPost g.r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗
          stackAt s0.sp stk ∗ anyHeap) ∗ (Rpad ∗ R)) =
        (⌜MainPost g.r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗
          stackAt s0.sp stk ∗ (anyHeap ∗ Rpad)) ∗ R := by
      sep_ac_rfl
    rw [eq1]
    exact sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))))
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [b2MainSpecTightNeedLocksFineAt, b2MainSpecTightNeedLocksFineAtPad] at hp ⊢
    refine Satisfies.mono ?_ hp
    have eq1 : ((⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ (Rpad ∗ R)) =
        (⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ (anyHeap ∗ Rpad)) ∗ R := by
      sep_ac_rfl
    rw [eq1]
    exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## 4. Honest `strlenSpecROSat`, Ideal `strlenHook` (`toSat`), & Real `muslStrlenWords` -/

/-- Honest SWAR-padded read-only `strlen` consumer specification for `main` Hop M1:
`withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack))` directly reusing
`HookDischarge.Libc.Strlen.withStrlenPadRO` / `StrlenSwarPadBound`. -/
abbrev strlenSpecROSat (hookStack : Nat) : Spec (BitVec 64 × List (BitVec 8)) :=
  withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack))

/-- Duplicate the read-only trailing pad `((p + (s.length + 1)) ↦ᵣ pad)` out of
`p ↦ᵣ (s ++ [0#8] ++ pad)` so one copy feeds `(withStrlenPadRO (strlenSpecRO hookStack)).pre`
and the other remains in the separation-logic frame to re-form `cStrAtROPad p s`. -/
theorem pointsToBytesRO_pad_entails_withStrlenPadRO (p : BitVec 64) (s pad : List (BitVec 8))
    (hswar : StrlenSwarPadBound p s pad) :
    (p ↦ᵣ (s ++ [0#8] ++ pad)) ⊢
      (∃∗ pad' : List (BitVec 8),
        ⌜StrlenSwarPadBound p s pad'⌝ ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad')) ∗
      LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.cStrAtRO p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) := by
  have hlen : (s ++ [0#8]).length = s.length + 1 := by simp
  have hsplit :
      (p ↦ᵣ (s ++ [0#8] ++ pad)) =
        ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗
          (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.cStrAtRO p s ∗
            ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)) := by
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.cStrAtRO]
    calc (p ↦ᵣ (s ++ [0#8] ++ pad))
      _ = (p ↦ᵣ (s ++ [0#8])) ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) := by
          rw [pointsToBytesRO_append p (s ++ [0#8]) pad, hlen]
      _ = (p ↦ᵣ (s ++ [0#8])) ∗
            (((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗
              ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)) := by
          rw [pointsToBytesRO_dup]
      _ = ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗
            ((p ↦ᵣ (s ++ [0#8])) ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)) := by
          sep_ac_rfl
  rw [hsplit]
  exact sepConj_mono_left (Entails.sepExists_right pad (Entails.pure_right hswar (Entails.refl _)))

theorem cStrAtRO_pad_entails_cStrAtROPad (p : BitVec 64) (s pad : List (BitVec 8))
    (hswar : StrlenSwarPadBound p s pad) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.cStrAtRO p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ⊢
    cStrAtROPad p s := by
  unfold cStrAtROPad
  refine Entails.sepExists_right pad (Entails.pure_right hswar ?_)
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.cStrAtRO]
  have hlen : (s ++ [0#8]).length = s.length + 1 := by simp
  rw [pointsToBytesRO_append p (s ++ [0#8]) pad, hlen]
  exact Entails.refl _

/-- Ideal `strlenHook` satisfies `strlenSpecROSat hookStack` (`toSat` witness). -/
theorem strlenHook_ro_sat_ok (hookStack : Nat) : HookOk strlenHook (strlenSpecROSat hookStack) := by
  intro ⟨p, s⟩ R s0 hrun hpre hsp
  dsimp only [strlenSpecROSat, withVmPreserved, withStrlenPadRO] at hpre
  rw [sepConj_assoc] at hpre
  have hpre' : s0.mem ⊨ (strlenSpecRO hookStack).pre (p, s) s0 ∗ R :=
    Satisfies.of_sep_right hpre
  obtain ⟨hkf, hsym, hout⟩ := strlenHook_ro_ok hookStack (p, s) R s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [strlenSpecROSat, withVmPreserved, withStrlenPadRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨strlenHook_vmPreserved s0, hpost⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Exact-to-`HookSat` bridge (`toSat`): `H "strlen" = some strlenHook` implies
`HookSat H "strlen" (strlenSpecROSat hookStack)`. -/
theorem hookSat_strlenHook_ro_sat {H : LibsignalHooks} {hookStack : Nat}
    (hext : H "strlen" = some strlenHook) :
    HookSat H "strlen" (strlenSpecROSat hookStack) :=
  ⟨strlenHook, hext, strlenHook_ro_sat_ok hookStack⟩

theorem hookSat_strlenHook_ro_sat_cliExterns
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (hookStack : Nat) :
    HookSat (cliExternsPlaced mmpl W) "strlen" (strlenSpecROSat hookStack) :=
  hookSat_strlenHook_ro_sat (cliExternsPlaced_strlen mmpl W)

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain h)

/-- Block `617` `subroutine_ok` discharge from `HookSat H "strlen" (strlenSpecROSat hookStack)`
alone (no `H "strlen" = some strlenHook` equality needed). -/
theorem strlen_ro_sat_placed_ok_of_sat [LibsignalPlacement]
    {H : LibsignalHooks} {hookStack : Nat}
    (hsat : HookSat H "strlen" (strlenSpecROSat hookStack)) :
    subroutine_ok (lsProg_617 H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)) :=
  subroutine_ok_rocl_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat (by decide))

/-- `toSat` corollary: `H "strlen" = some strlenHook` discharges Block `617`
`strlenSpecROSat hookStack` via `hookSat_strlenHook_ro_sat`. -/
theorem strlen_ro_sat_placed_ok_of_hooks [LibsignalPlacement]
    {H : LibsignalHooks} {hookStack : Nat}
    (hext : H "strlen" = some strlenHook) :
    subroutine_ok (lsProg_617 H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)) :=
  strlen_ro_sat_placed_ok_of_sat (hookSat_strlenHook_ro_sat hext)

theorem strlen_ro_sat_placed_ok_cliExterns [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (hookStack : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpecROSat hookStack)) :=
  strlen_ro_sat_placed_ok_of_hooks (cliExternsPlaced_strlen mmpl W)

/-- Real `musl` / `rustc 1.98.1` `libc.a` AArch64 `strlen` words (`muslStrlenWords`, 22 words = 88
bytes) satisfy `strlenSpecROSat hookStack` on any hook-free program (re-exported from
`HookDischarge.Libc.Strlen.strlen_strlenSpecRO_padRO_withVmPreserved_ok`). -/
theorem muslStrlen_strlenSpecROSat_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat)
    (hc : prog.hasWords entry muslStrlenWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (strlenSpecROSat hookStack) :=
  strlen_strlenSpecRO_padRO_withVmPreserved_ok hookStack hc h_no_ext haddr

end LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
