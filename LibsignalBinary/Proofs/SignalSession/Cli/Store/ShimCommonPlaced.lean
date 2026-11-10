/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.Common.InImageKit
public import ProofLib.SepLogic.WP.Apply
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.InImageKit
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Shared `[LibsignalPlacement]` Infrastructure for CLI Store Proofs

Mangled CLI panic-symbol contracts (`CliPanicHooksPlaced`), stack-bound extraction from
`LibsignalRoLoaded`, cross-block `StoreKit.withLsCodeRoLoaded` transfers, and the `wp_call_lscro`
call tactic.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PlacedCommon

open Arm64 Arm64.Obj ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. Mangled CLI Panic Hooks -/

/-- All 18 mangled panic symbols in `cliPanicSymbolsPlaced` map to `some Rust.panicked`. -/
def CliPanicHooksPlaced (H : LibsignalHooks) : Prop :=
  ∀ sym ∈ cliPanicSymbolsPlaced, H sym = some Rust.panicked

theorem cliPanicHooksPlaced_cli (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    CliPanicHooksPlaced (cliExternsPlaced mmpl W) := by
  intro sym hmem
  simp [cliExternsPlaced, isCliPanicSymbolPlaced, hmem]

theorem ls_panicAt_of_cliPanic [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {sym : String}
    (hpan : CliPanicHooksPlaced H)
    (hcli : sym ∈ cliPanicSymbolsPlaced := by decide)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = some Rust.panicked :=
  (ls_externAt?_of_mem hmem hi hunmut).trans (hpan sym hcli)

/-! ## 2. Stack Bound from `LibsignalRoLoaded` -/

theorem stk_le_pow64_of_roLoaded {pl : MultiPlacement} {m : Memory}
    {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hro : LibsignalRoLoaded pl m)
    (hm : m ⊨ stackAt sp stk ∗ R) : stk ≤ 2 ^ 64 := by
  by_cases hle : stk ≤ 2 ^ 64
  · exact hle
  · have hro_region : m.RO (pl.ρ sessLoadFutVtSym) 8 :=
      lsro_perm hro (by decide +kernel)
    have hperm_ro : m.perm (pl.ρ sessLoadFutVtSym) = some Perm.ro :=
      (hro_region (pl.ρ sessLoadFutVtSym) (by unfold InRegion; simp)).1
    have ha : InRegion (sp - BitVec.ofNat 64 stk) stk (pl.ρ sessLoadFutVtSym) := by
      unfold InRegion
      have := BitVec.isLt (pl.ρ sessLoadFutVtSym - (sp - BitVec.ofNat 64 stk))
      omega
    have hrw : m.perm (pl.ρ sessLoadFutVtSym) = some Perm.rw :=
      (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk).perm_rw hm ha
    rw [hperm_ro] at hrw
    exact absurd hrw (by decide)

theorem lift_stk_lscro {α : Type} {prog : Program} {entry : BitVec 64} {pl : MultiPlacement}
    {F : Nat → Spec α} {P : α → State → SepProp} {Q : α → State → State → SepProp}
    {stk0 stk : Nat}
    (hInner : subroutine_ok prog entry (F stk0))
    (hstk : stk0 ≤ stk)
    (hpre_eq : ∀ x s k, (F k).pre x s =
      ⌜StoreKit.LibsignalCodeRoLoaded pl s.mem⌝ ∗ P x s ∗ stackAt s.sp k)
    (hpost_eq : ∀ x s0 sf k, (F k).post x s0 sf = Q x s0 sf ∗ stackAt s0.sp k)
    (hpan_eq0 : (F stk0).onPanic =
      fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by rfl)
    (hpan_eq : (F stk).onPanic = (F stk0).onPanic := by rfl)
    (hexit_eq : (F stk0).onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom_eq : (F stk0).onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (F stk) := by
  intro x R s0 hpc hrun hpre halign hL
  have hpre0 := hpre
  rw [hpre_eq x s0 stk] at hpre0
  have hcrl : StoreKit.LibsignalCodeRoLoaded pl s0.mem := by
    have h1 : s0.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded pl s0.mem⌝ ∗
        (P x s0 ∗ stackAt s0.sp stk ∗ R) := by
      convert hpre0 using 1; ac_rfl
    rw [satisfies_pure_sepConj] at h1
    exact h1.1
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜StoreKit.LibsignalCodeRoLoaded pl s0.mem⌝ ∗ P x s0 ∗ R) := by
      convert hpre0 using 1; ac_rfl
    exact stk_le_pow64_of_roLoaded hcrl.2 hm_stk
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0) ∗ stackAt s0.sp stk0 := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp stk0 (stk - stk0) (by omega)
    rwa [Nat.add_sub_of_le hstk] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0) ∗ R
  have hpre' : s0.mem ⊨ (F stk0).pre x s0 ∗ R' := by
    rw [hpre_eq x s0 stk0]
    rw [hsplit] at hpre0
    dsimp only [R']
    convert hpre0 using 1; ac_rfl
  obtain ⟨sf, hs, ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩⟩ :=
    hInner x R' s0 hpc hrun hpre' halign hL
  · refine ⟨sf, hs, Or.inl ⟨hret, hcc, ?_⟩⟩
    rw [hpost_eq x s0 sf stk0] at hpost
    rw [hpost_eq x s0 sf stk, hsplit]
    dsimp only [R'] at hpost
    convert hpost using 1; ac_rfl
  · refine ⟨sf, hs, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    rw [hpan_eq, hpan_eq0]
    rw [hpan_eq0] at hpost
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · rw [hexit_eq] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · rw [hoom_eq] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 3. Cross-Block Transfer for `StoreKit.withLsCodeRoLoaded` & `AllocContractsXCliPlaced` -/

theorem ls_transfer_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (StoreKit.withLsCodeRoLoaded lsmpl spec) := by
  have h0 := StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := callerProg) hcallee hi hj hj_unmut
  exact subroutine_ok_mono h0 (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [StoreKit.withLsRoCl] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

theorem ls_transfer_cl_to_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  ls_transfer_lscro (callerProg := callerProg)
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee) hi hj hj_unmut

theorem ls_transfer_plain_to_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  ls_transfer_lscro (callerProg := callerProg)
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hcallee) hi hj hj_unmut

theorem alloc_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.alloc hi

theorem dealloc_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.dealloc hi

theorem realloc_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustReallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack A extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.realloc hi

theorem shim_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.shim stk h1 h2) hi

theorem memcpy_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (libcMemcpySpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memcpy stk h1 h2) hi

theorem session_memcpy_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpySpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memcpy stk h1 h2) hi

theorem memcpy_region_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack memcpyRegionSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memcpy_region stk h1 h2) hi

theorem memmove_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memmoveName)
      (StoreKit.withLsCodeRoLoaded lsmpl (libcMemmoveSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memmove stk h1 h2) hi

theorem session_memmove_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memmoveName)
      (StoreKit.withLsCodeRoLoaded lsmpl (sessionMemmoveSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memmove stk h1 h2) hi

theorem memset_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (StoreKit.withLsCodeRoLoaded lsmpl (libcMemsetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memset stk h1 h2) hi

theorem session_memset_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (StoreKit.withLsCodeRoLoaded lsmpl (sessionMemsetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memset stk h1 h2) hi

theorem memset_region_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack memsetRegionSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memset_region stk h1 h2) hi

theorem session_memset_region_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memset_region stk h1 h2) hi

/-! ## 4. `wp_call_lscro`: `InImageKit` Counterpart for `StoreKit.withLsCodeRoLoaded` -/

theorem lscro_of_mem_eq {pl : MultiPlacement} {s s' : State}
    (h : StoreKit.LibsignalCodeRoLoaded pl s.mem) (hmem : s'.mem = s.mem) :
    StoreKit.LibsignalCodeRoLoaded pl s'.mem :=
  hmem ▸ h

theorem satisfies_lscro_pre {α : Type} {spec : Spec α} {pl : MultiPlacement}
    {x : α} {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem) (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (StoreKit.withLsCodeRoLoaded pl spec).pre x s ∗ R := by
  dsimp only [StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcrl, hpre⟩

theorem SepWP.call_plain_lscro {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec) (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  sepWP_seq_lscro (mid := ret_pc) hcrl
    (ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp hlr hpre h_no_panic h_no_exit
      (fun sf hpcf hrunf hspf hcsf =>
        ProofLib.SepWP.done hpcf hrunf (hnext sf hpcf hrunf hspf hcsf))
      (fun R' sf ho h => (not_satisfies_false_sepConj (h_no_oom (F ∗ R') sf ho h)).elim))

theorem SepWP.call_lscro {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  SepWP.call_plain_lscro (spec := StoreKit.withLsCodeRoLoaded pl spec) (x := x) hcall hcrl hpc hrun hsp hlr
    (fun R hm => satisfies_lscro_pre hcrl (hpre R hm)) h_no_panic h_no_exit hnext h_no_oom

theorem SepWPp.call_plain_lscro {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec) (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ |
    ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (not_satisfies_false_sepConj (h_no_oom _ sm hoom hpost)).elim

theorem SepWPp.call_lscro {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_plain_lscro (spec := StoreKit.withLsCodeRoLoaded pl spec) (x := x) hcall hcrl hpc hrun hsp hlr
    (fun R hm => satisfies_lscro_pre hcrl (hpre R hm)) hexit hpanic hnext h_no_oom

open Lean Elab Tactic Meta in
meta def lsCroKitMentionsInv (e : Expr) : Bool :=
  (e.find? fun t => t.isConst &&
    ["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded",
     "LsFrozenInv"].contains (inImageKitLastStr t.constName!)).isSome

open Lean Elab Tactic Meta in
meta partial def lsCroKitFindPl? (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.getAppNumArgs == 2 && ty.getAppFn.isConst &&
      ["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded",
       "LsFrozenInv"].contains (inImageKitLastStr ty.getAppFn.constName!) then
    some (ty.getArg! 0)
  else if ty.isAppOfArity ``And 2 then
    (lsCroKitFindPl? (ty.getArg! 0)).orElse fun _ => lsCroKitFindPl? (ty.getArg! 1)
  else none

open Lean Elab Tactic Meta in
meta def lsCroKitClearInvHyps : TacticM Unit := do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc : Array FVarId := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOf ``Arm64.subroutine_ok then continue
      if lsCroKitMentionsInv ty then acc := acc.push decl.fvarId
    return acc
  let g' ← g.tryClearMany fvs
  replaceMainGoal [g']

open Lean Elab Tactic Meta in
meta def lsCroKitCall (tacName : String) (hcall hinv : Term) (arg? : Option Term) :
    TacticM Unit := do
  let g0 ← getMainGoal
  let gty ← g0.withContext do instantiateMVars (← g0.getType)
  let gty := gty.consumeMData
  let isWPp ← if gty.isAppOfArity ``SepWPp 7 then pure true
    else if gty.isAppOfArity ``SepWP 6 then pure false
    else throwError "{tacName}: goal is not `SepWP …` / `SepWPp …`"
  let sGoal := gty.getArg! 2
  let (hasWrap, plE) ← g0.withContext <| withoutModifyingState do
    let e ← Tactic.elabTerm hcall none
    let ty ← whnfR (← instantiateMVars (← inferType e))
    if !ty.isAppOfArity ``Arm64.subroutine_ok 4 then
      throwError "{tacName}: `{hcall}` is not a `subroutine_ok` hypothesis:{indentExpr ty}"
    let mut specE := (ty.getArg! 3).consumeMData
    for _ in [:8] do
      if specE.getAppFn.isConst then
        let fnStr := inImageKitLastStr specE.getAppFn.constName!
        if fnStr == "withLsCodeRoLoaded" || fnStr == "mk" then break
        match ← unfoldDefinition? specE with
        | some specE' => specE := specE'.consumeMData
        | none => break
      else break
    if specE.getAppNumArgs == 3 && specE.getAppFn.isConst &&
        inImageKitLastStr specE.getAppFn.constName! == "withLsCodeRoLoaded" then
      return (true, ← instantiateMVars (specE.getArg! 1))
    if specE.isAppOfArity ``Arm64.Spec.mk 6 then
      if let some pl := lsCroKitFindPl? (specE.getArg! 1) then
        return (true, ← instantiateMVars pl)
    let hty ← instantiateMVars (← inferType (← Tactic.elabTerm hinv none))
    let some pl := lsCroKitFindPl? hty
      | throwError "{tacName}: cannot read `MultiPlacement` off `{hinv} : {hty}`"
    return (false, ← instantiateMVars pl)
  let hinvId ← freshIdent `hcrl_call
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hinvSfId ← freshIdent `hcrl_sf
  let sStx ← g0.withContext (Term.exprToSyntax sGoal)
  let plStx ← g0.withContext (Term.exprToSyntax plE)
  let haveStx ← `(tactic|
    have $hinvId:ident :
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded $plStx ($sStx).mem := by
      first
        | with_reducible exact $hinv
        | exact ⟨($hinv).1, ($hinv).2⟩
        | exact lscro_of_mem_eq $hinv (by simp only [arm64_norm, wp_norm]; done)
        | exact lscro_of_mem_eq ⟨($hinv).1, ($hinv).2⟩ (by simp only [arm64_norm, wp_norm]; done))
  if !(← tryTacticCatchRuntimeBool (evalTactic haveStx)) then
    throwError "{tacName}: could not establish `LibsignalCodeRoLoaded pl s.mem` at call state from `{hinv}`"
  let lemmaName : Name := match isWPp, hasWrap with
    | false, true => ``SepWP.call_lscro
    | false, false => ``SepWP.call_plain_lscro
    | true, true => ``SepWPp.call_lscro
    | true, false => ``SepWPp.call_plain_lscro
  let lem := mkCIdent lemmaName
  let applyStx ← match arg? with
    | some a => `(tactic| apply ($lem $hcall $hinvId (x := $a)))
    | none => `(tactic| apply ($lem $hcall $hinvId))
  evalTactic applyStx
  inImageKitCloseSetup tacName
  let gs ← getGoals
  let gPre :: gA :: gB :: gCont :: rest := gs
    | throwError "{tacName}: unexpected subgoals after call-site setup"
  setGoals [gPre]
  lsCroKitClearInvHyps
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  inImageKitDestructureSat
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  let preLeft ← getGoals
  let mut side : List MVarId := []
  if isWPp then
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let gB' ← getMainGoal
    gB'.setTag `panic
    side := side ++ [gB']
  else
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
  setGoals [gCont]
  inImageKitClearByName hinvId.getId
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hinvSfId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  if isWPp then inImageKitElimSpatialWPp hspId else wpElimSpatialContext hspId
  let contGoals ← getGoals
  let mut restOpen : List MVarId := []
  for m in rest do
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    if ty.consumeMData.isAppOfArity ``autoParam 2 then
      let m' ← m.replaceTargetDefEq (ty.consumeMData.getArg! 0)
      let saved ← saveState
      setGoals [m']
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_close_oom_default))) then
        if (← getGoals).isEmpty then continue
      saved.restore
      restOpen := restOpen ++ [m']
    else
      restOpen := restOpen ++ [m]
  let preOpen ← preLeft.filterM fun m => not <$> m.isAssigned
  let sideOpen ← side.filterM fun m => not <$> m.isAssigned
  setGoals (contGoals ++ preOpen ++ sideOpen ++ restOpen)

syntax (name := wpCallLsCro) "wp_call_lscro" ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_call_lscro $hcall $hinv) => lsCroKitCall "wp_call_lscro" hcall hinv none
  | `(tactic| wp_call_lscro $hcall $hinv $arg) =>
    lsCroKitCall "wp_call_lscro" hcall hinv (some arg)

end CryptoVerification.SignalSession.Cli.Store.PlacedCommon
