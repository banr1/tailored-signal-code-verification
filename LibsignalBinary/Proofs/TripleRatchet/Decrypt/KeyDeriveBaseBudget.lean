/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `KeyDerive` & `spqr::recv` Helpers for `try_decrypt_with_state`

Provides `VmPreserved`-carrying relocatable `SepWP` / `reaches_pc` / `Steps` combinators, budget
callee bridges (`format_inner`, `__rust_dealloc`, `<ProtocolAddress as Display>::fmt`), and the
budget-threaded `spqrRecvSpecPlaced` contract and `onPanic` bridges over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement libsignalMutatedBlocks
  lsFmtWriteSym lsRustDeallocSym lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TryDecryptGhost VecArg
  keys_ls_hook_ok_of_mem logOff spqrRecvResultAt spqrRecvStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  tryDecryptMidMetaPlaced tryDecryptPlacedImg
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  tryDecryptMidMetaCore tryDecryptMidMetaPlaced_of_core
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
  formatInnerBudgetEnvSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptOnPanic tryDecryptFnOnPanic
  tryDecryptRawSpecPlaced tryDecryptFnRawSpecPlaced
  tryDecryptSpecPlaced tryDecryptFnSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget (
  tryDecrypt_onPanic_of_false_placed tryDecryptFn_onPanic_of_false_placed
  tryDecryptFnOnPanic_eq_auth tryDecryptFnSpecPlaced_onPanic_eq_auth
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  steps_call_out_placed steps_call_out_placed_cro
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  addrDisplayEnvSpec addrDisplaySpec
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget (
  addr_display_placed_ok_at
)

/-! ## 1. `VmPreserved`-Carrying Relocatable `SepWP` / `reaches_pc` / `Steps` Combinators -/

/-- State-indexed `VmPreserved` variant of `KeyDerive.reaches_pc_of_sepWP_placed`, allowing
`P_mid : State → SepProp` to carry `A.pool lim st sm` transported via `VmPreserved s sm`. -/
theorem reaches_pc_of_sepWP_placed_vm [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R))))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (P_mid sm) (fun sf P_f =>
        VmPreserved sm sf ∧ (VmPreserved sm sf → (sf.mem ⊨ P_f ∗ R) → Q sf))) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hvm hmm
    rcases (h2 sm hpc hrun hvm (hcl.of_keepsFrozen hsteps.keepsFrozen) hReg).elim
        hmm' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hvmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hvmf hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `withLsCodeRoLoaded` variant of `reaches_pc_of_sepWP_placed_vm`. -/
theorem reaches_pc_of_sepWP_placed_cro_vm [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R))))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      RegMid sm → SepWP prog target sm (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid sm)
        (fun sf P_f => VmPreserved sm sf ∧ (VmPreserved sm sf → (sf.mem ⊨ P_f ∗ R) → Q sf))) :
    reaches_pc prog target s Q := by
  intro hL
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hvm hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hmm'' : sm.mem ⊨ (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ P_mid sm) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hclm, hmm'⟩
    rcases (h2 sm hpc hrun hvm hclm hReg).elim hmm'' (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, P_f, hmf, hvmf, hq⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, hq hvmf hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- State-indexed `VmPreserved` variant of `KeyDerive.steps_of_sepWP_placed`. -/
theorem steps_of_sepWP_placed_vm [LibsignalPlacement] {prog : Program}
    {mid : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (VmPreserved s sm → (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R))))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid sm ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hvm hmm
    obtain ⟨s', hsteps', hout⟩ :=
      h2 sm hpc hrun hvm (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.codeLoaded hL) hReg hmm'
    exact ⟨s', hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `VmPreserved` variant of `KeyDerive.steps_done_of_sepWP_placed`. -/
theorem steps_done_of_sepWP_placed_vm [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s : State} {P R : SepProp}
    {QCore NormalOut PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (himp : ∀ sf, VmPreserved s sf → LibsignalCodeRoLoaded lsmpl sf.mem → QCore sf → NormalOut sf)
    (hwp : SepWP prog target s P (fun sf P_f =>
      VmPreserved s sf ∧ (VmPreserved s sf → (sf.mem ⊨ P_f ∗ R) → QCore sf))) :
    ∃ s', Steps prog s s' ∧ (NormalOut s' ∨ PanicOut s') := by
  rcases hwp.elim hmem hL with ⟨sf, hsteps, ⟨_, _, P_f, hmf, hvmf, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl (himp sf hvmf (hcl.of_keepsFrozen hsteps.keepsFrozen) (hq hvmf hmf))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `VmPreserved` variant of `KeyDerive.steps_done_of_sepWP_midMeta_placed`. -/
theorem steps_done_of_sepWP_midMeta_placed_vm [LibsignalPlacement] {prog : Program}
    {target : BitVec 64} {s0 s : State} {P R : SepProp}
    {Rest PanicOut : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWP prog target s P (fun sf P_f =>
      VmPreserved s sf ∧ (VmPreserved s sf → (sf.mem ⊨ P_f ∗ R) →
        sf.pc = target ∧ tryDecryptMidMetaCore s0 sf ∧ Rest sf))) :
    ∃ s', Steps prog s s' ∧
      ((s'.pc = target ∧ tryDecryptMidMetaPlaced s0 s' ∧ Rest s') ∨ PanicOut s') := by
  refine steps_done_of_sepWP_placed_vm hmem hL hcl ?_ hwp
  intro sf _hvmf hclf ⟨hpc', hcore, hrest⟩
  exact ⟨hpc', tryDecryptMidMetaPlaced_of_core hclf hcore, hrest⟩

/-- Call continuation combinator on `Steps` for `withLsCodeLoaded lsmpl spec` callees
(complementing `ConsumeMsgKeyBudget.steps_call_out_placed` and `steps_call_out_placed_cro`). -/
theorem steps_call_out_placed_cl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  have hpre' : sm.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl.1, hpre⟩
  exact steps_call_out_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

/-! ## 2. Relocatable Callee `subroutine_ok` Bridges (`KeyDeriveCallees` Budget Counterparts) -/

/-- Mangled symbol name for `alloc::fmt::format::format_inner`. -/
abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

/-- Relocatable `format_inner` (`formatInnerBudgetEnvSpec`) lifted to any caller block `prog`. -/
theorem formatInnerEnv_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim Env))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim Env) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

/-- Relocatable `format_inner` (`formatInnerBudgetSpec`, `Env = FormatInnerEnv`) lifted to `prog`. -/
theorem formatInner_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim) :=
  keys_ls_hook_ok_of_mem h_fmt (by decide) hi hunmut

/-- Relocatable `__rust_dealloc` (`rustCliDeallocBudgetSpec`) lifted to any caller block `prog`. -/
theorem dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  keys_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`, `addrDisplayEnvSpec`) lifted to
any caller block `prog`. -/
theorem addrDisplayEnv_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hW : HookSat H lsFmtWriteSym (fmtWriteBudgetEnvSpec M A lim Env))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 215)
      (withLsCodeLoaded lsmpl (addrDisplayEnvSpec M A lim Env)) :=
  addr_display_placed_ok_at hW hi hunmut

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`, `addrDisplaySpec`,
`Env = FmtWriteEnv`) lifted to any caller block `prog`. -/
theorem addrDisplay_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hW : HookSat H lsFmtWriteSym (fmtWriteBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 215)
      (withLsCodeLoaded lsmpl (addrDisplaySpec M A lim)) :=
  addr_display_placed_ok_at hW hi hunmut

/-! ## 3. Budget-Threaded `spqr::recv` Contract & `onPanic` Bridges -/

/-- Budget-threaded relocatable `spqr::recv` raw contract (`onOom = ⌜False⌝` under `FitsEnv`,
`allocFailedIn` dropped from `onPanic`). -/
def spqrRecvRawSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) where
  pre := fun ((st_arg, msg_arg, ret), st) s =>
    ⌜s.readReg64 .x0 = st_arg.v ∧ s.readReg64 .x1 = msg_arg.v ∧ s.readReg64 .x8 = ret ∧
      FitsEnv M lim st (spqrRecvEnv st_arg.bytes msg_arg.bytes)⌝ ∗
      st_arg.at A.repAlloc ∗ msg_arg.at A.repAlloc ∗ memRegion ret 48 ∗
      logOff tryDecryptPlacedImg ∗ A.pool lim st s ∗ stackAt s.sp spqrRecvStack
  post := fun ((st_arg, msg_arg, ret), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st_arg.bytes msg_arg.bytes ∧
        spqrRecvEnv st_arg.bytes msg_arg.bytes evs⌝ ∗
      st_arg.at A.repAlloc ∗ msg_arg.at A.repAlloc ∗
      spqrRecvResultAt A.repAlloc ret (S.recv st_arg.bytes msg_arg.bytes) ∗
      logOff tryDecryptPlacedImg ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp spqrRecvStack
  onPanic := fun ((st_arg, msg_arg, _), _) s0 sf =>
    ⌜S.recvPanics st_arg.bytes msg_arg.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `withLsCodeRoLoaded`-wrapped budget `spqr::recv` contract. -/
def spqrRecvSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlaced A lim S spqrRecvEnv)

/-- Bridge a budget `spqr::recv` panic into `(tryDecryptSpecPlaced ...).onPanic`. -/
theorem onPanic_of_spqrRecv_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨
      ((spqrRecvRawSpecPlaced A lim S spqrRecvEnv).onPanic ((st, msg, ret), st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced,
    tryDecryptOnPanic, spqrRecvRawSpecPlaced] at h ⊢
  rw [hst, hmsg] at h
  exact allowPanic_frame (fun ⟨hp, hmf⟩ => ⟨Or.inr hp, h0m.trans hmf⟩) h

/-- Convenience overload of `onPanic_of_spqrRecv_placed` for `sm.trace = s0.trace` and
`uuidTryParse`. -/
theorem onPanic_of_spqrRecv_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨
      ((spqrRecvRawSpecPlaced A lim S spqrRecvEnv).onPanic ((st, msg, ret), st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).onPanic (x, st_init) s0 sf ∗ R :=
  onPanic_of_spqrRecv_placed (htrace ▸ List.prefix_refl s0.trace) hst hmsg h

/-- Bridge a budget `spqr::recv` panic into `(tryDecryptFnSpecPlaced ...).onPanic`. -/
theorem onPanic_of_spqrRecv_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨
      ((spqrRecvRawSpecPlaced A lim S spqrRecvEnv).onPanic ((st, msg, ret), st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced,
    tryDecryptFnOnPanic, spqrRecvRawSpecPlaced] at h ⊢
  rw [hst, hmsg] at h
  exact allowPanic_frame (fun ⟨hp, hmf⟩ => ⟨Or.inr hp, h0m.trans hmf⟩) h

/-- Convenience overload of `onPanic_of_spqrRecv_fn_placed` for `sm.trace = s0.trace` and
`uuidTryParse`. -/
theorem onPanic_of_spqrRecv_fn_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {spqrRecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨
      ((spqrRecvRawSpecPlaced A lim S spqrRecvEnv).onPanic ((st, msg, ret), st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).onPanic
        (x, st_init) s0 sf ∗ R :=
  onPanic_of_spqrRecv_fn_placed (htrace ▸ List.prefix_refl s0.trace) hst hmsg h

/-- Discharge a budget `format_inner` panic obligation (`onPanic = ⌜False⌝`) into
`(tryDecryptSpecPlaced ...).onPanic`. -/
theorem onPanic_of_formatInner_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (h : sf.mem ⊨ ((formatInnerBudgetEnvSpec M A lim Env).onPanic (ret, st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R :=
  tryDecrypt_onPanic_of_false_placed C A lim ctl parse S tdEnv x st_init s0 sf F R h

/-- Discharge a budget `format_inner` panic obligation (`onPanic = ⌜False⌝`) into
`(tryDecryptFnSpecPlaced ...).onPanic`. -/
theorem onPanic_of_formatInner_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init st_m : M.σ} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (h : sf.mem ⊨ ((formatInnerBudgetEnvSpec M A lim Env).onPanic (ret, st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R :=
  tryDecryptFn_onPanic_of_false_placed C decFn A lim ctl parse S tdEnv x st_init s0 sf F R h

/-- `tryDecryptFnOnPanic` equals `tryDecryptOnPanic` because `decFn` only produces
`.invalidMessage _ .badCiphertext` (never `.panic`). -/
theorem tryDecryptFnOnPanic_eq (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (parse : UuidParser) (S : SpqrModel) :
    tryDecryptFnOnPanic C decFn parse S = tryDecryptOnPanic C parse S :=
  tryDecryptFnOnPanic_eq_auth C decFn parse S

/-- `(tryDecryptFnSpecPlaced ...).onPanic` equals `(tryDecryptSpecPlaced ...).onPanic`. -/
theorem tryDecryptFnSpecPlaced_onPanic_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic =
      (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic :=
  tryDecryptFnSpecPlaced_onPanic_eq_auth C decFn A lim ctl parse S tdEnv

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget
