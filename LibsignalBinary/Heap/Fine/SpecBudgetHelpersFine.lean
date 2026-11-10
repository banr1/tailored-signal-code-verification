/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Budget-Threaded Hook and `VmPreserved` Helpers

Cost-model-polymorphic `VmPreserved` invariants and `HookOk` / `HookSat` witnesses for the
non-allocating, formatting, time, ML-KEM-768, PQXDH, libc, and CLI I/O hooks in
`LibsignalBinary.Heap.SpecBudget`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi (
  durationSinceSpec durationSinceHookName timeAddHookName timeAddSpec
)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem
  mlkemDecapsName mlkemDecapsSpec mlkemEncaps1Name mlkemEncaps1Spec
  mlkemEncaps2Name mlkemEncaps2Spec mlkemFromSeedName mlkemFromSeedSpec
  mlkemPk1Name mlkemPk1Spec mlkemPk2Name mlkemPk2Spec
  mlkemValidatePkName mlkemValidatePkSpec
)
open CryptoVerification.SignalSession (
  CliHooks
  cliBcmpHook durationSinceExactHook fromUtf8Hook memrchrHook
  strlenHook unitResult unmodelled writeFileHook writeStdoutHook
)
open CryptoVerification.SignalSession.CliExt (
  bcmpSpec blackBoxSpec compress256Spec compress512Spec dhSpec dsmbSpec
  fromUtf8Spec kemDecapsSpec kemEncapsSpec memHookStack memcpyROSpec memcpySpec
  memmoveSpec memrchrSpec memsetSpec pubFromSecretSpec pureByteFunctionSpec
  shimSpec strlenSpec toEdwardsSpec torsionFreeSpec writeFileSpec writeStdoutSpec
  zeroizeSpec
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FdsHiFrame RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv
  durationSinceBudgetSpec durationSinceEpochBudgetSpec
  fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
  formatInnerBudgetEnvSpec formatInnerBudgetSpec
  timeAddBudgetSpec withVmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  cc_retHook_setMem_sameRegs vmPreserved_retHook_setMem
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers (
  write_empty_vecU8
)

/-! ## `withVmPreserved` and `HookSat` Combinators -/

/-- Strengthen any `HookOk f spec` witness to `HookOk f (withVmPreserved spec)` once `f` preserves
    `VmPreserved`. -/
theorem hookOk_withVmPreserved {α : Type} {f : State → State} {spec : Spec α}
    (hok : HookOk f spec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withVmPreserved spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm s0, hpost⟩
  · exact Or.inr hrest

/-- Package a `HookOk` witness at a lookup equation `hooks name = some f` into `HookSat`. -/
theorem hookSat_of_hookOk {α : Type} {hooks : String → Option (State → State)}
    {name : String} {f : State → State} {spec : Spec α}
    (hf : hooks name = some f) (hok : HookOk f spec) :
    HookSat hooks name spec :=
  ⟨f, hf, hok⟩

/-! ## Atomic `VmPreserved` Lemmas and `vm_close` Tactic -/

/-- Assemble `VmPreserved s s'` from the preserved `State` / permission / `FdsHiFrame` projections. -/
theorem VmPreserved.of_eq {s s' : State}
    (hbrkS : s'.brkStart = s.brkStart)
    (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0)
    (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : s'.mem.perm = s.mem.perm)
    (hfds : FdsHiFrame s s' := by intro _ _ _; rfl) :
    VmPreserved s s' :=
  ⟨⟨hbrkS, hbrk, htp⟩, hphys, fun a => congrFun hperm a, hfds⟩

private theorem brkStart_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brkStart = s.brkStart := by
  cases s; cases r <;> rfl

private theorem brk_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brk = s.brk := by
  cases s; cases r <;> rfl

private theorem tpidrEl0_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by
  cases s; cases r <;> rfl

private theorem physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by
  cases s; cases r <;> rfl

private theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by
  cases s; cases r <;> rfl

private theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by
  cases s; cases r <;> rfl

private theorem fds_setFile (fs : FsState) (p : String) (e : Option FsEntry) :
    (fs.setFile p e).fds = fs.fds := rfl

local macro "vm_field" : tactic => `(tactic| first
  | rfl
  | simp only [retHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister,
      Arm64.State.setMem, Arm64.State.setPC, Arm64.State.appendTrace, Arm64.State.setFs,
      Arm64.State.setStatus, Rust.panicked,
      brkStart_writeReg64, brk_writeReg64, tpidrEl0_writeReg64, physMemAvail_writeReg64])

local macro "vm_perm" : tactic => `(tactic| first
  | rfl
  | (simp only [retHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister,
      Arm64.State.setMem, Arm64.State.setPC, Arm64.State.appendTrace, Arm64.State.setFs,
      Arm64.State.setStatus, Rust.panicked, mem_writeReg64,
      CryptoVerification.E2E.writeVecHeader,
      Arm64.Memory.perm_writeBytes, Arm64.Memory.perm_write64, Arm64.Memory.perm_write32,
      Arm64.Memory.perm_write16, Arm64.Memory.perm_write8]
     try (split <;> simp only [Arm64.Memory.perm_writeBytes])))

local macro "vm_fds" : tactic => `(tactic| (
  intro _ _ _
  first
  | rfl
  | simp only [retHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister,
      Arm64.State.setMem, Arm64.State.setPC, Arm64.State.appendTrace, Arm64.State.setFs,
      Arm64.State.setStatus, Rust.panicked, fs_writeReg64, fds_setFile]))

local macro "vm_close" : tactic => `(tactic| (
  try dsimp only
  repeat' split
  all_goals
    refine VmPreserved.of_eq (by vm_field) (by vm_field) (by vm_field) (by vm_field)
      (by vm_perm) (by vm_fds)))

/-- Lift pointwise `VmPreserved` over every entry of a hook association list `L` to `L.lookup`. -/
theorem vmPreserved_of_lookup {L : List (String × (State → State))}
    {P : String → Prop}
    (hL : ∀ p ∈ L, P p.1 → ∀ s : State, VmPreserved s (p.2 s))
    {n : String} {f : State → State}
    (hlook : L.lookup n = some f) (hn : P n) (s : State) :
    VmPreserved s (f s) :=
  hL (n, f) (CryptoVerification.SignalSession.ExternsWitness.mem_of_lookup hlook) hn s

/-! ## `VmPreserved` for Non-Allocating Hooks -/

theorem panicked_vmPreserved (s : State) : VmPreserved s (Rust.panicked s) := by
  vm_close

theorem hookNoop_vmPreserved (s : State) : VmPreserved s (hookNoop s) := by
  unfold hookNoop; vm_close

theorem hookMemset_vmPreserved (s : State) : VmPreserved s (hookMemset s) := by
  unfold hookMemset; vm_close

theorem hookMemcpy_vmPreserved (s : State) : VmPreserved s (hookMemcpy s) := by
  unfold hookMemcpy; vm_close

theorem hookMemmove_vmPreserved (s : State) : VmPreserved s (hookMemmove s) :=
  hookMemcpy_vmPreserved s

theorem cliBcmpHook_vmPreserved (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64)
    (s : State) : VmPreserved s (cliBcmpHook bcmp s) := by
  unfold cliBcmpHook; vm_close

theorem strlenHook_vmPreserved (s : State) : VmPreserved s (strlenHook s) := by
  unfold strlenHook unmodelled; vm_close

theorem writeFileHook_vmPreserved (s : State) : VmPreserved s (writeFileHook s) := by
  unfold writeFileHook unitResult unmodelled; vm_close

theorem writeStdoutHook_vmPreserved (s : State) : VmPreserved s (writeStdoutHook s) := by
  unfold writeStdoutHook unitResult unmodelled; vm_close

theorem memrchrHook_vmPreserved (s : State) : VmPreserved s (memrchrHook s) := by
  unfold memrchrHook unmodelled; vm_close

theorem fromUtf8Hook_vmPreserved (utf8Err : List (BitVec 8) → BitVec 64 × BitVec 16)
    (s : State) : VmPreserved s (fromUtf8Hook utf8Err s) := by
  unfold fromUtf8Hook unmodelled; vm_close

theorem fmtWriteHook0_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.E2E.fmtWriteHook0 s) := by
  unfold CryptoVerification.E2E.fmtWriteHook0; vm_close

theorem formatInnerHook0_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.E2E.formatInnerHook0 s) := by
  unfold CryptoVerification.E2E.formatInnerHook0; vm_close

theorem durationSinceExactHook_vmPreserved (s : State) :
    VmPreserved s (durationSinceExactHook s) := by
  unfold durationSinceExactHook unmodelled; vm_close

theorem timeAddHook_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.E2E.timeAddHook s) := by
  unfold CryptoVerification.E2E.timeAddHook; vm_close

theorem blackBoxHook_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.LibsignalSession.blackBoxHook s) := by
  unfold CryptoVerification.LibsignalSession.blackBoxHook; vm_close

theorem compress256Hook_vmPreserved (C : Crypto) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalHmac.compress256Hook C.F s) := by
  unfold CryptoVerification.LibsignalHmac.compress256Hook; vm_close

theorem pubFromSecretHook_vmPreserved (C : Crypto) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook C.pubKey s) := by
  unfold CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook; vm_close

theorem diffieHellmanHook_vmPreserved (C : Crypto) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook C.X s) := by
  unfold CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook; vm_close

theorem zeroizeSecretHook_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook s) := by
  unfold CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook; vm_close

theorem compress512Hook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.compress512Hook Q.F512 s) := by
  unfold CryptoVerification.E2E.compress512Hook; vm_close

theorem toEdwardsHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.toEdwardsHook Q.montToEd s) := by
  unfold CryptoVerification.E2E.toEdwardsHook; vm_close

theorem compressHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.compressHook Q.compress s) := by
  unfold CryptoVerification.E2E.compressHook; vm_close

theorem edNegHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.edNegHook Q.edNeg s) := by
  unfold CryptoVerification.E2E.edNegHook; vm_close

theorem torsionFreeHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.torsionFreeHook Q.isTorsionFree s) := by
  unfold CryptoVerification.E2E.torsionFreeHook; vm_close

theorem dsmbHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.dsmbHook Q.dsmb s) := by
  unfold CryptoVerification.E2E.dsmbHook; vm_close

theorem scalarModHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.scalarModHook Q.scalarMod s) := by
  unfold CryptoVerification.E2E.scalarModHook; vm_close

theorem scalarWideHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.scalarWideHook Q.scalarWide s) := by
  unfold CryptoVerification.E2E.scalarWideHook; vm_close

theorem kemEncapsHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.kemEncapsHook Q.encaps s) := by
  unfold CryptoVerification.E2E.kemEncapsHook; vm_close

theorem kemDecapsHook_vmPreserved (Q : CryptoVerification.E2E.PqxdhPrims) (s : State) :
    VmPreserved s (CryptoVerification.E2E.kemDecapsHook Q.decaps s) := by
  unfold CryptoVerification.E2E.kemDecapsHook; vm_close

theorem mlkemFromSeedHook_vmPreserved (K : MlKem) (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemFromSeedHook K s) := by
  unfold CryptoVerification.E2E.mlkemFromSeedHook; vm_close

theorem mlkemPk1Hook_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemPk1Hook s) := by
  unfold CryptoVerification.E2E.mlkemPk1Hook; vm_close

theorem mlkemPk2Hook_vmPreserved (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemPk2Hook s) := by
  unfold CryptoVerification.E2E.mlkemPk2Hook; vm_close

theorem mlkemEncaps1Hook_vmPreserved (K : MlKem) (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemEncaps1Hook K s) := by
  unfold CryptoVerification.E2E.mlkemEncaps1Hook retHook; vm_close

theorem mlkemEncaps2Hook_vmPreserved (K : MlKem) (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemEncaps2Hook K s) := by
  unfold CryptoVerification.E2E.mlkemEncaps2Hook; vm_close

theorem mlkemDecapsHook_vmPreserved (K : MlKem) (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemDecapsHook K s) := by
  unfold CryptoVerification.E2E.mlkemDecapsHook; vm_close

theorem mlkemValidatePkHook_vmPreserved (K : MlKem) (s : State) :
    VmPreserved s (CryptoVerification.E2E.mlkemValidatePkHook K s) := by
  unfold CryptoVerification.E2E.mlkemValidatePkHook; vm_close

/-! ## Formatting and Time Budget `HookOk` Witnesses -/

/-- `formatInnerHook0` satisfies `formatInnerBudgetSpec M A lim` for any `(M, A, lim)` (`0`
    allocations; writes empty `Vec` header `{0, 1, 0}`). -/
theorem formatInnerHook0_budget_ok (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    HookOk CryptoVerification.E2E.formatInnerHook0 (formatInnerBudgetSpec M A lim) := by
  rintro ⟨ret, st⟩ R s0 hrun hpre _hsp
  dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, _hFit⟩, hmem⟩
  have hmem_ret : s0.mem ⊨ memRegion ret 24 ∗
      (A.pool lim st s0 ∗ stackAt s0.sp extHookStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨hkf_w, hperm_w, hvec⟩ := write_empty_vecU8 (A := A.repAlloc) hmem_ret
  let mf := CryptoVerification.E2E.writeVecHeader s0.mem ret 0#64 1#64 0#64
  unfold CryptoVerification.E2E.formatInnerHook0
  rw [show retHook (fun s => s.setMem
        (CryptoVerification.E2E.writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)) s0 =
      retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
  obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
  refine ⟨hkf_w, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
  dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨[], ?_⟩
  have hpool_f :
      A.pool lim (M.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
        A.pool lim st s0 :=
    A.pool_transport lim st s0 _ (vmPreserved_retHook_setMem hperm_w)
  rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hvec_ex : mf ⊨ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc ret bs) ∗
      (A.pool lim st s0 ∗ stackAt s0.sp extHookStack ∗ R) :=
    Satisfies.mono (sepConj_mono_left (Entails.sepExists_right [] (Entails.refl _))) hvec
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec_ex

/-- `fmtWriteHook0` satisfies `fmtWriteBudgetSpec M A lim` for any `(M, A, lim)` (`0` allocations;
    returns `x0 = 0` leaving `vecU8` intact). -/
theorem fmtWriteHook0_budget_ok (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    HookOk CryptoVerification.E2E.fmtWriteHook0 (fmtWriteBudgetSpec M A lim) := by
  unfold CryptoVerification.E2E.fmtWriteHook0
  refine retHook_ok fun ⟨v, bs, st⟩ R s0 hrun hpre _hsp => ?_
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hx0, _hFit⟩, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨[], ?_⟩
  have hx0_post :
      ((retHook (fun s => s.writeReg64 .x0 0#64) s0).readReg64 .x0).setWidth 32 = 0#32 := by
    simp [retHook]
  have hpool_f :
      A.pool lim (M.stepEvents [] st) (retHook (fun s => s.writeReg64 .x0 0#64) s0) =
        A.pool lim st s0 := by
    change A.pool lim st ((s0.writeReg64 .x0 0#64).setPC (s0.readReg64 .lr)) = A.pool lim st s0
    rw [A.pool_setPC, A.pool_writeReg64]
  have hmem_f : (s0.writeReg64 .x0 0#64).mem = s0.mem := mem_writeReg64 s0 .x0 0#64
  have htr_f : (retHook (fun s => s.writeReg64 .x0 0#64) s0).trace = s0.trace := by
    cases s0; rfl
  rw [hpool_f, hmem_f, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_post, htr_f, rfl⟩, ?_⟩
  have hmem_ex : s0.mem ⊨ (∃∗ bs' : List (BitVec 8), vecU8 A.repAlloc v bs') ∗
      (A.pool lim st s0 ∗ stackAt s0.sp extHookStack ∗ R) :=
    Satisfies.mono (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _)))
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem)
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_ex

/-- `timeAddHook` satisfies `timeAddBudgetSpec = withVmPreserved timeAddSpec`. -/
theorem timeAddHook_budget_ok :
    HookOk CryptoVerification.E2E.timeAddHook timeAddBudgetSpec :=
  hookOk_withVmPreserved CryptoVerification.E2E.HooksE.timeAddHook_ok timeAddHook_vmPreserved

/-- `hookNoop` satisfies `durationSinceSpec` (and hence `durationSinceBudgetSpec` via
    `hookNoop_durationSinceBudget_ok`). -/
theorem hookNoop_durationSince_ok : HookOk hookNoop durationSinceSpec := by
  refine hookNoop_ok fun ⟨p, ret⟩ R s0 hpre => ?_
  dsimp only [durationSinceSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨rfl, hpre.2⟩

/-- `hookNoop` satisfies `durationSinceBudgetSpec = withVmPreserved durationSinceSpec`. -/
theorem hookNoop_durationSinceBudget_ok : HookOk hookNoop durationSinceBudgetSpec :=
  hookOk_withVmPreserved hookNoop_durationSince_ok hookNoop_vmPreserved

/-- `durationSinceExactHook` satisfies `durationSinceEpochBudgetSpec =
    withVmPreserved CliExt.durationSinceEpochSpec`. -/
theorem durationSinceExactHook_epoch_budget_ok :
    HookOk durationSinceExactHook durationSinceEpochBudgetSpec :=
  hookOk_withVmPreserved
    CryptoVerification.SignalSession.Cli.Slots.durationSinceExactHook_epoch_ok
    durationSinceExactHook_vmPreserved

/-! ## ML-KEM-768 Incremental Budget `HookOk` Witnesses -/

theorem mlkemFromSeedHook_budget_ok (K : MlKem) :
    HookOk (CryptoVerification.E2E.mlkemFromSeedHook K)
      (withVmPreserved (mlkemFromSeedSpec K)) :=
  hookOk_withVmPreserved (CryptoVerification.E2E.Pqxdh.mlkemFromSeedHook_ok K)
    (mlkemFromSeedHook_vmPreserved K)

theorem mlkemPk1Hook_budget_ok :
    HookOk CryptoVerification.E2E.mlkemPk1Hook (withVmPreserved mlkemPk1Spec) :=
  hookOk_withVmPreserved CryptoVerification.E2E.Pqxdh.mlkemPk1Hook_ok mlkemPk1Hook_vmPreserved

theorem mlkemPk2Hook_budget_ok :
    HookOk CryptoVerification.E2E.mlkemPk2Hook (withVmPreserved mlkemPk2Spec) :=
  hookOk_withVmPreserved CryptoVerification.E2E.Pqxdh.mlkemPk2Hook_ok mlkemPk2Hook_vmPreserved

theorem mlkemEncaps1Hook_budget_ok (K : MlKem) :
    HookOk (CryptoVerification.E2E.mlkemEncaps1Hook K)
      (withVmPreserved (mlkemEncaps1Spec K)) :=
  hookOk_withVmPreserved (CryptoVerification.E2E.Pqxdh.mlkemEncaps1Hook_ok K)
    (mlkemEncaps1Hook_vmPreserved K)

theorem mlkemEncaps2Hook_budget_ok (K : MlKem) :
    HookOk (CryptoVerification.E2E.mlkemEncaps2Hook K)
      (withVmPreserved (mlkemEncaps2Spec K)) :=
  hookOk_withVmPreserved (CryptoVerification.E2E.Pqxdh.mlkemEncaps2Hook_ok K)
    (mlkemEncaps2Hook_vmPreserved K)

theorem mlkemDecapsHook_budget_ok (K : MlKem) :
    HookOk (CryptoVerification.E2E.mlkemDecapsHook K)
      (withVmPreserved (mlkemDecapsSpec K)) :=
  hookOk_withVmPreserved (CryptoVerification.E2E.Pqxdh.mlkemDecapsHook_ok K)
    (mlkemDecapsHook_vmPreserved K)

theorem mlkemValidatePkHook_budget_ok (K : MlKem) :
    HookOk (CryptoVerification.E2E.mlkemValidatePkHook K)
      (withVmPreserved (mlkemValidatePkSpec K)) :=
  hookOk_withVmPreserved (CryptoVerification.E2E.Pqxdh.mlkemValidatePkHook_ok K)
    (mlkemValidatePkHook_vmPreserved K)

/-! ## Non-Allocating `CliExt` `HookOk` Witnesses -/

section CliExtHookWitnesses

open CryptoVerification.SignalSession.ExternsWitness (
  blackBoxHook_ok compress512Hook_ok dsmbHook_ok hookOk_cliWithStack hookOk_map
  kemDecapsHook_ok kemEncapsHook_ok leafHook_ok toEdwardsHook_ok torsionFreeHook_ok
)

theorem cliShim_hookOk : HookOk hookNoop shimSpec :=
  CryptoVerification.LibsignalTripleRatchet.sessionShim_hookOk

theorem cliMemset_hookOk : HookOk hookMemset memsetSpec :=
  CryptoVerification.LibsignalTripleRatchet.hookMemset_trace_ok

theorem cliMemmove_hookOk : HookOk hookMemmove memmoveSpec :=
  CryptoVerification.LibsignalTripleRatchet.hookMemmove_trace_ok

theorem cliMemcpy_hookOk : HookOk hookMemcpy memcpySpec :=
  CryptoVerification.LibsignalTripleRatchet.hookMemcpy_trace_ok

theorem cliMemcpyRO_hookOk : HookOk hookMemcpy memcpyROSpec :=
  hookOk_cliWithStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok
    memHookStack (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem cliBcmp_hookOk (W : CliHooks) : HookOk (cliBcmpHook W.bcmp) bcmpSpec :=
  hookOk_map (s₁ := CryptoVerification.SignalSession.Cli.cliBcmpSpec)
    (fun x => ⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩)
    (fun _ _ => True) (fun _ => trivial)
    (CryptoVerification.SignalSession.Cli.RunGlue.cliBcmpHook_ok W)
    (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem cliStrlen_hookOk : HookOk strlenHook strlenSpec :=
  CryptoVerification.SignalSession.Cli.MainHops.strlenHook_ok extHookStack

theorem cliWriteFile_hookOk (img : Obj.Image) :
    HookOk writeFileHook (writeFileSpec img) :=
  hookOk_map
    (s₁ := CryptoVerification.SignalSession.Cli.MainHops.writeFileSpec
      CryptoVerification.SignalSession.Cli.MainHops.cliIo img extHookStack)
    (fun x => ⟨x.pathA, x.path, x.buf, x.bs⟩)
    (fun _ _ => True) (fun _ => trivial)
    (CryptoVerification.SignalSession.Cli.MainHops.writeFileHook_ok img extHookStack)
    (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem cliWriteStdout_hookOk (img : Obj.Image) :
    HookOk writeStdoutHook (writeStdoutSpec img) :=
  hookOk_map
    (s₁ := CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpec img extHookStack)
    (fun x => ⟨x.buf, x.bs⟩)
    (fun _ _ => True) (fun _ => trivial)
    (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutHook_ok img extHookStack)
    (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem cliMemrchr_hookOk : HookOk memrchrHook memrchrSpec :=
  hookOk_map
    (s₁ := CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)
    (fun x => ⟨x.c, x.p, x.bs⟩)
    (fun _ _ => True) (fun _ => trivial)
    (CryptoVerification.SignalSession.Cli.MainHops.memrchrHook_ok extHookStack)
    (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem cliFromUtf8_hookOk (W : CliHooks) :
    HookOk (fromUtf8Hook W.utf8Err) fromUtf8Spec :=
  CryptoVerification.SignalSession.Cli.MainHops.fromUtf8Hook_ok extHookStack W.utf8Err

theorem cliBlackBox_hookOk :
    HookOk CryptoVerification.LibsignalSession.blackBoxHook blackBoxSpec :=
  blackBoxHook_ok

theorem cliCompress256_hookOk (C : Crypto) :
    HookOk (CryptoVerification.LibsignalHmac.compress256Hook C.F)
      (compress256Spec C) :=
  hookOk_cliWithStack
    (CryptoVerification.LibsignalTripleRatchet.compress256Hook_ok C.F) extHookStack
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem cliPubFromSecret_hookOk (C : Crypto) :
    HookOk (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook C.pubKey)
      (pubFromSecretSpec C) :=
  hookOk_cliWithStack
    (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook_ok C.pubKey) extHookStack
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem cliDh_hookOk (C : Crypto) :
    HookOk (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook C.X)
      (dhSpec C) :=
  hookOk_cliWithStack
    (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook_ok C.X) extHookStack
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem cliZeroize_hookOk :
    HookOk CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook zeroizeSpec :=
  hookOk_cliWithStack
    CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook_ok extHookStack
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem cliCompress512_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.compress512Hook Q.F512) (compress512Spec Q) :=
  compress512Hook_ok Q

theorem cliToEdwards_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.toEdwardsHook Q.montToEd) (toEdwardsSpec Q) :=
  toEdwardsHook_ok Q

theorem cliCompress_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.compressHook Q.compress)
      (pureByteFunctionSpec Q.compress false) :=
  leafHook_ok (by decide) Q.compress false

theorem cliEdNeg_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.edNegHook Q.edNeg)
      (pureByteFunctionSpec Q.edNeg true) :=
  leafHook_ok (by decide) Q.edNeg true

theorem cliTorsionFree_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.torsionFreeHook Q.isTorsionFree)
      (torsionFreeSpec Q) :=
  torsionFreeHook_ok Q

theorem cliDsmb_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.dsmbHook Q.dsmb) (dsmbSpec Q) :=
  dsmbHook_ok Q

theorem cliScalarMod_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.scalarModHook Q.scalarMod)
      (pureByteFunctionSpec Q.scalarMod true) :=
  leafHook_ok (by decide) Q.scalarMod true

theorem cliScalarWide_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.scalarWideHook Q.scalarWide)
      (pureByteFunctionSpec Q.scalarWide false) :=
  leafHook_ok (by decide) Q.scalarWide false

theorem cliKemEncaps_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.kemEncapsHook Q.encaps) (kemEncapsSpec Q) :=
  kemEncapsHook_ok Q

theorem cliKemDecaps_hookOk (Q : CryptoVerification.E2E.PqxdhPrims) :
    HookOk (CryptoVerification.E2E.kemDecapsHook Q.decaps) (kemDecapsSpec Q) :=
  kemDecapsHook_ok Q

end CliExtHookWitnesses

end LibsignalBinary.Heap.Fine
