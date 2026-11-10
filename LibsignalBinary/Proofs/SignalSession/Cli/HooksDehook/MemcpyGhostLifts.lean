/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsDeserialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX -- proof-setup: allow-public-import

/-!
# File-Local Consumer `HookOk` Ghost Lifts for `memcpy` (`HooksDehook.MemcpyGhostLifts`)

`WP6a-mc1` (`#1255` L5) `HookOk` consequence lifts from `masterMemcpySpec` / `memcpySpecK` to the
remaining in-cone file-local and namespace-distinct `memcpy` consumer specifications on `main`:

1. `CryptoVerification.E2E.Bin.openMemcpySpec` (`OpenSegsDeserialize.lean:159`) and
   `CryptoVerification.E2E.Bin.openMemcpyRoSpec` (`OpenSegsPartyRoData.lean:125`).
2. `CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity.hashbrownMemcpyRegionSpec`
   (`FallibleWithCapacity.lean:122`).
3. `CryptoVerification.E2E.Pqxdh.Initiator.pqxdhMemcpyRegionSpec` (`HandshakeDerive.lean:915`) and
   its `withVmPreserved` (`pqxdhMemcpyRegionBudgetSpec`) counterpart.
4. `CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec`
   (`ChainClone3/ChainCloneEpilogue.lean:526`), its `ChainCloneEpilogueBudget` alias (`:504`), and
   `CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec`
   (`Record/Serialization/SessionCloneAux/ChainCloneEpilogue.lean:716`).
5. `LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec`
   (`RustStdAllocBudgetBridge.lean:811`, consumed by `Initiate/HooksPlacedBudget.lean:174`).
6. `CryptoVerification.LibsignalTripleRatchet.sessionMemcpyROXSpec`
   (`SessionRecordAt/TripleRatchet/HooksX.lean:47`) and its `withVmPreserved` counterpart.

Fixed-320 mixed-`↦₆₄` `pcs` contracts (`memcpyRecvPcsSpec[S]`, `memcpyPcs[Budget]Spec`) live in the
companion leaf module `HooksDehook.MemcpyGhostLiftsPcs`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords memcpySrc)
open CryptoVerification.E2E.Bin (openMemcpySpec openMemcpyRoSpec)
open CryptoVerification.E2E.InMem.HashbrownBin.FallibleWithCapacity (hashbrownMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (pqxdhMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpyROXSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec memcpySpecK
  hookOk_map_frame_pureAbort hookOk_memcpySpecK_map_frame_pureAbort
  hookOk_framelessMemcpyBudgetFlat_of_master hookOk_framelessMemcpyBudgetFlatK_of_master
  memcpySpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK
  memcpyGhostHook_master_ok memcpyGhostHookK_masterK_ok
  memcpyGhostHook_vmPreserved memcpyGhostHookK_vmPreserved
  memcpyGhostHook_oracle memcpyGhostHookK_oracle
)

/-! ## 1. Generic `HookOk` Consequence Lifts from `masterMemcpySpec` & `memcpySpecK` -/

/-- B1: Lift `HookOk f masterMemcpySpec` to `openMemcpySpec` (`ro = false`). -/
theorem hookOk_openMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f openMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, openMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- B1 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to `openMemcpySpec`. -/
theorem hookOk_openMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep openMemcpySpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpySpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, openMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- B2: Lift `HookOk f masterMemcpySpec` to `openMemcpyRoSpec` (`ro = true`). -/
theorem hookOk_openMemcpyRo_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f openMemcpyRoSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpyRoSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, openMemcpyRoSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- B2 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to `openMemcpyRoSpec`. -/
theorem hookOk_openMemcpyRoK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep openMemcpyRoSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [openMemcpyRoSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, _⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)
  · dsimp only [masterMemcpySpec, openMemcpyRoSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1, hst.2.2.1⟩ (Entails.refl _)

/-- B3: Lift `HookOk f masterMemcpySpec` to `hashbrownMemcpyRegionSpec` (`ro = false`). -/
theorem hookOk_hashbrownMemcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f hashbrownMemcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [hashbrownMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, hashbrownMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B3 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `hashbrownMemcpyRegionSpec`. -/
theorem hookOk_hashbrownMemcpyRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep hashbrownMemcpyRegionSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [hashbrownMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, hashbrownMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B4: Lift `HookOk f masterMemcpySpec` to `pqxdhMemcpyRegionSpec` (`ro = false`). -/
theorem hookOk_pqxdhMemcpyRegion_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f pqxdhMemcpyRegionSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [pqxdhMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, pqxdhMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B4 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to `pqxdhMemcpyRegionSpec`. -/
theorem hookOk_pqxdhMemcpyRegionK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep pqxdhMemcpyRegionSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [pqxdhMemcpyRegionSpec, memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec, pqxdhMemcpyRegionSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B7: Lift `HookOk f masterMemcpySpec` to `ChainClone3.sessionMemcpySpec` (`ro = false`). -/
theorem hookOk_chainClone3SessionMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B7 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `ChainClone3.sessionMemcpySpec`. -/
theorem hookOk_chainClone3SessionMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f
      (memcpySpecK keep CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B7 Budget alias: `ChainCloneEpilogueBudget.sessionMemcpySpec` (`= framelessMemcpyBudgetSpec`). -/
theorem hookOk_chainClone3SessionMemcpyBudget_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec :=
  hookOk_framelessMemcpyBudgetFlat_of_master hh hvm

/-- B7 Budget alias (`K`). -/
theorem hookOk_chainClone3SessionMemcpyBudgetK_of_master (keep : BitVec 64 → Bool)
    {f : State → State} (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      (memcpySpecK keep
        LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec) :=
  hookOk_framelessMemcpyBudgetFlatK_of_master keep hh hvm

/-- B8: Lift `HookOk f masterMemcpySpec` to `ChainCloneLocal1.sessionMemcpySpec` (`ro = false`). -/
theorem hookOk_recordSessionCloneMemcpy_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B8 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `ChainCloneLocal1.sessionMemcpySpec`. -/
theorem hookOk_recordSessionCloneMemcpyK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f
      (memcpySpecK keep
        CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.refl _
  · dsimp only [masterMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B9: Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` + `oracle` preservation to
    `RustStdAllocBudgetBridge.allocMemcpyVmSpec` (`ro = false`). -/
theorem hookOk_rustStdAllocMemcpyVm_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, hlt⟩ =>
      have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
        rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      Entails.pure_right ⟨hx0, hx1, hx2_nat⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- B9 (`K`): `K`-narrowed counterpart of `hookOk_rustStdAllocMemcpyVm_of_master`. -/
theorem hookOk_rustStdAllocMemcpyVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) :
    HookOk f
      (memcpySpecK keep LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (false, d, s, b))
    (fun _ _ => emp) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf hsf hsym => ?_)
  · dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec,
      masterMemcpySpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hx1, hx2, hlt⟩ =>
      have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
        rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      Entails.pure_right ⟨hx0, hx1, hx2_nat⟩ (Entails.refl _)
  · subst hsf
    dsimp only [masterMemcpySpec,
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec, memcpySrc, cond]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- B10: Lift `HookOk f masterMemcpySpec` to `HooksX.sessionMemcpyROXSpec` (`ro = true`). -/
theorem hookOk_sessionMemcpyROX_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f sessionMemcpyROXSpec := by
  refine hookOk_map_frame_pureAbort (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpyROXSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, sessionMemcpyROXSpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- B10 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `HooksX.sessionMemcpyROXSpec`. -/
theorem hookOk_sessionMemcpyROXK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep sessionMemcpyROXSpec) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun ⟨d, s, b⟩ => (true, d, s, b))
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf _ _ => ?_)
  · dsimp only [sessionMemcpyROXSpec, masterMemcpySpec, memcpySrc, cond]
    exact Entails.of_eq (by simp only [sepConj_assoc])
  · dsimp only [masterMemcpySpec, sessionMemcpyROXSpec, memcpySrc, cond]
    rw [sepConj_assoc, sepConj_assoc]
    exact Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-! ## 2. Instantiations for `memcpyGhostHook` & `memcpyGhostHookK` -/

section GhostHookLifts

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memcpySymWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem memcpyGhostHook_openMemcpy_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) openMemcpySpec :=
  hookOk_openMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_openMemcpy_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withVmPreserved openMemcpySpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_openMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_openMemcpyK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (memcpySpecK keep openMemcpySpec) :=
  hookOk_openMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_openMemcpyK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved openMemcpySpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_openMemcpyK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_openMemcpyRo_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) openMemcpyRoSpec :=
  hookOk_openMemcpyRo_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_openMemcpyRo_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withVmPreserved openMemcpyRoSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_openMemcpyRo_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_openMemcpyRoK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget) (memcpySpecK keep openMemcpyRoSpec) :=
  hookOk_openMemcpyRoK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_openMemcpyRoK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved openMemcpyRoSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_openMemcpyRoK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_hashbrownMemcpyRegion_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) hashbrownMemcpyRegionSpec :=
  hookOk_hashbrownMemcpyRegion_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_hashbrownMemcpyRegion_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved hashbrownMemcpyRegionSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_hashbrownMemcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_hashbrownMemcpyRegionK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep hashbrownMemcpyRegionSpec) :=
  hookOk_hashbrownMemcpyRegionK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_hashbrownMemcpyRegionK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved hashbrownMemcpyRegionSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_hashbrownMemcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_pqxdhMemcpyRegion_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) pqxdhMemcpyRegionSpec :=
  hookOk_pqxdhMemcpyRegion_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_pqxdhMemcpyRegion_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved pqxdhMemcpyRegionSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_pqxdhMemcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_pqxdhMemcpyRegionK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep pqxdhMemcpyRegionSpec) :=
  hookOk_pqxdhMemcpyRegionK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_pqxdhMemcpyRegionK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved pqxdhMemcpyRegionSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_pqxdhMemcpyRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_chainClone3SessionMemcpy_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec :=
  hookOk_chainClone3SessionMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_chainClone3SessionMemcpyBudget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec :=
  hookOk_chainClone3SessionMemcpyBudget_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_chainClone3SessionMemcpyK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep CryptoVerification.LibsignalTripleRatchet.ChainClone3.sessionMemcpySpec) :=
  hookOk_chainClone3SessionMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_chainClone3SessionMemcpyBudgetK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogueBudget.sessionMemcpySpec) :=
  hookOk_chainClone3SessionMemcpyBudgetK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_recordSessionCloneMemcpy_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec :=
  hookOk_recordSessionCloneMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_recordSessionCloneMemcpy_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_recordSessionCloneMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_recordSessionCloneMemcpyK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec) :=
  hookOk_recordSessionCloneMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_recordSessionCloneMemcpyK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep
        (withVmPreserved
          CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.sessionMemcpySpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_recordSessionCloneMemcpyK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
  |> fun hok => hookOk_withVmPreserved hok
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_rustStdAllocMemcpyVm_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec :=
  hookOk_rustStdAllocMemcpyVm_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_rustStdAllocMemcpyVmK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec) :=
  hookOk_rustStdAllocMemcpyVmK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyROX_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) sessionMemcpyROXSpec :=
  hookOk_sessionMemcpyROX_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyROX_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved sessionMemcpyROXSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_sessionMemcpyROX_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyROXK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep sessionMemcpyROXSpec) :=
  hookOk_sessionMemcpyROXK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_sessionMemcpyROXK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved sessionMemcpyROXSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_sessionMemcpyROXK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

end GhostHookLifts

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLifts
