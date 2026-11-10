/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget -- proof-setup: allow-public-import

/-!
# Fixed-320 Mixed-`↦₆₄` `pcs` `HookOk` Ghost Lifts (`HooksDehook.MemcpyGhostLiftsPcs`)

`WP6a-mc1` (`#1255` L5) `HookOk` consequence lifts from `masterMemcpySpec` / `memcpySpecK` to the
fixed-320-byte mixed-layout (`memRegion` + `↦₆₄`) decode-payload `memcpy` contracts:

1. `CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.memcpyRecvPcsSpec` (`Defs.lean:220`),
   its `stackAt sp extHookStack` wrapper `memcpyRecvPcsSpecS` (`:379`), and
   `withVmPreserved memcpyRecvPcsSpec`.
2. `CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.memcpyPcsSpec` (`Core.lean:256`) and
   `LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget.memcpyPcsBudgetSpec`
   (`CoreBudget.lean:140`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs

open Arm64 ProofLib SepProp
open VerifiedLibraries.Musl (memcpySymWords)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty (
  memcpyRecvPcsSpec memcpyRecvPcsSpecS
)
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty (memcpyPcsSpec)
open LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget (memcpyPcsBudgetSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec memcpySpecK
  hookOk_map_frame_pureAbort hookOk_memcpySpecK_map_frame_pureAbort
  hookOk_sessionMemcpyRegion_of_master hookOk_sessionMemcpyRegionK_of_master
  memcpySpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK
  memcpyGhostHook_master_ok memcpyGhostHookK_masterK_ok
  memcpyGhostHook_vmPreserved memcpyGhostHookK_vmPreserved
)

/-! ## 1. `SpqrRecvEmpty.memcpyRecvPcsSpec` & `memcpyRecvPcsSpecS` (Target B5) -/

/-- B5: Lift `HookOk f masterMemcpySpec` to `memcpyRecvPcsSpec` (`320` B mixed `↦₆₄` layout). -/
theorem hookOk_memcpyRecvPcs_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpyRecvPcsSpec := by
  have hreg := hookOk_sessionMemcpyRegion_of_master hh
  intro ⟨t, c, i⟩ R s0 hrun hpre hsp
  simp only [memcpyRecvPcsSpec] at hpre
  rw [← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_src,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right
    (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ sessionMemcpyRegionSpec.pre
      (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  obtain ⟨hkf, hsym, hout⟩ :=
    hreg (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
      R s0 hrun hpre_mc hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpyRecvPcsSpec]
    rw [← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_src,
      ← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_dst,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5)
      (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5))) hpost_mem
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- B5 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to `memcpyRecvPcsSpec`. -/
theorem hookOk_memcpyRecvPcsK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpyRecvPcsSpec) := by
  have hregK := hookOk_sessionMemcpyRegionK_of_master keep hh
  intro ⟨t, c, i⟩ R s0 hrun hpre hsp
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre⟩ := hpre
  simp only [memcpyRecvPcsSpec] at hpre
  rw [← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_src,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right
    (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ (memcpySpecK keep sessionMemcpyRegionSpec).pre
      (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hlr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  obtain ⟨hkf, hsym, hout⟩ :=
    hregK (t - 4960#64, t - 3024#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
      R s0 hrun hpre_mc hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [memcpySpecK, sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpySpecK, memcpyRecvPcsSpec]
    rw [← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_src,
      ← CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_dst,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5)
      (CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5))) hpost_mem
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- B5 (`SpecS`): Lift `HookOk f masterMemcpySpec` to `memcpyRecvPcsSpecS`. -/
theorem hookOk_memcpyRecvPcsS_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpyRecvPcsSpecS := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp extHookStack)
    (hookOk_memcpyRecvPcs_of_master hh)
    (fun _ _ => Entails.refl _)
    (fun _ _ _ _ _ => Entails.refl _)

/-- B5 (`SpecS`, `K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to
    `memcpyRecvPcsSpecS`. -/
theorem hookOk_memcpyRecvPcsSK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpyRecvPcsSpecS) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp extHookStack)
    (hookOk_memcpyRecvPcsK_of_master keep hh)
    (fun _ _ => Entails.refl _)
    (fun _ _ _ _ _ => Entails.refl _)

/-! ## 2. `SpqrSendEmpty.memcpyPcsSpec` & `memcpyPcsBudgetSpec` (Target B6) -/

/-- B6: Lift `HookOk f masterMemcpySpec` to `memcpyPcsSpec` (`320` B mixed `↦₆₄` layout). -/
theorem hookOk_memcpyPcs_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) :
    HookOk f memcpyPcsSpec := by
  have hreg := hookOk_sessionMemcpyRegion_of_master hh
  intro ⟨t, c, i⟩ R s0 hrun hpre hsp
  simp only [memcpyPcsSpec] at hpre
  rw [← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_src,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right
    (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ sessionMemcpyRegionSpec.pre
      (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  obtain ⟨hkf, hsym, hout⟩ :=
    hreg (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
      R s0 hrun hpre_mc hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpyPcsSpec]
    rw [← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_src,
      ← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_dst,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5)
      (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5))) hpost_mem
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- B6 (`K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` to `memcpyPcsSpec`. -/
theorem hookOk_memcpyPcsK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec)) :
    HookOk f (memcpySpecK keep memcpyPcsSpec) := by
  have hregK := hookOk_sessionMemcpyRegionK_of_master keep hh
  intro ⟨t, c, i⟩ R s0 hrun hpre hsp
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre⟩ := hpre
  simp only [memcpyPcsSpec] at hpre
  rw [← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_src,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right
    (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc : s0.mem ⊨ (memcpySpecK keep sessionMemcpyRegionSpec).pre
      (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hlr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  obtain ⟨hkf, hsym, hout⟩ :=
    hregK (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
      R s0 hrun hpre_mc hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [memcpySpecK, sessionMemcpyRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost
    dsimp only [memcpySpecK, memcpyPcsSpec]
    rw [← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_src,
      ← CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_dst,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hx0_sf⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono
      (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5)
      (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.pcs_of_bytes _ c i b1 b3 b5
        h1 h3' h5))) hpost_mem
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [memcpySpecK, sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- B6 (`Budget`): Lift `HookOk f masterMemcpySpec` + pointwise `VmPreserved` to
    `memcpyPcsBudgetSpec`. -/
theorem hookOk_memcpyPcsBudget_of_master {f : State → State}
    (hh : HookOk f masterMemcpySpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f memcpyPcsBudgetSpec :=
  hookOk_withVmPreserved (hookOk_memcpyPcs_of_master hh) hvm

/-- B6 (`Budget`, `K`): Lift `HookOk f (memcpySpecK keep masterMemcpySpec)` + pointwise
    `VmPreserved` to `memcpySpecK keep memcpyPcsBudgetSpec`. -/
theorem hookOk_memcpyPcsBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memcpySpecK keep masterMemcpySpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (memcpySpecK keep memcpyPcsBudgetSpec) := by
  change HookOk f (memcpySpecK keep (withVmPreserved memcpyPcsSpec))
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved (hookOk_memcpyPcsK_of_master keep hh) hvm

/-! ## 3. Instantiations for `memcpyGhostHook` & `memcpyGhostHookK` -/

section GhostHookPcsLifts

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memcpySymWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem memcpyGhostHook_memcpyRecvPcs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyRecvPcsSpec :=
  hookOk_memcpyRecvPcs_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRecvPcsS_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyRecvPcsSpecS :=
  hookOk_memcpyRecvPcsS_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRecvPcs_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved memcpyRecvPcsSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_memcpyRecvPcs_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRecvPcsK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyRecvPcsSpec) :=
  hookOk_memcpyRecvPcsK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRecvPcsSK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyRecvPcsSpecS) :=
  hookOk_memcpyRecvPcsSK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyRecvPcsK_budget_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep (withVmPreserved memcpyRecvPcsSpec)) := by
  rw [← memcpySpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memcpyGhostHookK_memcpyRecvPcsK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyPcs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyPcsSpec :=
  hookOk_memcpyPcs_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyPcsBudget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyPcsBudgetSpec :=
  hookOk_memcpyPcsBudget_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyPcsK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyPcsSpec) :=
  hookOk_memcpyPcsK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHookK_memcpyPcsBudgetK_ok :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep memcpyPcsBudgetSpec) :=
  hookOk_memcpyPcsBudgetK_of_master keep
    (memcpyGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

end GhostHookPcsLifts

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostLiftsPcs
