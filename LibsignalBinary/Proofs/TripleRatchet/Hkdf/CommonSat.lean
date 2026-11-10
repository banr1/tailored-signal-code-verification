/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSegsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.HeapIntro

/-!
# `HookSat`-Parameterized HKDF Hook Bundles and Step Lemmas

Defines `HkdfPlacedHooksSat` (specifying `memset` via `HookSat H lsMemsetSym sessionMemsetRegionSpec`
replacing `some memsetHook`) and its `HookSatExactMemcpy H lsMemcpySym` sibling `HkdfPlacedHooksExactSat`
(with automatic `instance HkdfPlacedHooksSat.toExactSat`), along with `S2Frame` / `AgreesOn` framing
lemmas and `[LibsignalPlacement]` `RunsToFrom` hook-step rules.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoGames.HMAC (ShaState)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved HkdfPlacedHooks RW RunsTo RunsToFrom TraceEq compress256Hook_eq
   hookMemset_eq_memsetHook hookMemset_region_trace_ok lsCompress256Sym lsMemcpySym
   lsMemsetSym ls_externAt?_of_mem memcpyHook_eq sessionMemsetRegionSpec
   shaStateBytes_length truncate8_truncate32)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (S2Frame disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap
   read8_eq_of_readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open VerifiedLibraries.Musl (memcpySrc)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (hookOk_sessionMemcpyRegion_of_master hookOk_sessionMemcpy_of_master masterMemcpySpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact hookSatExactMemcpy_of_eq
   memcpyHook_exact s2_memcpy_step_placed_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec)

/-! ## `HkdfPlacedHooksSat` and Coercions -/

/-- `HookSat`-parameterized sibling of `HkdfPlacedHooks`: replaces the extensional equality
`H lsMemsetSym = some memsetHook` with `HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
public class HkdfPlacedHooksSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionSpec
  memcpy : H lsMemcpySym = some memcpyHook
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- `memsetHook` satisfies `sessionMemsetRegionSpec` (transferred from `hookMemset_region_trace_ok`
via `hookMemset_eq_memsetHook`). -/
public theorem memsetHook_region_trace_ok : HookOk memsetHook sessionMemsetRegionSpec :=
  hookMemset_eq_memsetHook ▸ hookMemset_region_trace_ok

public theorem hookSat_memsetHook_of_eq {H : LibsignalHooks}
    (h : H lsMemsetSym = some memsetHook) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec :=
  ⟨memsetHook, h, memsetHook_region_trace_ok⟩

public theorem hookSat_hookMemset_of_eq {H : LibsignalHooks}
    (h : H lsMemsetSym = some ProofLib.hookMemset) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec :=
  ⟨ProofLib.hookMemset, h, hookMemset_region_trace_ok⟩

public theorem HkdfPlacedHooks.toSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksSat F H where
  memset := hookSat_memsetHook_of_eq hH.memset
  memcpy := hH.memcpy
  compress256 := hH.compress256

public theorem hookSat_sessionMemsetRegion_of_budget {H : LibsignalHooks}
    (h : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec := by
  obtain ⟨f, hfH, hfOk⟩ := h
  refine ⟨f, hfH, fun x R s0 hrun hpre hsp => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hfOk x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpost⟩ | ⟨he, hcc, hpost⟩ | ⟨ho, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemsetRegionBudgetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl ⟨hp, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨he, hcc, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hpost⟩))

public theorem HkdfPlacedHooksSat.of_budget {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksSat F H where
  memset := hookSat_sessionMemsetRegion_of_budget h_memset
  memcpy := h_memcpy
  compress256 := h_compress

/-- `HookSatExactMemcpy`-widened sibling of `HkdfPlacedHooksSat`: relaxes
`memcpy : H lsMemcpySym = some memcpyHook` to `memcpy : HookSatExactMemcpy H lsMemcpySym`
while keeping `memset : HookSat H lsMemsetSym sessionMemsetRegionSpec` and
`compress256 : H lsCompress256Sym = some (compress256Hook F)`. -/
public class HkdfPlacedHooksExactSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionSpec
  memcpy : HookSatExactMemcpy H lsMemcpySym
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- Discharge `HookSatExactMemcpy H lsMemcpySym` from `H lsMemcpySym = some memcpyHook`. -/
public theorem hookSat_memcpyHook_exact_of_eq {H : LibsignalHooks}
    (h : H lsMemcpySym = some memcpyHook) :
    HookSatExactMemcpy H lsMemcpySym :=
  hookSatExactMemcpy_of_eq h memcpyHook_exact

/-- Discharge `HookSatExactMemcpy H lsMemcpySym` from `H lsMemcpySym = some ProofLib.hookMemcpy`. -/
public theorem hookSat_hookMemcpy_exact_of_eq {H : LibsignalHooks}
    (h : H lsMemcpySym = some ProofLib.hookMemcpy) :
    HookSatExactMemcpy H lsMemcpySym :=
  hookSatExactMemcpy_of_eq h hookMemcpy_exact

/-- Automatic widening instance from `HkdfPlacedHooksSat F H` to `HkdfPlacedHooksExactSat F H`
via `hookSatExactMemcpy_of_eq` + `memcpyHook_exact`, so callers holding `[HkdfPlacedHooksSat F H]`
transparently satisfy `[HkdfPlacedHooksExactSat F H]` as downstream modules migrate. -/
public instance HkdfPlacedHooksSat.toExactSat {F : ShaCompress} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksSat F H] : HkdfPlacedHooksExactSat F H where
  memset := hH.memset
  memcpy := hookSatExactMemcpy_of_eq hH.memcpy memcpyHook_exact
  compress256 := hH.compress256

/-- Direct coercion from `HkdfPlacedHooks F H` to `HkdfPlacedHooksExactSat F H`. -/
public theorem HkdfPlacedHooks.toExactSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksExactSat F H :=
  have _ : HkdfPlacedHooksSat F H := HkdfPlacedHooks.toSat hH
  inferInstance

/-- Construct `HkdfPlacedHooksExactSat F H` from a budget-strengthened `memset` `HookSat`
contract and `HookSatExactMemcpy H lsMemcpySym`. -/
public theorem HkdfPlacedHooksExactSat.of_budget {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksExactSat F H where
  memset := hookSat_sessionMemsetRegion_of_budget h_memset
  memcpy := h_memcpy
  compress256 := h_compress

/-! ## `CallingConventionPreserved` and `S2Frame` Helpers -/

public theorem CallingConventionPreserved.x23 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x23 = s.readReg64 .x23 :=
  h.2.2.2.2.2.1

public theorem CallingConventionPreserved.x24 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x24 = s.readReg64 .x24 :=
  h.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x25 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x25 = s.readReg64 .x25 :=
  h.2.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x26 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x26 = s.readReg64 .x26 :=
  h.2.2.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x28 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x28 = s.readReg64 .x28 :=
  h.2.2.2.2.2.2.2.2.2.2.1

private theorem isBlock_one_none_outside {P : SepProp} {b : BitVec 64} {n : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P b n Φ) {h : Heap} (hp : P h)
    {a : BitVec 64} (ha : OutsideRegion b n a) :
    h.phys a = none := by
  obtain ⟨m1, -, rfl⟩ := (hb.iff h).mp hp
  have hn : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  change (regionHeap b n m1).phys a = none
  simp [regionHeap, hn]

private theorem isBlock_one_mapped_false {P : SepProp} {b : BitVec 64} {n : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P b n Φ) {h : Heap} (hp : P h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨m1, -, rfl⟩ := (hb.iff h).mp hp
  simp [regionHeap]

/-- One-block analogue of `HkdfExt.isBlock_three_all_s2frame`: a hook transition transforming
`P` to `P'` on `[b, b + n)` while preserving `fullComplementHeap hP m` establishes
`S2Frame m m' [(b, n)]`. -/
public theorem isBlock_one_s2frame {P P' R' : SepProp} {b : BitVec 64} {n : Nat}
    {Φ Φ' : Memory → Prop}
    (hb : IsBlock P b n Φ) (hb' : IsBlock P' b n Φ')
    {hP : Heap} {m m' : Memory}
    (hpP : P hP) (hmP : hP.Matches m)
    (hpost : m' ⊨ P' ∗ R')
    (hmc : (fullComplementHeap hP m).Matches m') :
    S2Frame m m' [(b, n)] := by
  unfold Heap.Matches at hmc hmP
  have hmc_phys := hmc.1
  have hmc_map := hmc.2.2
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion b n a := ha (b, n) (by simp)
    have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc_phys a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc_phys a _ hca).1
  · by_cases hin : InRegion b n a
    · exact hb'.permNoLazy_rw hpost hin
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
      have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      obtain ⟨-, hp', hlf'⟩ := hmc_phys a _ hca
      exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin : InRegion b n a
    · exact hb'.perm_rw hpost hin
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      by_cases hlf_a : m.isLazyFree a = true
      · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        exact hmc_phys a .lazy hca
      · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_f]
        exact (hmc_phys a _ hca).2.1
  · have hm0 : hP.mapped a = false := isBlock_one_mapped_false hb hpP a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : hP.phys a = none := by
      obtain ⟨m1, -, rfl⟩ := (hb.iff hP).mp hpP
      cases ha : (regionHeap b n m1).phys a with
      | none => rfl
      | some c =>
        have hperm := hmP.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b n a <;> simp [regionHeap, h1] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b n a <;> simp [regionHeap, h1] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap hP m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc_phys a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap hP m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc_phys a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩
  · by_cases hin : InRegion b n a
    · exact ⟨by rw [hb'.perm_rw hpost hin]; rfl, hb'.isLazyFree_false hpost hin⟩
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      by_cases hrw_a : m.perm a = some Perm.rw
      · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc_phys a _ hca
        exact ⟨by rw [hp']; rfl, hlf'⟩
      · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
        obtain ⟨-, hr', hlf'⟩ := hmc_phys a _ hca
        exact ⟨hr', hlf'⟩

/-- If `m'` modifies only `(dst, bs.length)` relative to `m` via `S2Frame` and
`m'.readBytes dst bs.length = bs`, then `m'` agrees byte-for-byte with `m.writeBytes dst bs`
on every readable non-lazy address of `m`. -/
public theorem agreesOn_readable_of_s2Frame_writeBytes {m m' : Memory}
    {dst : BitVec 64} {bs : List (BitVec 8)}
    (hdst : m'.readBytes dst bs.length = bs)
    (hframe : S2Frame m m' [(dst, bs.length)])
    (hlen : bs.length ≤ 2 ^ 64) :
    AgreesOn (fun a => (m.perm a).r = true ∧ m.isLazyFree a = false)
      m' (m.writeBytes dst bs) := by
  intro a ⟨hr, hlf⟩
  by_cases hin : InRegion dst bs.length a
  · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset dst bs.length a hlen).mp hin
    have hwb : (m.writeBytes dst bs).readBytes dst bs.length = bs :=
      Memory.readBytes_writeBytes_same m dst bs hlen
    exact read8_eq_of_readBytes_eq (hdst.trans hwb.symm) hi
  · have hout : OutsideRegion dst bs.length a :=
      (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin
    have h1 : m'.read8 a = m.read8 a :=
      hframe.1 a hr hlf fun r hr_mem => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
        subst hr_mem; exact hout
    have h2 : (m.writeBytes dst bs).read8 a = m.read8 a :=
      (ProofLib.AgreesOutside.writeBytes_self m dst bs).1 a hout
    exact h1.trans h2.symm

/-- Execute a `HookOk f sessionMemsetRegionSpec` hook on a state `s` with `s.mem.RW dst len`,
yielding `Returned`, `CallingConventionPreserved`, `readBytes dst len = List.replicate len val`,
`S2Frame s.mem (f s).mem [(dst, len)]`, and `AgreesOn` with `s.mem.writeBytes dst (List.replicate len val)`. -/
public theorem hookOk_sessionMemsetRegion_elim {f : State → State}
    (hf : HookOk f sessionMemsetRegionSpec)
    {s : State} {dst : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len) :
    let s' := f s
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    s'.readReg64 .x0 = dst ∧
    s'.trace = s.trace ∧
    s'.mem.readBytes dst len = List.replicate len val ∧
    S2Frame s.mem s'.mem [(dst, len)] ∧
    AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
      s'.mem (s.mem.writeBytes dst (List.replicate len val)) := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hb_pre := IsBlock.memRegion dst len
  let hP : Heap := regionHeap dst len s.mem
  have hpP : (memRegion dst len) hP := (hb_pre.iff hP).mpr ⟨s.mem, trivial, rfl⟩
  have hmP : hP.Matches s.mem := IsBlock.regionHeap_matches dst len s.mem hrw
  let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
  have hsep_pre : s.mem ⊨ memRegion dst len ∗ R_comp :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx1_32 : (s.readReg32 .x1).truncate 8 = val := by
    rw [State.readReg32, truncate8_truncate32, hx1]
  have hpre_full : s.mem ⊨ sessionMemsetRegionSpec.pre (dst, val, len) s ∗ R_comp := by
    dsimp only [sessionMemsetRegionSpec, memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_32, hx2, hlen_le⟩, hsep_pre⟩
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  obtain ⟨hkf, hsym, hout⟩ := hf (dst, val, len) R_comp s hrun hpre_full hsp_aligned
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [sessionMemsetRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0', htr'⟩, hsep_post⟩ := hpost
    have hrep_len : (List.replicate len val).length = len := List.length_replicate
    have hb_post := IsBlock.pointsToBytes_len (a := dst) hrep_len
    have hread_post : (f s).mem.readBytes dst len = List.replicate len val := by
      have h := (hb_post.read hsep_post).2
      rwa [hrep_len] at h
    have hpost_R : (f s).mem ⊨ R_comp ∗ (dst ↦ₛ List.replicate len val) := by
      ac_nf at hsep_post ⊢
    have hm_post : (fullComplementHeap hP s.mem).Matches (f s).mem := by
      obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
      cases hR_hc'
      exact Heap.Matches.of_union_left hmatch
    have hs2 : S2Frame s.mem (f s).mem [(dst, len)] :=
      isBlock_one_s2frame hb_pre hb_post hpP hmP hsep_post hm_post
    have hread_rep : (f s).mem.readBytes dst (List.replicate len val).length =
        List.replicate len val := by rwa [hrep_len]
    have hs2_rep : S2Frame s.mem (f s).mem [(dst, (List.replicate len val).length)] := by
      rwa [hrep_len]
    have hag : AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        (f s).mem (s.mem.writeBytes dst (List.replicate len val)) :=
      agreesOn_readable_of_s2Frame_writeBytes hread_rep hs2_rep (by rw [hrep_len]; exact hlen_le)
    exact ⟨hkf, hsym, hret, hcc, hx0', htr', hread_post, hs2, hag⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## Placed `RunsToFrom` Step Lemmas -/

/-- Step through `memset` at `lsρ lsMemsetSym` in any placed block program `prog` using
`HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
public theorem s2_memset_step_placed_of_hookSat [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len val →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len val)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  obtain ⟨f, hfH, hfOk⟩ := h_memset
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hx0', htr', hread', hs2', hag'⟩ :=
    hookOk_sessionMemsetRegion_elim hfOk hrun hx0 hx1 hx2 hsp_al hrw
  have htr_f : TraceEq s (f s) := ⟨htr', hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hpc' : (f s).pc = lr := hret.1.trans hlr
  exact RunsTo.hook hrun hhook hkf hsym
    (h (f s) (TraceEq.trans htr_f htr_s) hpc' hret.2.2 hcc hx0' hkf hread' hs2' hag')

public theorem s2_memset_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memset_step_placed_of_hookSat hH.memset hrun hpc hx0 hx1 hx2 hlr hsp_al hrw h htr_s hi hunmut

public theorem s2_compress256_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.compress256]
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

public theorem s2_memcpy_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memcpyHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.memcpy]
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## 4. Placed `RunsToFrom` Step Lemmas under `HookSatExactMemcpy` / `HkdfPlacedHooksExactSat` -/

/-- Step through `memcpy` at `lsρ lsMemcpySym` in any placed block program `prog` using
`HookSatExactMemcpy H lsMemcpySym` (in the `∀ c : MemcpyClobber` shape with exact memory
`s.mem.writeBytes dst bs`). -/
public theorem s2_memcpy_step_placed_of_hookSatExact [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hsp : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  exact s2_memcpy_step_placed_of_exact H h_memcpy hrun hsp hpc hx0 hx1 hx2 hlr
    hread hrw hreadable hdisj h hi hunmut

/-- `[HkdfPlacedHooksExactSat C.F H]` wrapper for `s2_memcpy_step_placed_of_hookSatExact`. -/
public theorem s2_memcpy_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memcpy_step_placed_of_hookSatExact hH.memcpy hrun hpc hx0 hx1 hx2 hlr hsp_al
    hread hrw hreadable hdisj h hi hunmut

/-- `[HkdfPlacedHooksExactSat C.F H]` wrapper for `s2_memset_step_placed_of_hookSat` (`val = 0#8`). -/
public theorem s2_memset_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memset_step_placed_of_hookSat hH.memset hrun hpc hx0 hx1 hx2 hlr hsp_al hrw h htr_s hi hunmut

/-- Step through 1-block `compress256` under `[HkdfPlacedHooksExactSat C.F H]`. -/
public theorem s2_compress256_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.compress256]
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## 5. `VmPreserved` & Budget Spec Lifts from `HookExactMemcpy` -/

private theorem writeBytes_perm_eq (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    ∀ a : BitVec 64, (m.writeBytes base bs).perm a = m.perm a := by
  induction bs generalizing m base with
  | nil => intro _; rfl
  | cons _ _ ih =>
    intro a
    dsimp only [Memory.writeBytes]
    rw [ih]
    dsimp only [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

/-- `applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c` preserves `VmPreserved`
(`PoolPreserved`, `physMemAvail`, per-byte `mem.perm`, and `FdsHiFrame`). -/
public theorem vmPreserved_applyMemcpyClobber_writeBytes (s : State) (dst : BitVec 64)
    (bs : List (BitVec 8)) (lr : BitVec 64) (c : MemcpyClobber) :
    VmPreserved s (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) := by
  have hp := writeBytes_perm_eq s.mem dst bs
  cases s
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

/-- Pointwise `VmPreserved` (and `oracle` preservation) for any `HookExactMemcpy f` under the
standard `memcpy(dst, src, len)` register, `spAligned`, `RW`/`Readable`, and non-overlap
preconditions. -/
public theorem hookExactMemcpy_vmPreserved {f : State → State} (hf : HookExactMemcpy f)
    {u : State} {dst src : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    VmPreserved u (f u) ∧ (f u).oracle = u.oracle := by
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  rw [heq]
  exact ⟨vmPreserved_applyMemcpyClobber_writeBytes u dst bs (u.readReg64 .lr) c, rfl⟩

/-- Any `HookExactMemcpy f` satisfies `withVmPreserved masterMemcpySpec` (covering both `ro = false`
RW and `ro = true` RO sources) without requiring a global `∀ s, VmPreserved s (f s)` hypothesis. -/
private theorem hookExactMemcpy_withVmPreserved_master_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f (withVmPreserved masterMemcpySpec) := by
  rintro ⟨ro, dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [withVmPreserved, masterMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : bs.length ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc : s0.mem.readBytes src bs.length = bs ∧
      s0.mem.Readable src bs.length ∧
      (bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length) := by
    cases ro
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      have hb := IsBlock.pointsToBytes src bs
      refine ⟨(hb.read hsrc_front).2,
        fun a ha => ⟨by rw [hb.perm_rw hsrc_front ha]; rfl, hb.isLazyFree_false hsrc_front ha⟩, ?_⟩
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
        exact Or.inr ((IsBlock.memRegion dst bs.length).disjoint hb hpos hpos hmem)
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      have hb := IsBlockRO.pointsToBytesRO src bs hlen
      refine ⟨hb.read hsrc_front,
        fun a ha => ⟨hb.perm_r hsrc_front ha, hb.isLazyFree_false hsrc_front ha⟩, ?_⟩
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
        have hnd : ¬ InRegion dst bs.length src := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hlen (by simp [InRegion, hpos]))
            (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length src h))
            hsrc_front
        have hns : ¬ InRegion src bs.length dst := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hlen h)
            (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length dst (by simp [InRegion, hpos])))
            hsrc_front
        dsimp only [InRegion] at hnd hns
        exact Or.inr ⟨Nat.le_of_not_lt hnd, Nat.le_of_not_lt hns⟩
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hsrc.1 hrw hsrc.2.1 hsrc.2.2
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact vmPreserved_applyMemcpyClobber_writeBytes s0 dst bs (s0.readReg64 .lr) c
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [withVmPreserved, masterMemcpySpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [heq]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret :
      (applyMemcpyClobber s0 (s0.mem.writeBytes dst bs) (s0.readReg64 .lr) c).readReg64 .x0 =
        dst := hx0
  exact ⟨⟨hx0_ret, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

private theorem hookExactMemcpy_masterMemcpy_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f masterMemcpySpec := by
  intro x R s0 hrun hpre hsp
  rcases hookExactMemcpy_withVmPreserved_master_ok hf x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

/-- Separation-logic `VmPreserved` witness for any `HookExactMemcpy f` on a `memRegion dst bs.length ∗
memcpySrc ro src bs` footprint (both `ro = false` RW and `ro = true` RO). -/
public theorem vmPreserved_of_hookExactMemcpy_sep {f : State → State}
    (hf : HookExactMemcpy f)
    {ro : Bool} {dst src : BitVec 64} {bs : List (BitVec 8)} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = bs.length)
    (hmem : s0.mem ⊨ (memRegion dst bs.length ∗ memcpySrc ro src bs) ∗ R) :
    VmPreserved s0 (f s0) := by
  have hp_master : s0.mem ⊨ (withVmPreserved masterMemcpySpec).pre (ro, dst, src, bs) s0 ∗ R := by
    dsimp only [withVmPreserved, masterMemcpySpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by rwa [sepConj_assoc] at hmem⟩
  obtain ⟨_, _, hout_vm⟩ :=
    hookExactMemcpy_withVmPreserved_master_ok hf (ro, dst, src, bs) R s0 hrun hp_master hsp
  rcases hout_vm with ⟨_, _, hq⟩ | ⟨_, hp_sat⟩ | ⟨_, _, he_sat⟩ | ⟨_, ho_sat⟩
  · dsimp only [withVmPreserved] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.1
  · exact False.elim (not_satisfies_false_sepConj hp_sat)
  · exact False.elim (not_satisfies_false_sepConj he_sat)
  · exact False.elim (not_satisfies_false_sepConj ho_sat)

/-- Generic `VmPreserved`-strengthened (`withVmPreserved`-shape) upgrade for any `memcpy` spec
`target` from `HookOk f target` and a precondition-conditioned `VmPreserved` witness (e.g. via
`vmPreserved_of_hookExactMemcpy_sep`). -/
public theorem hookOk_withVmPreserved_of_witness {β : Type} {f : State → State}
    {target : Spec β}
    (hbase : HookOk f target)
    (hwit : ∀ y R s0, s0.status = .Running → s0.spAligned = true →
      s0.mem ⊨ target.pre y s0 ∗ R → VmPreserved s0 (f s0)) :
    HookOk f { target with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ target.post x s0 sf } := by
  intro y R s0 hrun hp hsp
  have hvm : VmPreserved s0 (f s0) := hwit y R s0 hrun hsp hp
  rcases hbase y R s0 hrun hp hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost⟩
  · exact Or.inr hrest

private theorem hookOk_withVmPreserved_of_exact_lift {β : Type} {f : State → State}
    {target : Spec β}
    (hf : HookExactMemcpy f)
    (hbase : HookOk f target)
    (g : β → Bool × BitVec 64 × BitVec 64 × List (BitVec 8))
    (F : β → State → SepProp)
    (hpre : ∀ y s0, target.pre y s0 ⊢ masterMemcpySpec.pre (g y) s0 ∗ F y s0) :
    HookOk f (withVmPreserved target) := by
  intro y R s0 hrun hp hsp
  have hp_master : s0.mem ⊨ (withVmPreserved masterMemcpySpec).pre (g y) s0 ∗ (F y s0 ∗ R) := by
    dsimp only [withVmPreserved]
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  obtain ⟨_, _, hout_vm⟩ :=
    hookExactMemcpy_withVmPreserved_master_ok hf (g y) (F y s0 ∗ R) s0 hrun hp_master hsp
  have hvm : VmPreserved s0 (f s0) := by
    rcases hout_vm with ⟨_, _, hq⟩ | ⟨_, hp_sat⟩ | ⟨_, _, he_sat⟩ | ⟨_, ho_sat⟩
    · dsimp only [withVmPreserved] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.1
    · exact False.elim (not_satisfies_false_sepConj hp_sat)
    · exact False.elim (not_satisfies_false_sepConj he_sat)
    · exact False.elim (not_satisfies_false_sepConj ho_sat)
  rcases hbase y R s0 hrun hp hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost⟩
  · exact Or.inr hrest

/-- Any `HookExactMemcpy f` satisfies `sessionMemcpyRegionBudgetSpec`
(`= withVmPreserved sessionMemcpyRegionSpec`). -/
public theorem hookExactMemcpy_sessionMemcpyRegionBudget_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f sessionMemcpyRegionBudgetSpec := by
  change HookOk f (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec)
  refine hookOk_withVmPreserved_of_exact_lift hf
    (hookOk_sessionMemcpyRegion_of_master (hookExactMemcpy_masterMemcpy_ok hf))
    (fun ⟨d, s, b⟩ => (false, d, s, b)) (fun _ _ => emp)
    (fun ⟨_, _, _⟩ _ => ?_)
  dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
    memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
  exact Entails.of_eq (sepConj_emp _).symm

/-- Lift `HookSatExactMemcpy H name` to `HookSat H name sessionMemcpyRegionBudgetSpec`. -/
public theorem hookSat_sessionMemcpyRegionBudget_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) :
    HookSat H name sessionMemcpyRegionBudgetSpec := by
  obtain ⟨f, hfH, hfEx⟩ := h
  exact ⟨f, hfH, hookExactMemcpy_sessionMemcpyRegionBudget_ok hfEx⟩

/-- Any `HookExactMemcpy f` satisfies `sessionMemcpyBudgetSpec stk`
(`= withVmPreserved (sessionMemcpySpec stk)`). -/
public theorem hookExactMemcpy_sessionMemcpyBudget_ok {f : State → State}
    (hf : HookExactMemcpy f) (stk : Nat := 4096) :
    HookOk f (sessionMemcpyBudgetSpec stk) := by
  change HookOk f
    (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec stk))
  refine hookOk_withVmPreserved_of_exact_lift hf
    (hookOk_sessionMemcpy_of_master (hookExactMemcpy_masterMemcpy_ok hf) stk)
    (fun ⟨d, s, b⟩ => (false, d, s, b)) (fun _ s0 => stackAt s0.sp stk)
    (fun ⟨_, _, _⟩ _ => ?_)
  dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
    libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
  exact Entails.of_eq (by simp only [sepConj_assoc])

/-- Lift `HookSatExactMemcpy H name` to `HookSat H name (sessionMemcpyBudgetSpec stk)`. -/
public theorem hookSat_sessionMemcpyBudget_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) (stk : Nat := 4096) :
    HookSat H name (sessionMemcpyBudgetSpec stk) := by
  obtain ⟨f, hfH, hfEx⟩ := h
  exact ⟨f, hfH, hookExactMemcpy_sessionMemcpyBudget_ok hfEx stk⟩

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
