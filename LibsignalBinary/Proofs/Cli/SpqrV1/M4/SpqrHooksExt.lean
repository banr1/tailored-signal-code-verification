/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# SPQR V1 4 KB-Stack Allocator, `SpqrHooks`, and `allocZeroed` Bridges

Lifts `CliExternsOk P A ext` onto `cliExternsWith ext` (and any `ext'` satisfying
`AgreeOnCliHooks ext ext'`) to establish `AllocContracts4K`, `SpqrHooks`, and
`rustAllocZeroedSpec A`.
-/

namespace CryptoVerification.Cli.SpqrV1.M4

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyROSpec4K libcMemcpyRO_of_sessionMemcpyRO4K)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem hookOk_stack_mono_local {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (withStack base s1).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem sessionMemcpyRO4K_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpyROSpec) (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemcpyROSpec4K stk) := by
  have h1 : HookOk f (withStack sessionMemcpyROSpec4K CliExt.memHookStack) := by
    intro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
    have hpre' : s0.mem ⊨ CliExt.memcpyROSpec.pre (dst, src, bs) s0 ∗ R := by
      dsimp only [withStack, sessionMemcpyROSpec4K, CliExt.memcpyROSpec, CliExt.withStack] at hpre ⊢
      simpa only [sepConj_assoc, satisfies_pure_sepConj] using hpre
    obtain ⟨hkf, hsym, hout⟩ := hh (dst, src, bs) R s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | hp | he | ho
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withStack, sessionMemcpyROSpec4K, CliExt.memcpyROSpec, CliExt.withStack] at hpost ⊢
      simpa only [sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr ho))
  exact hookOk_stack_mono_local h1 hle hmax

private theorem stub_sessionMemcpyRO4K_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (b : BitVec 64)
    (stk : Nat) (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt b ext')
      ((tripleRatchetProgAtExt b ext').fnAddr memcpyName)
      (withStack sessionMemcpyROSpec4K stk) := by
  obtain ⟨f, hf, hok⟩ := hAg.hookSat (by decide) hOk.memcpyRO
  have hsat : HookSat ext' memcpyName (withStack sessionMemcpyROSpec4K stk) :=
    ⟨f, hf, sessionMemcpyRO4K_of_cliExt hok hle hmax⟩
  have h := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext')
    (name := memcpyName) (hname := memcpyName) (stub := libsignalSessionCode.fnOff memcpyName)
    (k := 0) rfl (Nat.add_zero _) (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hsat
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

private theorem memsetRegion_of_libcMemset {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (libcMemsetSpec stk)) :
    subroutine_ok prog addr (withStack memsetRegionSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  refine ⟨(ptr, c, len), R, ?_, ?_⟩
  · dsimp only [libcMemsetSpec, withStack, memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  · intro sf hpost
    dsimp only [libcMemsetSpec, withStack, memsetRegionSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

private theorem sessionMemsetRegion_of_sessionMemset {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (sessionMemsetSpec stk)) :
    subroutine_ok prog addr (withStack sessionMemsetRegionSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  refine ⟨(ptr, c, len), R, ?_, ?_⟩
  · dsimp only [sessionMemsetSpec, libcMemsetSpec, withStack, sessionMemsetRegionSpec,
      memsetRegionSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
  · intro sf hpost
    dsimp only [sessionMemsetSpec, withStack, sessionMemsetRegionSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

/-- Lift `CliExternsOk P A ext` onto any `ext'` with `AgreeOnCliHooks ext ext'` to obtain
`CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext'`. -/
theorem spqrAllocContracts4K_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (b : BitVec 64) :
    CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext' :=
  let hBase := CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K.of_externsOk_on hOk hAg b
  { alloc := hBase.alloc
    dealloc := hBase.dealloc
    realloc := hBase.realloc
    shim := hBase.shim
    memcpy := hBase.memcpy
    session_memcpy := hBase.session_memcpy
    memcpy_ro := fun stk hlo hhi =>
      libcMemcpyRO_of_sessionMemcpyRO4K (stub_sessionMemcpyRO4K_on hOk hAg b stk hlo hhi)
    session_memcpy_region_ro := fun stk hlo hhi =>
      stub_sessionMemcpyRO4K_on hOk hAg b stk hlo hhi
    memcpy_region := hBase.memcpy_region
    session_memcpy_region := hBase.session_memcpy_region
    memmove := hBase.memmove
    session_memmove := hBase.session_memmove
    memset := hBase.memset
    session_memset := hBase.session_memset
    memset_region := fun stk hlo hhi => memsetRegion_of_libcMemset (hBase.memset stk hlo hhi)
    session_memset_region := fun stk hlo hhi =>
      sessionMemsetRegion_of_sessionMemset (hBase.session_memset stk hlo hhi) }

/-- `CryptoVerification.SpqrV1.Alloc.AllocContracts4K` on `cliExternsWith ext` from `CliExternsOk`. -/
theorem spqrAllocContracts4K_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A (cliExternsWith ext) :=
  spqrAllocContracts4K_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) b

/-- Transport `hOk.spqr : SpqrHooks P.C A P.Q.K ext` across `AgreeOnCliHooks ext ext'`. -/
theorem spqrHooks_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    CryptoVerification.LibsignalSpqrV1.SpqrHooks P.C A P.Q.K ext' where
  fromSeed := hAg.hookSat (by decide) hOk.spqr.fromSeed
  pk1 := hAg.hookSat (by decide) hOk.spqr.pk1
  pk2 := hAg.hookSat (by decide) hOk.spqr.pk2
  encaps1 := hAg.hookSat (by decide) hOk.spqr.encaps1
  encaps2 := hAg.hookSat (by decide) hOk.spqr.encaps2
  decaps := hAg.hookSat (by decide) hOk.spqr.decaps
  validatePk := hAg.hookSat (by decide) hOk.spqr.validatePk
  hmac := hAg.hookSat (by decide) hOk.spqr.hmac

/-- `SpqrHooks P.C A P.Q.K (cliExternsWith ext)` from `CliExternsOk P A ext`. -/
theorem spqrHooks_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.LibsignalSpqrV1.SpqrHooks P.C A P.Q.K (cliExternsWith ext) :=
  spqrHooks_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext)

/-- `rustAllocZeroedSpec A` at call offset `k` from `name` on `tripleRatchetProgAtExt b ext'`
under `AgreeOnCliHooks ext ext'`. -/
theorem allocZeroed_ok_at_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (b : BitVec 64)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext')
      ((tripleRatchetProgAtExt b ext').fnAddr name + BitVec.ofNat 64 k)
      (rustAllocZeroedSpec A) :=
  hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext')
    (name := name) (hname := allocZeroedName) (stub := libsignalSessionCode.fnOff allocZeroedName)
    (k := k) rfl hk (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol, allocZeroedName]) (hAg.hookSat (by decide) hOk.allocZeroed)

/-- `rustAllocZeroedSpec A` at call offset `k` from `name` on
`tripleRatchetProgAtExt b (cliExternsWith ext)` from `CliExternsOk P A ext`. -/
theorem allocZeroed_ok_at_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (b : BitVec 64) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr name + BitVec.ofNat 64 k)
      (rustAllocZeroedSpec A) :=
  allocZeroed_ok_at_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) b name k hk

end CryptoVerification.Cli.SpqrV1.M4
