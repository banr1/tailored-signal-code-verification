/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.TripleRatchet.Hooks

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Placed Allocator Contracts from `CliExternsOk`

Derives `AllocContractsFsPlaced` and `AllocContractsXCliPlaced` from `CliExternsOk`.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops
open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Main.Placed

private theorem hookOk_conseq {α β : Type} {f : State → State} {spec₁ : Spec α} {spec₂ : Spec β}
    (hh : HookOk f spec₁)
    (hstep : ∀ (x : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec₂.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp), (s0.mem ⊨ spec₁.pre y s0 ∗ (F ∗ R)) ∧
        ∀ sf, (sf.mem ⊨ spec₁.post y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hpan₁ : ∀ y s0 sf, spec₁.onPanic y s0 sf = ⌜False⌝ := by intros; rfl)
    (hex₁ : ∀ y code s0 sf, spec₁.onExit y code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom₁ : ∀ y s0 sf, spec₁.onOom y s0 sf = ⌜False⌝ := by intros; rfl) : HookOk f spec₂ := by
  intro x R s0 hrun hpre hsp
  obtain ⟨y, F, hpre₁, hpost₁⟩ := hstep x R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hh y (F ∗ R) s0 hrun hpre₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost₁ (f s0) hpost⟩
  · rw [hpan₁ y s0 (f s0), satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · rw [hex₁ y code s0 (f s0), satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · rw [hoom₁ y s0 (f s0), satisfies_pure_sepConj] at hoom; exact False.elim hoom.1
private theorem stackAt_split_ge {sp : BitVec 64} {inner stk : Nat} (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega); rwa [Nat.add_sub_of_le hle] at h1
private theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) : CliExt.memHookStack ≤ stk :=
  Nat.le_trans (by decide : CliExt.memHookStack ≤ extHookStack) hle

private theorem hookOk_shim_of_cliExt {f : State → State} (hh : HookOk f CliExt.shimSpec) :
    HookOk f sessionShimSpec :=
  hookOk_conseq hh fun u R s0 hpre => ⟨u, emp,
    by simpa [CliExt.shimSpec, sessionShimSpec, emp_sepConj] using hpre,
    fun sf hpost => by simpa [CliExt.shimSpec, sessionShimSpec, emp_sepConj] using hpost⟩
private theorem hookOk_sessionMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack),
    by dsimp only [sessionMemcpySpec, CliExt.memcpySpec, libcMemcpySpec] at hpre ⊢; rw [hsp] at hpre; ac_nf at hpre ⊢,
    fun sf hpost => by dsimp only [sessionMemcpySpec, CliExt.memcpySpec] at hpost ⊢; rw [hsp]; ac_nf at hpost ⊢⟩
private theorem hookOk_libcMemcpy_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemcpySpec stk) :=
  hookOk_conseq (hookOk_sessionMemcpy_of_cliExt hh stk hle hmax) fun x R s0 hpre => ⟨x, emp,
    by simpa [sessionMemcpySpec, libcMemcpySpec, emp_sepConj] using hpre, fun sf hpost => by
      dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢; exact ⟨hpost.1.1, hpost.2⟩⟩
private theorem hookOk_sessionMemcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_conseq (hookOk_sessionMemcpy_of_cliExt hh stk hle hmax) fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), emp,
    by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec, libcMemcpySpec] at hpre ⊢
       simp only [emp_sepConj]; ac_nf at hpre ⊢, fun sf hpost => by
      dsimp only [withStack, sessionMemcpyRegionSpec, sessionMemcpySpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, by have h2 := hpost.2; ac_nf at h2 ⊢⟩⟩
private theorem hookOk_memcpyRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpySpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack memcpyRegionSpec stk) :=
  hookOk_conseq (hookOk_sessionMemcpyRegion_of_cliExt hh stk hle hmax) fun x R s0 hpre => ⟨x, emp,
    by simpa [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, emp_sepConj] using hpre, fun sf hpost => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢; exact ⟨hpost.1.1, hpost.2⟩⟩
private theorem hookOk_sessionMemcpyRegionRO_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memcpyROSpec) (stk : Nat) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk) := by
  refine hookOk_conseq hh fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) hle hmax
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack),
    by dsimp only [withStack, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec, CliExt.memcpyROSpec, CliExt.withStack] at hpre ⊢
       rw [hsp] at hpre; ac_nf at hpre ⊢, fun sf hpost => by
      dsimp only [withStack, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec, CliExt.memcpyROSpec, CliExt.withStack] at hpost ⊢
      rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, by have h2 := hpost.2; ac_nf at h2 ⊢⟩⟩
private theorem hookOk_sessionMemmove_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memmoveSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveSpec stk) := by
  refine hookOk_conseq hh fun ⟨base, buf, dst, src, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(base, buf, dst, src, len), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack),
    by dsimp only [sessionMemmoveSpec, CliExt.memmoveSpec, libcMemmoveSpec] at hpre ⊢; rw [hsp] at hpre; ac_nf at hpre ⊢,
    fun sf hpost => by dsimp only [sessionMemmoveSpec, CliExt.memmoveSpec] at hpost ⊢; rw [hsp]; ac_nf at hpost ⊢⟩
private theorem hookOk_libcMemmove_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memmoveSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemmoveSpec stk) :=
  hookOk_conseq (hookOk_sessionMemmove_of_cliExt hh stk hle hmax) fun x R s0 hpre => ⟨x, emp,
    by simpa [sessionMemmoveSpec, libcMemmoveSpec, emp_sepConj] using hpre, fun sf hpost => by
      dsimp only [sessionMemmoveSpec, libcMemmoveSpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢; exact ⟨hpost.1.1, hpost.2⟩⟩
private theorem hookOk_sessionMemset_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  refine hookOk_conseq hh fun ⟨ptr, c, len⟩ R s0 hpre => ?_
  have hsp := stackAt_split_ge (sp := s0.sp) (memHookStack_le_of_ext hle) hmax
  refine ⟨(ptr, c, len), memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - CliExt.memHookStack),
    by dsimp only [sessionMemsetSpec, CliExt.memsetSpec, libcMemsetSpec] at hpre ⊢; rw [hsp] at hpre
       simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
       exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2⟩, by have h2 := hpre.2; ac_nf at h2 ⊢⟩,
    fun sf hpost => by dsimp only [sessionMemsetSpec, CliExt.memsetSpec] at hpost ⊢; rw [hsp]; ac_nf at hpost ⊢⟩
private theorem hookOk_libcMemset_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (libcMemsetSpec stk) :=
  hookOk_conseq (hookOk_sessionMemset_of_cliExt hh stk hle hmax) fun x R s0 hpre => ⟨x, emp,
    by simpa [sessionMemsetSpec, libcMemsetSpec, emp_sepConj] using hpre, fun sf hpost => by
      dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢; exact ⟨hpost.1.1, hpost.2⟩⟩
private theorem hookOk_sessionMemsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack sessionMemsetRegionSpec stk) :=
  hookOk_conseq (hookOk_sessionMemset_of_cliExt hh stk hle hmax) fun ⟨ptr, c, len⟩ R s0 hpre => ⟨(ptr, c, len), emp,
    by dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec, sessionMemsetSpec, libcMemsetSpec] at hpre ⊢
       simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
       exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, by have h2 := hpre.2; ac_nf at h2 ⊢⟩, fun sf hpost => by
      dsimp only [withStack, sessionMemsetRegionSpec, sessionMemsetSpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, by have h2 := hpost.2; ac_nf at h2 ⊢⟩⟩
private theorem hookOk_memsetRegion_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.memsetSpec) (stk : Nat) (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (withStack memsetRegionSpec stk) :=
  hookOk_conseq (hookOk_sessionMemsetRegion_of_cliExt hh stk hle hmax) fun x R s0 hpre => ⟨x, emp,
    by simpa [withStack, sessionMemsetRegionSpec, memsetRegionSpec, emp_sepConj] using hpre, fun sf hpost => by
      dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec] at hpost ⊢
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢; exact ⟨hpost.1.1, hpost.2⟩⟩

structure ExtAllocLookup (ext : String → Option (State → State)) (H : LibsignalHooks) : Prop where
  alloc : H lsRustAllocSymCli = ext allocName
  dealloc : H lsRustDeallocSymCli = ext deallocName
  realloc : H lsRustReallocSymCli = ext reallocName
  shim : H lsRustNoAllocShimSymCli = ext shimName
  memcpy : H "memcpy" = ext memcpyName
  memmove : H "memmove" = ext memmoveName
  memset : H "memset" = ext memsetName

private theorem ext_stub_fs_placed_ok [LibsignalPlacement] {α β : Type}
    {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)} {H : LibsignalHooks}
    {extSym stSym : String} {s₁ : Spec α} {s₂ : Spec β}
    (hOk : CliExternsOk P A ext) (hH : H extSym = ext stSym) (hsat : HookSat ext stSym s₁)
    (hnotIo : stSym ∉ CliExt.ioNames) (hmap : ∀ {f}, HookOk f s₁ → HookOk f s₂)
    (hmem : extSym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ extSym) (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl s₂.keepsFs) := by
  rcases hsat with ⟨f, hf, hh⟩
  exact LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨f, hH.trans hf, (hmap hh).keepsFs (hOk.fsKept stSym f hf hnotIo)⟩ hmem

private theorem notIo_of_ne {n : String}
    (h1 : n ≠ SignalSession.readFileName := by decide) (h2 : n ≠ writeFileName := by decide)
    (h3 : n ≠ readStdinName := by decide) (h4 : n ≠ writeStdoutName := by decide) : n ∉ CliExt.ioNames := by
  simp [CliExt.ioNames, h1, h2, h3, h4]

theorem allocContractsFsPlaced_of_lookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)} {H : LibsignalHooks}
    (hL : ExtAllocLookup ext H) (hOk : CliExternsOk P A ext) : AllocContractsFsPlaced A H where
  alloc := ext_stub_fs_placed_ok hOk hL.alloc hOk.alloc.alloc notIo_of_ne fun h =>
    hookOk_rustAllocWithStack (stk := extHookStack) h allocHookStack_le_extHookStack extHookStack_le
  dealloc := ext_stub_fs_placed_ok hOk hL.dealloc hOk.alloc.dealloc notIo_of_ne fun h =>
    hookOk_rustDeallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack extHookStack_le
  realloc := ext_stub_fs_placed_ok hOk hL.realloc hOk.alloc.realloc notIo_of_ne fun h =>
    hookOk_rustReallocExternWithStack (stk := extHookStack) h allocHookStack_le_extHookStack extHookStack_le
  shim stk _ _ := ext_stub_fs_placed_ok hOk hL.shim hOk.shim notIo_of_ne fun h => hookOk_withStack (hookOk_shim_of_cliExt h) stk
  memcpy stk hle hmax := ext_stub_fs_placed_ok hOk hL.memcpy hOk.memcpy notIo_of_ne fun h => hookOk_libcMemcpy_of_cliExt h stk hle hmax
  session_memcpy stk hle hmax := ext_stub_fs_placed_ok hOk hL.memcpy hOk.memcpy notIo_of_ne fun h => hookOk_sessionMemcpy_of_cliExt h stk hle hmax
  memcpy_region stk hle hmax := ext_stub_fs_placed_ok hOk hL.memcpy hOk.memcpy notIo_of_ne fun h => hookOk_memcpyRegion_of_cliExt h stk hle hmax
  session_memcpy_region stk hle hmax := ext_stub_fs_placed_ok hOk hL.memcpy hOk.memcpy notIo_of_ne fun h => hookOk_sessionMemcpyRegion_of_cliExt h stk hle hmax
  memmove stk hle hmax := ext_stub_fs_placed_ok hOk hL.memmove hOk.memmove notIo_of_ne fun h => hookOk_libcMemmove_of_cliExt h stk hle hmax
  session_memmove stk hle hmax := ext_stub_fs_placed_ok hOk hL.memmove hOk.memmove notIo_of_ne fun h => hookOk_sessionMemmove_of_cliExt h stk hle hmax
  memset stk hle hmax := ext_stub_fs_placed_ok hOk hL.memset hOk.memset notIo_of_ne fun h => hookOk_libcMemset_of_cliExt h stk hle hmax
  session_memset stk hle hmax := ext_stub_fs_placed_ok hOk hL.memset hOk.memset notIo_of_ne fun h => hookOk_sessionMemset_of_cliExt h stk hle hmax
  memset_region stk hle hmax := ext_stub_fs_placed_ok hOk hL.memset hOk.memset notIo_of_ne fun h => hookOk_memsetRegion_of_cliExt h stk hle hmax
  session_memset_region stk hle hmax := ext_stub_fs_placed_ok hOk hL.memset hOk.memset notIo_of_ne fun h => hookOk_sessionMemsetRegion_of_cliExt h stk hle hmax
  session_memcpy_region_ro stk hle hmax := ext_stub_fs_placed_ok hOk hL.memcpy hOk.memcpyRO notIo_of_ne fun h =>
    hookOk_sessionMemcpyRegionRO_of_cliExt h stk (memHookStack_le_of_ext hle) hmax

theorem allocContractsXCliPlaced_of_lookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)} {H : LibsignalHooks}
    (hL : ExtAllocLookup ext H) (hOk : CliExternsOk P A ext) : AllocContractsXCliPlaced A H :=
  (allocContractsFsPlaced_of_lookup hL hOk).toAllocContractsX

end CryptoVerification.SignalSession.Cli.MainHops
