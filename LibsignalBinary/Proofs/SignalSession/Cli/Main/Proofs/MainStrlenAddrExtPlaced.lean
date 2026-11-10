/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Placed `strlen`, `from_utf8`, and `address` Contracts from `CliExternsOk`

Derives placed `subroutine_ok` contracts on Block `617` for `strlen`, `core::str::converts::from_utf8`,
and `signal_session::address` (via `memrchr`) from `CliExternsOk`.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open Address.Helpers

private theorem stackAt_split_ext {sp : BitVec 64} {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

structure ExtStrlenAddrLookup (ext : String → Option (State → State)) (H : LibsignalHooks) : Prop where
  strlen : H "strlen" = ext "strlen"
  fromUtf8 : H lsFromUtf8Sym = ext "core::str::converts::from_utf8"
  memrchr : H lsMemrchrSym = ext "core::slice::memchr::memrchr"
  handleError : H lsHandleErrorSym580 = some Rust.panicked

theorem strlen_placed_ok_of_hookSat [LibsignalPlacement]
    {ext : String → Option (State → State)} {H : LibsignalHooks} {hookStack : Nat}
    (hH : H "strlen" = ext "strlen") (hsat : HookSat ext "strlen" CliExt.strlenSpec)
    (hle : extHookStack ≤ hookStack := by decide) (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ "strlen") (withLsRoCl lsmpl (strlenSpec hookStack)) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (strlenSpec hookStack) := by
    intro ⟨p, s⟩ R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext (sp := s0.sp) hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.strlenSpec.pre (p, s) s0 ∗ R' := by
      dsimp only [strlenSpec, CliExt.strlenSpec, CliExt.cStrAt, Cli.cStrAt, R'] at hpre ⊢
      rw [hsplit] at hpre; ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh (p, s) R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [strlenSpec, CliExt.strlenSpec, CliExt.cStrAt, Cli.cStrAt, R'] at hpost ⊢
      rw [hsplit]; ac_nf at hpost ⊢
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  exact subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨f, hH.trans hf, hh'⟩ (by decide)

theorem fromUtf8Ascii_placed_ok_of_hookSat [LibsignalPlacement]
    {ext : String → Option (State → State)} {H : LibsignalHooks} {hookStack : Nat}
    (hH : H lsFromUtf8Sym = ext "core::str::converts::from_utf8")
    (hsat : HookSat ext "core::str::converts::from_utf8" CliExt.fromUtf8Spec)
    (hle : extHookStack ≤ hookStack := by decide) (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym) (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (fromUtf8AsciiSpec hookStack) := by
    intro ⟨r, p, bs⟩ R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext (sp := s0.sp) hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.fromUtf8Spec.pre (r, p, bs) s0 ∗ R' := by
      dsimp only [fromUtf8AsciiSpec, CliExt.fromUtf8Spec, R'] at hpre ⊢
      rw [hsplit] at hpre; ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh (r, p, bs) R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [fromUtf8AsciiSpec, CliExt.fromUtf8Spec, R'] at hpost ⊢
      rw [hsplit]; ac_nf at hpost ⊢
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  exact subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨f, hH.trans hf, hh'⟩ (by decide)

theorem memrchr_blk580_ok_of_hookSat [LibsignalPlacement]
    {ext : String → Option (State → State)} {H : LibsignalHooks} {stk : Nat}
    (hH : H lsMemrchrSym = ext "core::slice::memchr::memrchr")
    (hsat : HookSat ext "core::slice::memchr::memrchr" CliExt.memrchrSpec)
    (hle : extHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym) (withLsRoCl lsmpl (memrchrSpec stk)) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (memrchrSpec stk) := by
    intro x R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext (sp := s0.sp) hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.memrchrSpec.pre ⟨x.c, x.p, x.bs⟩ s0 ∗ R' := by
      dsimp only [memrchrSpec, CliExt.memrchrSpec, R'] at hpre ⊢
      rw [hsplit] at hpre; ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.c, x.p, x.bs⟩ R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [memrchrSpec, CliExt.memrchrSpec, R'] at hpost ⊢
      rw [hsplit]; ac_nf at hpost ⊢
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.memrchrSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  exact subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_580 H) (i := 580) ⟨f, hH.trans hf, hh'⟩ (by decide)

theorem address_placed_ok_of_lookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {ext : String → Option (State → State)} {H : LibsignalHooks}
    {resStack : Nat} (hCF : AllocContractsFsPlaced A H)
    (hL : ExtStrlenAddrLookup ext H) (hOk : CliExternsOk P A ext)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_placed_ok hCF hL.handleError
    (memrchr_blk580_ok_of_hookSat hL.memrchr hOk.memrchr (by decide) (by decide)) hres hres64

end CryptoVerification.SignalSession.Cli.MainHops
