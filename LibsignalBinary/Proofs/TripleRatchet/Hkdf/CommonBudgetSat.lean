/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat

/-!
# Budget-Threaded `HookSat` HKDF Hook Bundle (`CommonBudgetSat`)

Provides `HkdfPlacedHooksBudgetSat` and its `HookSatExactMemcpy`-widened sibling
`HkdfPlacedHooksExactBudgetSat` — replacing `H lsMemsetSym = some memsetHook` with
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec` and `H lsMemcpySym = some memcpyHook`
with `HookSatExactMemcpy H lsMemcpySym` — together with forgetful instances and coercion
lemmas to `HkdfPlacedHooksExactSat` / `HkdfPlacedHooksSat`, from `HkdfPlacedHooks`, from
`HkdfPlacedHooksExactSat` + budget `memset`, and across point-wise hook table equalities.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalHooks)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks lsCompress256Sym lsMemcpySym lsMemsetSym)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (hookOk_sessionMemsetRegion_of_budget hookSat_hookMemset_budget_of_eq
   hookSat_memsetHook_budget_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy hookSatExactMemcpy_of_eq memcpyHook_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat HkdfPlacedHooksSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

/-- Budget-threaded `HookSat` sibling of `HkdfPlacedHooks`: replaces the extensional equality
`H lsMemsetSym = some memsetHook` with `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
public class HkdfPlacedHooksBudgetSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  memcpy : H lsMemcpySym = some memcpyHook
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- Forget `VmPreserved` on `memset` to obtain `HkdfPlacedHooksSat F H`. -/
public theorem HkdfPlacedHooksBudgetSat.toSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooksBudgetSat F H) : HkdfPlacedHooksSat F H :=
  HkdfPlacedHooksSat.of_budget hH.memset hH.memcpy hH.compress256

/-- Coerce `HkdfPlacedHooks F H` into `HkdfPlacedHooksBudgetSat F H` via
`hookSat_memsetHook_budget_of_eq` (plain theorem, never an `instance`). -/
public theorem HkdfPlacedHooks.toBudgetSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksBudgetSat F H where
  memset := hookSat_memsetHook_budget_of_eq hH.memset
  memcpy := hH.memcpy
  compress256 := hH.compress256

/-- Build `HkdfPlacedHooksBudgetSat F H` from `H lsMemsetSym = some memsetHook`. -/
public theorem HkdfPlacedHooksBudgetSat.of_memsetHook_eq {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksBudgetSat F H where
  memset := hookSat_memsetHook_budget_of_eq h_memset
  memcpy := h_memcpy
  compress256 := h_compress

/-- Build `HkdfPlacedHooksBudgetSat F H` from `H lsMemsetSym = some ProofLib.hookMemset`. -/
public theorem HkdfPlacedHooksBudgetSat.of_hookMemset_eq {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : H lsMemsetSym = some ProofLib.hookMemset)
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksBudgetSat F H where
  memset := hookSat_hookMemset_budget_of_eq h_memset
  memcpy := h_memcpy
  compress256 := h_compress

/-- Transport `HookSat` across pointwise equality at `sym`. -/
public theorem hookSat_of_sym_eq {α : Type} {H1 H2 : String → Option (State → State)}
    {sym : String} {spec : Spec α}
    (heq : H1 sym = H2 sym) (h : HookSat H2 sym spec) :
    HookSat H1 sym spec := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, heq.trans hf, hok⟩

/-- Transport `HkdfPlacedHooksBudgetSat` across pointwise equality on the 3 HKDF symbols. -/
public theorem HkdfPlacedHooksBudgetSat.of_hooks_eq {F : ShaCompress}
    {H1 H2 : LibsignalHooks} (hH : HkdfPlacedHooksBudgetSat F H2)
    (h_memset : H1 lsMemsetSym = H2 lsMemsetSym)
    (h_memcpy : H1 lsMemcpySym = H2 lsMemcpySym)
    (h_compress : H1 lsCompress256Sym = H2 lsCompress256Sym) :
    HkdfPlacedHooksBudgetSat F H1 where
  memset := hookSat_of_sym_eq h_memset hH.memset
  memcpy := h_memcpy.trans hH.memcpy
  compress256 := h_compress.trans hH.compress256

/-! ## `HookSatExactMemcpy`-Widened Budget HKDF Hook Bundle (`HkdfPlacedHooksExactBudgetSat`) -/

/-- Budget-threaded `HookSat` + `HookSatExactMemcpy` HKDF hook bundle: replaces
`H lsMemsetSym = some memsetHook` with `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`
and `H lsMemcpySym = some memcpyHook` with `HookSatExactMemcpy H lsMemcpySym`. -/
public class HkdfPlacedHooksExactBudgetSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  memcpy : HookSatExactMemcpy H lsMemcpySym
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- Every `HkdfPlacedHooksBudgetSat` is an `HkdfPlacedHooksExactBudgetSat` via
`memcpyHook_exact`. -/
public instance instHkdfPlacedHooksExactBudgetSatOfBudgetSat
    {F : ShaCompress} {H : LibsignalHooks} [hH : HkdfPlacedHooksBudgetSat F H] :
    HkdfPlacedHooksExactBudgetSat F H where
  memset := hH.memset
  memcpy := hookSatExactMemcpy_of_eq hH.memcpy memcpyHook_exact
  compress256 := hH.compress256

/-- Forget `VmPreserved` on `memset` to obtain `HkdfPlacedHooksExactSat F H`. -/
public theorem HkdfPlacedHooksExactBudgetSat.toExactSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooksExactBudgetSat F H) : HkdfPlacedHooksExactSat F H where
  memset := by
    rcases hH.memset with ⟨f, hf, hok⟩
    exact ⟨f, hf, hookOk_sessionMemsetRegion_of_budget hok⟩
  memcpy := hH.memcpy
  compress256 := hH.compress256

/-- Forgetful typeclass instance `HkdfPlacedHooksExactBudgetSat → HkdfPlacedHooksExactSat`. -/
public instance instHkdfPlacedHooksExactSatOfExactBudgetSat
    {F : ShaCompress} {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat F H] :
    HkdfPlacedHooksExactSat F H :=
  hH.toExactSat

/-- Combine budget `memset` (`sessionMemsetRegionBudgetSpec`, e.g. from `CliGhostAllocHooks`)
with `[HkdfPlacedHooksExactSat F H]` to construct `HkdfPlacedHooksExactBudgetSat F H`. -/
public theorem HkdfPlacedHooksExactBudgetSat.of_exactSat {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    [hEx : HkdfPlacedHooksExactSat F H] :
    HkdfPlacedHooksExactBudgetSat F H where
  memset := h_memset
  memcpy := hEx.memcpy
  compress256 := hEx.compress256

/-- Coerce `HkdfPlacedHooksBudgetSat F H` into `HkdfPlacedHooksExactBudgetSat F H`. -/
public theorem HkdfPlacedHooksBudgetSat.toExactBudgetSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooksBudgetSat F H) : HkdfPlacedHooksExactBudgetSat F H :=
  @instHkdfPlacedHooksExactBudgetSatOfBudgetSat F H hH

/-- Coerce `HkdfPlacedHooks F H` into `HkdfPlacedHooksExactBudgetSat F H`. -/
public theorem HkdfPlacedHooks.toExactBudgetSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksExactBudgetSat F H :=
  (HkdfPlacedHooks.toBudgetSat hH).toExactBudgetSat

/-- Transport `HookSatExactMemcpy` across pointwise equality at `sym`. -/
public theorem hookSatExactMemcpy_of_sym_eq {H1 H2 : String → Option (State → State)}
    {sym : String} (heq : H1 sym = H2 sym) (h : HookSatExactMemcpy H2 sym) :
    HookSatExactMemcpy H1 sym := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, heq.trans hf, hex⟩

/-- Transport `HkdfPlacedHooksExactBudgetSat` across pointwise equality on the 3 HKDF symbols. -/
public theorem HkdfPlacedHooksExactBudgetSat.of_hooks_eq {F : ShaCompress}
    {H1 H2 : LibsignalHooks} (hH : HkdfPlacedHooksExactBudgetSat F H2)
    (h_memset : H1 lsMemsetSym = H2 lsMemsetSym)
    (h_memcpy : H1 lsMemcpySym = H2 lsMemcpySym)
    (h_compress : H1 lsCompress256Sym = H2 lsCompress256Sym) :
    HkdfPlacedHooksExactBudgetSat F H1 where
  memset := hookSat_of_sym_eq h_memset hH.memset
  memcpy := hookSatExactMemcpy_of_sym_eq h_memcpy hH.memcpy
  compress256 := h_compress.trans hH.compress256

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
