/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `CalleesRO` (`from_utf8` & `memrchr` RO Discharges) (`CalleesROSat`)

Replaces both:
- `hext : H lsFromUtf8Sym = some (fromUtf8Hook err)` (dropping the unused `err` parameter) in
  `fromUtf8Ascii_ro_placed_ok_of_hooks` (`CalleesRO.lean:607`) and
  `mainCalleesROBlk617_of_mainCalleesBlk617_and_addr` (`CalleesRO.lean:653`) with
  `HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack))`, and
- `hext : H lsMemrchrSym = some memrchrHook` in `memrchr_ro_blk580_ok_of_hooks`
  (`CalleesRO.lean:628`) with `HookSat H lsMemrchrSym (withVmPreserved (memrchrSpecRO stk))`,
plus the exact-hook coercions `hookSat_fromUtf8ROVm_of_eq` and `hookSat_memrchrROVm_of_eq`.
`hstrlen : H "strlen" = some strlenHook` is kept exact pending `strlen` inventory.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (fromUtf8Hook lsFromUtf8Sym lsMemrchrSym memrchrHook strlenHook)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_580)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookSat_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 addressSpecRO fromUtf8AsciiSpecRO fromUtf8Hook_ro_ok
   fromUtf8Hook_vmPreserved memrchrHook_ro_ok memrchrHook_vmPreserved memrchrSpecRO
   strlen_ro_placed_ok_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)

private theorem subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain h)

/-- Coercion from `H lsFromUtf8Sym = some (fromUtf8Hook err)` to
    `HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack))`. -/
theorem hookSat_fromUtf8ROVm_of_eq {H : LibsignalHooks} (hookStack : Nat)
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hext : H lsFromUtf8Sym = some (fromUtf8Hook err)) :
    HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)) :=
  hookSat_withVmPreserved ⟨fromUtf8Hook err, hext, fromUtf8Hook_ro_ok hookStack err⟩
    (fun _ hf s => by
      cases hext.symm.trans hf
      exact fromUtf8Hook_vmPreserved err s)

/-- Coercion from `H lsMemrchrSym = some memrchrHook` to
    `HookSat H lsMemrchrSym (withVmPreserved (memrchrSpecRO stk))`. -/
theorem hookSat_memrchrROVm_of_eq {H : LibsignalHooks} (stk : Nat)
    (hext : H lsMemrchrSym = some memrchrHook) :
    HookSat H lsMemrchrSym (withVmPreserved (memrchrSpecRO stk)) :=
  hookSat_withVmPreserved ⟨memrchrHook, hext, memrchrHook_ro_ok stk⟩
    (fun _ hf s => by
      cases hext.symm.trans hf
      exact memrchrHook_vmPreserved s)

/-- Coercion from `H lsMemrchrSym = some memrchrHook` to
    `HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO stk)))`. -/
theorem hookSat_memrchrROVm_ls_of_eq [LibsignalPlacement] {H : LibsignalHooks} (stk : Nat)
    (hext : H lsMemrchrSym = some memrchrHook) :
    HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  hookSat_withLsRet (hookSat_memrchrROVm_of_eq stk hext)

/-- `HookSat` sibling of `fromUtf8Ascii_ro_placed_ok_of_hooks` (`CalleesRO.lean:607`), dropping
    the unused `err` parameter. -/
theorem fromUtf8Ascii_ro_placed_ok_of_hooks_sat [LibsignalPlacement]
    {H : LibsignalHooks} {hookStack : Nat}
    (hext : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) :
    subroutine_ok (lsProg_617 H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) :=
  subroutine_ok_rocl_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hext (by decide))

/-- `HookSat` sibling of `memrchr_ro_blk580_ok_of_hooks` (`CalleesRO.lean:628`). -/
theorem memrchr_ro_blk580_ok_of_hooks_sat [LibsignalPlacement]
    {H : LibsignalHooks} {stk : Nat}
    (hext : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO stk)))) :
    subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (withVmPreserved (memrchrSpecRO stk)))) := by
  have hplain : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRet (withVmPreserved (memrchrSpecRO stk))) := by
    dsimp only [lsProg_580]
    exact ls_hook_ok_ultra_of_mem hext (by decide)
  exact subroutine_ok_rocl_of_plain hplain

/-- `HookSat` sibling of `mainCalleesROBlk617_of_mainCalleesBlk617_and_addr` (`CalleesRO.lean:653`),
    replacing `hutf8` with `HookSat` and dropping `err`. -/
theorem mainCalleesROBlk617_of_mainCalleesBlk617_and_addr_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (haddr : subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidParse resStack))) :
    MainCalleesROBlk617 A lim H uuidParse hookStack resStack where
  alloc := hc.alloc
  allocFs := hc.allocFs
  strlen := strlen_ro_placed_ok_of_hooks hstrlen
  fromUtf8 := fromUtf8Ascii_ro_placed_ok_of_hooks_sat hutf8
  address := haddr
  reserve16 := hc.reserve16
  reserve1 := hc.reserve1
  tryAllocateIn3 := hc.tryAllocateIn3
  handleErrorPanic := hc.handleErrorPanic

end LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat
