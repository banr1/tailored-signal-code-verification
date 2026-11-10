/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShim
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# Shared CLI Store Callee Instantiations

Transfers the shared `IdentityFiles` and `SessionFiles` shim, poll, and future-drop contracts onto
`initProg img W` and `tripleRatchetProgAtExt img.base ext1` at residual stack
`stk - cliInitiateFrame`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Fixed-Table Store Callee Instantiations -/

theorem publicKeyEq_cli_ok (W : CliHooks) (b : BitVec 64) :
    Getters.PublicKeyEqOkExt b (cliExterns W) :=
  Glue.publicKeyEq_ok_ext b (by
    rw [withPanics_cliExterns]
    exact cliExterns_row W
      (List.mem_append_right _ (List.mem_of_getElem? (i := 20) rfl)))

abbrev cliAddrTextStk : Nat :=
  0x70 + max (max doReserveStackX extHookStack) (10 * 0x50 + doReserveStackX)

abbrev cliDirPutStk : Nat :=
  0x60 + max (0x40 + finishGrowStackX) extHookStack

abbrev cliDirPutStrStk : Nat :=
  0x50 + max (0x40 + finishGrowStackX) extHookStack

theorem dirGet_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img B.dirGetNeed) :=
  Get.dirGet_ok_of_deps himg (fun _ h => h.2) hh.alloc hh.memcpyRO hh.bcmp
    (RunSkeleton.path_ok himg hh (Nat.le_refl _)) hRead hh.fs (Nat.le_refl _)
    (RunSkeleton.base_aligned himg)

theorem addressText_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr addressTextName)
      (addrTextSpec A img cliAddrTextStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hRes := RunSkeleton.reserve_ok hh (Nat.le_refl doReserveStackX)
  let hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl (10 * 0x50 + doReserveStackX)) hb
  AddressText.addressText_ok_of_deps hh.alloc hRes hDec (Nat.le_refl _) hb

theorem dirPut_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr dirPutName)
      (dirPutSpec A img cliDirPutStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hGrow := GrowOne.growOneDir_ok_x hh.alloc (Nat.le_refl (0x40 + finishGrowStackX)) hb
  Put.dirPut_ok_of_deps hh.alloc hh.bcmp hGrow (Nat.le_refl _) hb

theorem dirPutStr_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr dirPutStrName)
      (dirPutStrSpec A img cliDirPutStrStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hGrow := GrowOne.growOneDir_ok_x hh.alloc (Nat.le_refl (0x40 + finishGrowStackX)) hb
  PutStr.dirPutStr_ok_of_deps hh.alloc hh.memcpyRO hh.bcmp hGrow (Nat.le_refl _) hb

theorem idTrustShim_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr idTrustShimName)
      (idTrustShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0x30 + extHookStack ≤ 516880 := by decide
  exact Store.IdTrustShim.idTrustShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem idTrustPoll_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr idTrustPollName)
      (idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hext : extHookStack ≤ 65536 := by decide
  exact Store.IdTrustPoll.idTrustPoll_ok_of_deps hh.alloc
    (dirGet_cli_ok W B himg hh hRead)
    (RunSkeleton.identityKeyDecode_ok himg)
    (publicKeyEq_cli_ok W img.base)
    (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessLoadShim_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr sessLoadShimName)
      (sessLoadShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0x20 + extHookStack ≤ 516880 := by decide
  exact Store.LoadShim.sessLoadShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessLoadPoll_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr sessLoadPollName)
      (sessLoadPollSpec cliIo.rd cliWrOk (fun _ => False) A img (stk - cliInitiateFrame)) :=
  Store.LoadPoll.sessLoadPoll_ok_of_deps hh.alloc
    (addressText_cli_ok W himg hh)
    (dirGet_cli_ok W B himg hh hRead)
    sessDeserialize_false_ok
    hh.fs
    (sessLoadPoll_stk_le (by decide) hstk)
    (RunSkeleton.base_aligned himg)

theorem idSaveShim_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr idSaveShimName)
      (idSaveShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0x30 + extHookStack ≤ 516880 := by decide
  exact Store.IdSaveShim.idSaveShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem idSavePoll_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hRead : subroutine_ok (initProg img W)
      ((initProg img W).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr idSavePollName)
      (idSavePollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hput : cliDirPutStrStk ≤ 65536 := by decide
  have hpks : publicKeySerializeStackX ≤ 65536 := by decide
  have hext : extHookStack ≤ 65536 := by decide
  exact Store.IdSavePoll.idSavePoll_ok_of_deps hh.alloc
    (dirGet_cli_ok W B himg hh hRead)
    (dirPutStr_cli_ok W himg hh)
    (RunSkeleton.identityKeyDecode_ok himg)
    (publicKeyEq_cli_ok W img.base)
    (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessStoreShim_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr sessStoreShimName)
      (sessStoreShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0x30 + extHookStack ≤ 516880 := by decide
  exact Store.StoreShim.sessStoreShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

/-! ## Contract-Parameterized Store Callee Instantiations -/

theorem publicKeyEq_ext_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    Getters.PublicKeyEqOkExt32 b (cliExternsWith ext) :=
  Glue.publicKeyEq_ok_ext32 b
    (RunGlue.hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
      hOk.blackBox)

theorem path_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr pathName)
      (pathSpec A img pathNeed) :=
  Path.path_ok_of_deps_withStack hh.alloc hh.memcpyRO
    (RunSkeleton.reserve_ok_ext hh (Nat.le_refl doReserveStackX))
    (Nat.le_refl _) (RunSkeleton.base_aligned himg) (by decide)

theorem dirGet_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img B.dirGetNeed) :=
  Get.dirGet_ok_of_deps_withStack himg (fun _ h => h.2) hh.alloc hh.memcpyRO hh.bcmp
    (path_ext_ok himg hh) hRead hh.fs (Nat.le_refl _)
    (RunSkeleton.base_aligned himg) (by decide)

theorem addressText_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr addressTextName)
      (addrTextSpec A img cliAddrTextStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hRes := RunSkeleton.reserve_ok_ext hh (Nat.le_refl doReserveStackX)
  let hDec := Decimal.decimal_ok_of_deps hRes (Nat.le_refl (10 * 0x50 + doReserveStackX)) hb
  AddressText.addressText_ok_of_deps hh.alloc hRes hDec (Nat.le_refl _) hb

theorem dirPut_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr dirPutName)
      (dirPutSpec A img cliDirPutStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hGrow := GrowOne.growOneDir_ok_x hh.alloc (Nat.le_refl (0x40 + finishGrowStackX)) hb
  Put.dirPut_ok_of_deps hh.alloc hh.bcmp hGrow (Nat.le_refl _) hb

theorem dirPutStr_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr dirPutStrName)
      (dirPutStrSpec A img cliDirPutStrStk) :=
  let hb := RunSkeleton.base_aligned himg
  let hGrow := GrowOne.growOneDir_ok_x hh.alloc (Nat.le_refl (0x40 + finishGrowStackX)) hb
  PutStr.dirPutStr_ok_of_deps_withStack hh.alloc hh.memcpyRO hh.bcmp hGrow (Nat.le_refl _) hb
    (by decide)

theorem idTrustShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idTrustShimName)
      (idTrustShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 48 + extHookStack ≤ 516880 := by decide
  exact Store.IdTrustShim.idTrustShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem idTrustPoll_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext1)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idTrustPollName)
      (idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hext : Getters.publicKeyEqStackExt ≤ 65536 := by decide
  exact Store.IdTrustPoll.idTrustPoll_ok_of_deps_ext32 hh.alloc
    (dirGet_ext_ok B himg hh hRead)
    (RunSkeleton.identityKeyDecode_ok himg)
    hEq
    (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessLoadShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr sessLoadShimName)
      (sessLoadShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 32 + extHookStack ≤ 516880 := by decide
  exact Store.LoadShim.sessLoadShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessLoadPoll_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr sessLoadPollName)
      (sessLoadPollSpec cliIo.rd cliWrOk (fun _ => False) A img (stk - cliInitiateFrame)) :=
  Store.LoadPoll.sessLoadPoll_ok_of_deps hh.alloc
    (addressText_ext_ok himg hh)
    (dirGet_ext_ok B himg hh hRead)
    sessDeserialize_false_ok
    hh.fs
    (sessLoadPoll_stk_le (by decide) hstk)
    (RunSkeleton.base_aligned himg)

theorem idSaveShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idSaveShimName)
      (idSaveShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 48 + extHookStack ≤ 516880 := by decide
  exact Store.IdSaveShim.idSaveShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

theorem idSavePoll_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext1)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idSavePollName)
      (idSavePollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hput : cliDirPutStrStk ≤ 65536 := by decide
  have hpks : publicKeySerializeStackX ≤ 65536 := by decide
  have hext : Getters.publicKeyEqStackExt ≤ 65536 := by decide
  exact Store.IdSavePoll.idSavePoll_ok_of_deps_ext32 hh.alloc
    (dirGet_ext_ok B himg hh hRead)
    (dirPutStr_ext_ok himg hh)
    (RunSkeleton.identityKeyDecode_ok himg)
    hEq
    (by omega)
    (RunSkeleton.base_aligned himg)

theorem sessStoreShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr sessStoreShimName)
      (sessStoreShimSpec A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 48 + extHookStack ≤ 516880 := by decide
  exact Store.StoreShim.sessStoreShim_ok_of_deps hh.alloc (by omega)
    (RunSkeleton.base_aligned himg)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
