/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeAlloc
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeRealloc
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeHooks

/-!
# `Mallocng` to `RustStdAlloc` Bridge

Re-exports `MallocngInst`, `MallocngBridgeCommon`, `MallocngBridgeAlloc`, `MallocngBridgeRealloc`,
and `MallocngBridgeHooks`, and assembles `RustStdAllocEntries` bundles across `__rdl_*` shims,
`__rust_*` thunks, and `WordTree` validators.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `RustStdAllocEntries` over `MallocngProgCContractsWith` -/

theorem mallocngRustCliEntriesWithOf_of_rdlShims_ok
    {J : MallocngIface} (hIf : MallocngIfaceFacts J) (extra : SepProp) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr)
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocWithOf J hIf extra γ mAddrs) P rdlAddrs where
  alloc := rdlAlloc_placed_withExtra_ok hIf extra γ rdlAddrs.alloc hShims.alloc_instrs hC
  dealloc := rdlDealloc_placed_withExtra_ok hIf extra γ rdlAddrs.dealloc hShims.dealloc_instrs hC
  realloc :=
    rdlRealloc_placed_withExtra_ok hIf extra γ rdlAddrs.realloc memcpyAddr
      hShims.realloc_instrs hC hMemcpy

theorem mallocngRustCliEntriesWithOf_of_thunks_ok
    {J : MallocngIface} (hIf : MallocngIfaceFacts J) (extra : SepProp) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs rdlAddrs)
    (hShims : RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr)
    (hC : MallocngProgCContractsWith J extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocWithOf J hIf extra γ mAddrs) P thunkAddrs where
  alloc :=
    rdlAlloc_thunk_withExtra_ok hIf extra γ thunkAddrs.alloc rdlAddrs.alloc
      hThunks.alloc_thunk hShims.alloc_instrs hC
  dealloc :=
    rdlDealloc_thunk_withExtra_ok hIf extra γ thunkAddrs.dealloc rdlAddrs.dealloc
      hThunks.dealloc_thunk hShims.dealloc_instrs hC
  realloc :=
    rdlRealloc_thunk_withExtra_ok hIf extra γ thunkAddrs.realloc rdlAddrs.realloc memcpyAddr
      hThunks.realloc_thunk hShims.realloc_instrs hC hMemcpy

theorem mallocngRustCliEntriesWith_of_rdlShims_ok
    (extra : SepProp) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr)
    (hC : MallocngProgCContractsWith mallocngIface extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocWith extra γ mAddrs) P rdlAddrs :=
  mallocngRustCliEntriesWithOf_of_rdlShims_ok mallocngRustCliIfaceFacts extra γ hShims hC hMemcpy

theorem mallocngRustCliEntriesWith_of_thunks_ok
    (extra : SepProp) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs rdlAddrs)
    (hShims : RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr)
    (hC : MallocngProgCContractsWith mallocngIface extra P mAddrs cAddrs)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocWith extra γ mAddrs) P thunkAddrs :=
  mallocngRustCliEntriesWithOf_of_thunks_ok
    mallocngRustCliIfaceFacts extra γ hThunks hShims hC hMemcpy

/-! ## Placed `RustStdAllocEntries` from `MallocngPlacedEntryContracts` -/

theorem mallocngRustCliEntriesOf_placed_ok
    {J : MallocngIface} (hIf : MallocngIfaceFacts J) (γ : GhostName)
    {P : Program} {mpl : Obj.MultiPlacement}
    {rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard)
    (hShims : RustStdRdlShimCode P rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ (mallocngAddrsOfPlacement mpl)) P rdlAddrs :=
  rustStdAllocEntries_of_with_emp
    (mallocngRustCliEntriesWithOf_of_rdlShims_ok hIf emp γ hShims
      (MallocngProgCContractsWith.of_placed emp hCont hEntries) hMemcpy)

theorem mallocngRustCliEntriesOf_placed_thunks_ok
    {J : MallocngIface} (hIf : MallocngIfaceFacts J) (γ : GhostName)
    {P : Program} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard)
    (hThunks : RustStdThunkCode P thunkAddrs rdlAddrs)
    (hShims : RustStdRdlShimCode P rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ (mallocngAddrsOfPlacement mpl)) P thunkAddrs :=
  rustStdAllocEntries_of_with_emp
    (mallocngRustCliEntriesWithOf_of_thunks_ok hIf emp γ hThunks hShims
      (MallocngProgCContractsWith.of_placed emp hCont hEntries) hMemcpy)

theorem mallocngRustCliEntries_placed_ok
    (γ : GhostName) {P : Program} {mpl : Obj.MultiPlacement}
    {rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts mallocngIface mpl Syscall.standard)
    (hShims : RustStdRdlShimCode P rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAlloc γ (mallocngAddrsOfPlacement mpl)) P rdlAddrs :=
  mallocngRustCliEntriesOf_placed_ok mallocngRustCliIfaceFacts γ hCont hEntries hShims hMemcpy

theorem mallocngRustCliEntries_placed_thunks_ok
    (γ : GhostName) {P : Program} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts mallocngIface mpl Syscall.standard)
    (hThunks : RustStdThunkCode P thunkAddrs rdlAddrs)
    (hShims : RustStdRdlShimCode P rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpySpec) :
    RustStdAllocEntries (mallocngRustCliAlloc γ (mallocngAddrsOfPlacement mpl)) P thunkAddrs :=
  mallocngRustCliEntriesOf_placed_thunks_ok
    mallocngRustCliIfaceFacts γ hCont hEntries hThunks hShims hMemcpy

/-! ## `WordTree` Placed ELF Wrappers -/

theorem mallocngRustCliEntries_placed_wordTree_ok
    (γ : GhostName) {P : Program} {t : WordTree} {mpl : Obj.MultiPlacement}
    {rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64} {memcpyOff : Nat}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts mallocngIface mpl Syscall.standard)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hnoext : ∀ pc, P.externAt? pc = none)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hShimsOk : checkRustStdRdlShimCode P.base t rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr = true)
    (hMcOff : (memcpyAddr - P.base).toNat = memcpyOff)
    (hMcBnd : memcpyOff + 4 * memcpySymWords.length ≤ 2 ^ 64)
    (hMcOk : checkWordsAt t memcpyOff memcpySymWords = true) :
    RustStdAllocEntries (mallocngRustCliAlloc γ (mallocngAddrsOfPlacement mpl)) P rdlAddrs :=
  mallocngRustCliEntries_placed_ok γ hCont hEntries
    (rustStdRdlShimCode_of_wordTree n hcode hwf hext hovr hShimsOk)
    (allocMemcpy_ok_of_wordTree n hcode hwf hnoext hMcOff hMcBnd hstubs hsyms hMcOk)

theorem mallocngRustCliEntries_placed_thunks_wordTree_ok
    (γ : GhostName) {P : Program} {t : WordTree} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64} {memcpyOff : Nat}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hCont : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts mallocngIface mpl Syscall.standard)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hnoext : ∀ pc, P.externAt? pc = none)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hThunksOk : checkRustStdThunkCode P.base t thunkAddrs rdlAddrs = true)
    (hShimsOk : checkRustStdRdlShimCode P.base t rdlAddrs (mallocngPlacedCAddrs mpl) memcpyAddr = true)
    (hMcOff : (memcpyAddr - P.base).toNat = memcpyOff)
    (hMcBnd : memcpyOff + 4 * memcpySymWords.length ≤ 2 ^ 64)
    (hMcOk : checkWordsAt t memcpyOff memcpySymWords = true) :
    RustStdAllocEntries (mallocngRustCliAlloc γ (mallocngAddrsOfPlacement mpl)) P thunkAddrs :=
  mallocngRustCliEntries_placed_thunks_ok γ hCont hEntries
    (rustStdThunkCode_of_wordTree n hcode hwf hext hovr hThunksOk)
    (rustStdRdlShimCode_of_wordTree n hcode hwf hext hovr hShimsOk)
    (allocMemcpy_ok_of_wordTree n hcode hwf hnoext hMcOff hMcBnd hstubs hsyms hMcOk)

end VerifiedLibraries.RustStd
