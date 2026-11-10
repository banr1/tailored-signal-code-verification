/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetFine

/-!
# `HookSat` Sibling of `SpecBudgetFine` §5 (`SpecBudgetFineSat`)

**Not trusted (`Role::Proof`).** Provides `FineCliB2ExternRowsSat` — carrying `HookSat` contracts
for `memset`, `memcpy`, and `memcpyRO` matching `FineCliB2ExternRows` (`SpecBudgetFine.lean:596`) —
together with `FineCliB2ExternRows.toSat`, `fineCliExternsBudgetAllocSlice_sat`, and
`fineCliExternsBudgetOk_of_b2_sat`.
-/

set_option autoImplicit false

public noncomputable section

namespace LibsignalBinary.Heap.Fine.SpecBudgetFineSat

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (
  aesDecHookMallocng aesEncHookMallocng
  compress512Name compressName dsmbName edNegName kemDecapsName kemEncapsName
  libcruxHmacHookMallocng scalarModName scalarWideName toEdwardsName torsionFreeName
)
open CryptoVerification.LibsignalPublicApi (
  durationSinceHookName stringCloneHookName timeAddHookName
)
open CryptoVerification.LibsignalSpqrV1 (
  libcruxHmacName mlkemDecapsName mlkemEncaps1Name mlkemEncaps2Name
  mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemValidatePkName
)
open CryptoVerification.LibsignalTripleRatchet (
  aesDecName aesEncName allocZeroedName dhName
  fmtWriteName formatInnerName pubFromSecretName sharedDropName staticDropName
)
open CryptoVerification.SignalSession (
  CliHooks cliBcmpHook durationSinceExactHook fromUtf8Hook memrchrHook
  readFileName readStdinName strlenHook writeFileHook writeFileName
  writeStdoutHook writeStdoutName
)
open CryptoVerification.SignalSession.CliExt (ioNames memcpyROSpec memcpySpec memsetSpec)
open LibsignalBinary.Heap (BudgetLimits VmPreserved)
open LibsignalBinary.Heap.Fine (
  FineCliB2ExternRows FineCliExternsAllocSlice SpqrHooksB2Residual
  cliBcmp_hookOk cliBlackBox_hookOk cliCompress256_hookOk cliCompress512_hookOk
  cliCompress_hookOk cliDh_hookOk cliDsmb_hookOk cliEdNeg_hookOk cliFromUtf8_hookOk
  cliKemDecaps_hookOk cliKemEncaps_hookOk
  cliMemmove_hookOk cliMemrchr_hookOk cliPubFromSecret_hookOk
  cliScalarMod_hookOk cliScalarWide_hookOk cliShim_hookOk cliStrlen_hookOk
  cliToEdwards_hookOk cliTorsionFree_hookOk cliWriteFile_hookOk cliWriteStdout_hookOk
  cliZeroize_hookOk durationSinceExactHook_epoch_budget_ok fineCostModel
  fineCliExternsBudgetOk_of_slice fineSpqrB2Hooks_of_b2 fmtWriteHook0_budget_ok
  formatInnerHook0_budget_ok hookSat_of_hookOk timeAddHook_budget_ok
)
open LibsignalBinary.Heap.SpecBudget (
  AllocHooksBudget CliExternsBudgetOk cliAllocNames hookSat_writeFileBudget_of_hookSat
  hookSat_writeStdoutBudget_of_hookSat readFileBudgetSpec readStdinBudgetSpec
  rustAllocZeroedBudgetSpec vmPreserved_writeFileHook vmPreserved_writeStdoutHook
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineAesDec_budget_hookSat fineAesEnc_budget_hookSat
  fineHookRustCliAllocBudget fineStringClone_budget_hookSat stringCloneHookMallocng
)

/-- `HookSat`-parameterized sibling of `FineCliB2ExternRows`: carries `HookSat` contracts for
`memset` (`memsetSpec`), `memcpy` (`memcpySpec`), and `memcpyRO` (`memcpyROSpec`). -/
structure FineCliB2ExternRowsSat [LibsignalPlacement] (mpl : Obj.MultiPlacement) (W : CliHooks)
    (ext : String → Option (State → State)) : Prop where
  shim : ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" = some hookNoop
  memset : HookSat ext "memset" memsetSpec
  memmove : ext "memmove" = some hookMemmove
  memcpy : HookSat ext "memcpy" memcpySpec
  memcpyRO : HookSat ext "memcpy" memcpyROSpec
  bcmp : ext "bcmp" = some (cliBcmpHook W.bcmp)
  strlen : ext "strlen" = some strlenHook
  writeFile : ext writeFileName = some writeFileHook
  writeStdout : ext writeStdoutName = some writeStdoutHook
  memrchr : ext "core::slice::memchr::memrchr" = some memrchrHook
  fromUtf8 : ext "core::str::converts::from_utf8" = some (fromUtf8Hook W.utf8Err)
  stringClone : ext stringCloneHookName = some (stringCloneHookMallocng mpl)
  fmtWrite : ext fmtWriteName = some CryptoVerification.E2E.fmtWriteHook0
  formatInner : ext formatInnerName = some CryptoVerification.E2E.formatInnerHook0
  durationSince : ext durationSinceHookName = some durationSinceExactHook
  timeAdd : ext timeAddHookName = some CryptoVerification.E2E.timeAddHook
  blackBox : ext "subtle::black_box::<u8>" = some CryptoVerification.LibsignalSession.blackBoxHook
  compress256 : ext "sha2::sha256::compress256" =
    some (CryptoVerification.LibsignalHmac.compress256Hook W.C.F)
  aesEnc : ext aesEncName = some (aesEncHookMallocng mpl W.C.E)
  aesDec : ext aesDecName = some (aesDecHookMallocng mpl W.C.D)
  pubFromSecret : ext pubFromSecretName =
    some (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey)
  dh : ext dhName = some (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook W.C.X)
  staticDrop : ext staticDropName = some CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook
  sharedDrop : ext sharedDropName = some CryptoVerification.LibsignalTripleRatchet.zeroizeSecretHook
  compress512 : ext compress512Name = some (CryptoVerification.E2E.compress512Hook W.Q.F512)
  toEdwards : ext toEdwardsName = some (CryptoVerification.E2E.toEdwardsHook W.Q.montToEd)
  compress : ext compressName = some (CryptoVerification.E2E.compressHook W.Q.compress)
  edNeg : ext edNegName = some (CryptoVerification.E2E.edNegHook W.Q.edNeg)
  torsionFree : ext torsionFreeName =
    some (CryptoVerification.E2E.torsionFreeHook W.Q.isTorsionFree)
  dsmb : ext dsmbName = some (CryptoVerification.E2E.dsmbHook W.Q.dsmb)
  scalarMod : ext scalarModName = some (CryptoVerification.E2E.scalarModHook W.Q.scalarMod)
  scalarWide : ext scalarWideName = some (CryptoVerification.E2E.scalarWideHook W.Q.scalarWide)
  kemEncaps : ext kemEncapsName = some (CryptoVerification.E2E.kemEncapsHook W.Q.encaps)
  kemDecaps : ext kemDecapsName = some (CryptoVerification.E2E.kemDecapsHook W.Q.decaps)
  mlkemFromSeed : ext mlkemFromSeedName = some (CryptoVerification.E2E.mlkemFromSeedHook W.Q.K)
  mlkemPk1 : ext mlkemPk1Name = some CryptoVerification.E2E.mlkemPk1Hook
  mlkemPk2 : ext mlkemPk2Name = some CryptoVerification.E2E.mlkemPk2Hook
  mlkemEncaps1 : ext mlkemEncaps1Name = some (CryptoVerification.E2E.mlkemEncaps1Hook W.Q.K)
  mlkemEncaps2 : ext mlkemEncaps2Name = some (CryptoVerification.E2E.mlkemEncaps2Hook W.Q.K)
  mlkemDecaps : ext mlkemDecapsName = some (CryptoVerification.E2E.mlkemDecapsHook W.Q.K)
  mlkemValidatePk : ext mlkemValidatePkName =
    some (CryptoVerification.E2E.mlkemValidatePkHook W.Q.K)
  libcruxHmac : ext libcruxHmacName = some (libcruxHmacHookMallocng mpl W.C.F)

/-- Coerce `FineCliB2ExternRows` to `FineCliB2ExternRowsSat`. -/
theorem FineCliB2ExternRows.toSat [LibsignalPlacement] {mpl : Obj.MultiPlacement}
    {W : CliHooks} {ext : String → Option (State → State)}
    (h : FineCliB2ExternRows mpl W ext) : FineCliB2ExternRowsSat mpl W ext where
  shim := h.shim
  memset := h.memset
  memmove := h.memmove
  memcpy := h.memcpy
  memcpyRO := h.memcpyRO
  bcmp := h.bcmp
  strlen := h.strlen
  writeFile := h.writeFile
  writeStdout := h.writeStdout
  memrchr := h.memrchr
  fromUtf8 := h.fromUtf8
  stringClone := h.stringClone
  fmtWrite := h.fmtWrite
  formatInner := h.formatInner
  durationSince := h.durationSince
  timeAdd := h.timeAdd
  blackBox := h.blackBox
  compress256 := h.compress256
  aesEnc := h.aesEnc
  aesDec := h.aesDec
  pubFromSecret := h.pubFromSecret
  dh := h.dh
  staticDrop := h.staticDrop
  sharedDrop := h.sharedDrop
  compress512 := h.compress512
  toEdwards := h.toEdwards
  compress := h.compress
  edNeg := h.edNeg
  torsionFree := h.torsionFree
  dsmb := h.dsmb
  scalarMod := h.scalarMod
  scalarWide := h.scalarWide
  kemEncaps := h.kemEncaps
  kemDecaps := h.kemDecaps
  mlkemFromSeed := h.mlkemFromSeed
  mlkemPk1 := h.mlkemPk1
  mlkemPk2 := h.mlkemPk2
  mlkemEncaps1 := h.mlkemEncaps1
  mlkemEncaps2 := h.mlkemEncaps2
  mlkemDecaps := h.mlkemDecaps
  mlkemValidatePk := h.mlkemValidatePk
  libcruxHmac := h.libcruxHmac

/-- `HookSat` sibling of `fineCliExternsBudgetAllocSlice` (`SpecBudgetFine.lean:691`). -/
theorem fineCliExternsBudgetAllocSlice_sat [LibsignalPlacement]
    (W : CliHooks) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {ext : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext)
    (hAllocZeroed : HookSat ext allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hRows : FineCliB2ExternRowsSat mpl W ext) :
    FineCliExternsAllocSlice ⟨W.C, W.Q⟩ fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext where
  shim := hookSat_of_hookOk hRows.shim cliShim_hookOk
  alloc := hAlloc
  allocZeroed := hAllocZeroed
  memset := hRows.memset
  memmove := hookSat_of_hookOk hRows.memmove cliMemmove_hookOk
  memcpy := hRows.memcpy
  memcpyRO := hRows.memcpyRO
  bcmp := hookSat_of_hookOk hRows.bcmp (cliBcmp_hookOk W)
  strlen := hookSat_of_hookOk hRows.strlen cliStrlen_hookOk
  writeFile img := hookSat_writeFileBudget_of_hookSat
    (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    (hookSat_of_hookOk hRows.writeFile (cliWriteFile_hookOk img))
    (fun _ hf s => (Option.some.inj (hRows.writeFile.symm.trans hf)) ▸ vmPreserved_writeFileHook s)
  writeStdout img := hookSat_writeStdoutBudget_of_hookSat
    (fineHookRustCliAllocBudget γ mpl tp brkStart) lim
    (hookSat_of_hookOk hRows.writeStdout (cliWriteStdout_hookOk img))
    (fun _ hf s => (Option.some.inj (hRows.writeStdout.symm.trans hf)) ▸ vmPreserved_writeStdoutHook s)
  memrchr := hookSat_of_hookOk hRows.memrchr cliMemrchr_hookOk
  fromUtf8 := hookSat_of_hookOk hRows.fromUtf8 (cliFromUtf8_hookOk W)
  stringClone := fineStringClone_budget_hookSat γ tp brkStart lim hPl hRows.stringClone
  fmtWrite := hookSat_of_hookOk hRows.fmtWrite
    (fmtWriteHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)
  formatInner := hookSat_of_hookOk hRows.formatInner
    (formatInnerHook0_budget_ok fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim)
  durationSince := hookSat_of_hookOk hRows.durationSince durationSinceExactHook_epoch_budget_ok
  timeAdd := hookSat_of_hookOk hRows.timeAdd timeAddHook_budget_ok
  blackBox := hookSat_of_hookOk hRows.blackBox cliBlackBox_hookOk
  compress256 := hookSat_of_hookOk hRows.compress256 (cliCompress256_hookOk W.C)
  aesEnc := fineAesEnc_budget_hookSat γ tp brkStart lim hPl W.C.E hRows.aesEnc
  aesDec := fineAesDec_budget_hookSat γ tp brkStart lim hPl W.C.D hRows.aesDec
  pubFromSecret := hookSat_of_hookOk hRows.pubFromSecret (cliPubFromSecret_hookOk W.C)
  dh := hookSat_of_hookOk hRows.dh (cliDh_hookOk W.C)
  staticDrop := hookSat_of_hookOk hRows.staticDrop cliZeroize_hookOk
  sharedDrop := hookSat_of_hookOk hRows.sharedDrop cliZeroize_hookOk
  compress512 := hookSat_of_hookOk hRows.compress512 (cliCompress512_hookOk W.Q)
  toEdwards := hookSat_of_hookOk hRows.toEdwards (cliToEdwards_hookOk W.Q)
  compress := hookSat_of_hookOk hRows.compress (cliCompress_hookOk W.Q)
  edNeg := hookSat_of_hookOk hRows.edNeg (cliEdNeg_hookOk W.Q)
  torsionFree := hookSat_of_hookOk hRows.torsionFree (cliTorsionFree_hookOk W.Q)
  dsmb := hookSat_of_hookOk hRows.dsmb (cliDsmb_hookOk W.Q)
  scalarMod := hookSat_of_hookOk hRows.scalarMod (cliScalarMod_hookOk W.Q)
  scalarWide := hookSat_of_hookOk hRows.scalarWide (cliScalarWide_hookOk W.Q)
  kemEncaps := hookSat_of_hookOk hRows.kemEncaps (cliKemEncaps_hookOk W.Q)
  kemDecaps := hookSat_of_hookOk hRows.kemDecaps (cliKemDecaps_hookOk W.Q)
  spqrB2 := fineSpqrB2Hooks_of_b2 W.C γ tp brkStart lim W.Q.K hPl
    hRows.mlkemFromSeed hRows.mlkemPk1 hRows.mlkemPk2 hRows.mlkemEncaps1
    hRows.mlkemEncaps2 hRows.mlkemDecaps hRows.mlkemValidatePk hRows.libcruxHmac

/-- `HookSat` sibling of `fineCliExternsBudgetOk_of_b2` (`SpecBudgetFine.lean:757`). -/
theorem fineCliExternsBudgetOk_of_b2_sat [LibsignalPlacement]
    (W : CliHooks) (γ : GhostName) {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64)
    (lim : BudgetLimits) {ext : String → Option (State → State)}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hTpidr : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0)
    (hNoExec : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x)
    (hFsTraced : ∀ n f, ext n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hFsKept : ∀ n f, ext n = some f → n ∉ ioNames → ∀ s, (f s).fs = s.fs)
    (hVmKept : ∀ n f, ext n = some f → n ∉ cliAllocNames → ∀ s, VmPreserved s (f s))
    (hAlloc : AllocHooksBudget fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext)
    (hAllocZeroed : HookSat ext allocZeroedName
      (rustAllocZeroedBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim))
    (hReadFile : ∀ img, HookSat ext readFileName
      (readFileBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim img))
    (hReadStdin : ∀ img, HookSat ext readStdinName
      (readStdinBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim img))
    (hRows : FineCliB2ExternRowsSat mpl W ext)
    (hSpqrRes : SpqrHooksB2Residual W.C fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim W.Q.K ext) :
    CliExternsBudgetOk ⟨W.C, W.Q⟩ fineCostModel
      (fineHookRustCliAllocBudget γ mpl tp brkStart) lim ext :=
  fineCliExternsBudgetOk_of_slice hTpidr hNoExec hFsTraced hFsKept hVmKept hReadFile hReadStdin
    (fineCliExternsBudgetAllocSlice_sat W γ tp brkStart lim hPl hAlloc hAllocZeroed hRows)
    hSpqrRes

end LibsignalBinary.Heap.Fine.SpecBudgetFineSat
