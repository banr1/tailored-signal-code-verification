/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

set_option autoImplicit false

/-!
# Relocatable CLI Correctness Compatibility Re-Exports

**Checked by Lean.** Compatibility re-exports of the relocatable `Obj.MultiPlacedLib` CLI
correctness definitions in `LibsignalBinary.Specifications.SignalSession.CliBinaryPq`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced

open Arm64
open Arm64.Process (ElfImage)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E (PqxdhPrims)
open CryptoVerification.SignalSession (CliHooks Inputs Outcome CliRun)

abbrev libsignalSessionLib : Obj.MultiPlacedLib := CryptoVerification.SignalSession.libsignalSessionLib

abbrev lsRustNoAllocShimSymCli : String := CryptoVerification.SignalSession.lsRustNoAllocShimSymCli
abbrev lsRustAllocSymCli : String := CryptoVerification.SignalSession.lsRustAllocSymCli
abbrev lsRustDeallocSymCli : String := CryptoVerification.SignalSession.lsRustDeallocSymCli
abbrev lsRustReallocSymCli : String := CryptoVerification.SignalSession.lsRustReallocSymCli
abbrev lsRustAllocZeroedSymCli : String := CryptoVerification.SignalSession.lsRustAllocZeroedSymCli

abbrev lsReadFileSym : String := CryptoVerification.SignalSession.lsReadFileSym
abbrev lsWriteFileSym : String := CryptoVerification.SignalSession.lsWriteFileSym
abbrev lsReadStdinSym : String := CryptoVerification.SignalSession.lsReadStdinSym
abbrev lsWriteStdoutSym : String := CryptoVerification.SignalSession.lsWriteStdoutSym

abbrev lsMemrchrSym : String := CryptoVerification.SignalSession.lsMemrchrSym
abbrev lsFromUtf8Sym : String := CryptoVerification.SignalSession.lsFromUtf8Sym
abbrev lsFmtWriteSym : String := CryptoVerification.SignalSession.lsFmtWriteSym
abbrev lsFormatInnerSym : String := CryptoVerification.SignalSession.lsFormatInnerSym
abbrev lsDurationSinceSym : String := CryptoVerification.SignalSession.lsDurationSinceSym
abbrev lsTimeAddSym : String := CryptoVerification.SignalSession.lsTimeAddSym
abbrev lsBlackBoxSym : String := CryptoVerification.SignalSession.lsBlackBoxSym
abbrev lsCompress256Sym : String := CryptoVerification.SignalSession.lsCompress256Sym
abbrev lsAesEncSym : String := CryptoVerification.SignalSession.lsAesEncSym
abbrev lsAesDecSym : String := CryptoVerification.SignalSession.lsAesDecSym
abbrev lsPubFromSecretSym : String := CryptoVerification.SignalSession.lsPubFromSecretSym
abbrev lsDiffieHellmanSym : String := CryptoVerification.SignalSession.lsDiffieHellmanSym
abbrev lsStaticSecretDropSym : String := CryptoVerification.SignalSession.lsStaticSecretDropSym
abbrev lsSharedSecretDropSym : String := CryptoVerification.SignalSession.lsSharedSecretDropSym

noncomputable abbrev cliPqxdhHookTablePlaced (mmpl : Obj.MultiPlacement) (C : Crypto)
    (Q : PqxdhPrims) : List (String × (State → State)) :=
  CryptoVerification.SignalSession.cliPqxdhHookTablePlaced mmpl C Q

noncomputable abbrev cliHookTablePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    List (String × (State → State)) :=
  CryptoVerification.SignalSession.cliHookTablePlaced mmpl W

abbrev cliPanicSymbolsPlaced : List String :=
  CryptoVerification.SignalSession.cliPanicSymbolsPlaced

abbrev isCliPanicSymbolPlaced (name : String) : Bool :=
  CryptoVerification.SignalSession.isCliPanicSymbolPlaced name

noncomputable abbrev cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  CryptoVerification.SignalSession.cliExternsPlaced mmpl W

noncomputable abbrev cliExternsPlacedSig (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  CryptoVerification.SignalSession.cliExternsPlacedSig mmpl W

noncomputable abbrev cliProgPlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : Program :=
  CryptoVerification.SignalSession.Placed.cliProgPlacedSig mpl mmpl W

abbrev cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) : State :=
  CryptoVerification.SignalSession.Placed.cliTokenPatchPlaced mpl s

abbrev CliRunsToPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs)
    (o : Outcome) : Prop :=
  CryptoVerification.SignalSession.Placed.CliRunsToPlaced mpl mmpl elf W i o

noncomputable abbrev cliRunPlacedSig (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : CliRun :=
  CryptoVerification.SignalSession.Placed.cliRunPlacedSig mpl mmpl elf W

abbrev CliElfCodeMatchesPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl mmpl elf

abbrev CliPqxdhElfCorrectPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CryptoVerification.SignalSession.CliPqxdhElfCorrectPlaced mpl mmpl elf

abbrev CliPqxdhBinaryCorrectPlacedAt (mpl mmpl : Obj.MultiPlacement) (bytes : List (BitVec 8)) :
    Prop :=
  CryptoVerification.SignalSession.CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes

abbrev CliPqxdhBinaryCorrectPlaced (bytes : List (BitVec 8)) : Prop :=
  CryptoVerification.SignalSession.CliPqxdhBinaryCorrectPlaced bytes

end LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
