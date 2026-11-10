/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.Specifications.Refinement.Statement

/-!
# Relocatable ELF Binding for CLI Refinement

Instantiates `CompRefinesCli` with the relocatable ARM64 ELF run relation (`elfRelPlaced`) over
placements `(mpl, mmpl)` of `libsignalSessionLib` and `mallocngLib`, together with hook-to-symbol
agreement (`HooksMatchInterpretation`) and the no-fault termination guarantee
(`CliElfProgressPlaced`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
  x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol
  torsionFreeSymbol)
open CryptoVerification.SignalSession (CliHooks libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced cliRunPlacedSig)

/-- Agreement between `CliHooks` `W` and `ExternInterpretation` `interp` on SHA-256 compression,
AES-256-CBC, X25519, Kyber-1024, Montgomery-to-Edwards conversion, and curve torsion checks. -/
def HooksMatchInterpretation (interp : ExternInterpretation) (W : CliHooks) : Prop :=
  W.C.F = sha256CompressFunction interp ∧
  (∀ p k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcEncryptSymbol [p, k, iv] =
      some (CryptoGames.LibsignalSession.aesCbcEncrypt W.C.E (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) p)) ∧
  (∀ c k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcDecryptSymbol [c, k, iv] =
      CryptoGames.LibsignalSession.aesCbcDecrypt W.C.D (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) c) ∧
  (∀ a b : List.Vector (BitVec 8) 32,
    interp x25519AgreementSymbol [a.toList, b.toList] = some (W.C.X a b).toList) ∧
  (∀ a : List.Vector (BitVec 8) 32,
    interp x25519PublicKeySymbol [a.toList] = some (W.C.pubKey a).toList) ∧
  (∀ (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32),
    interp kyberEncapsSymbol [pk.toList, rand.toList] =
      some ((W.Q.encaps pk rand).1.toList ++ (W.Q.encaps pk rand).2.toList)) ∧
  (∀ (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568),
    interp kyberDecapsSymbol [sk.toList, ct.toList] = some (W.Q.decaps sk ct).toList) ∧
  (∀ (u : List.Vector (BitVec 8) 32) (sign : BitVec 8),
    interp toEdwardsSymbol [u.toList, [sign]] = (W.Q.montToEd u sign).map List.Vector.toList) ∧
  (∀ pt : List.Vector (BitVec 8) 160,
    W.Q.isTorsionFree pt = decide (interp torsionFreeSymbol [pt.toList] = some [1#8]))

/-- Relocatable ARM64 process run relation of `elf` at multi-block placements `(mpl, mmpl)` under
hooks `W`. -/
noncomputable def elfRelPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (_interp : ExternInterpretation) (W : CliHooks) :
    CryptoVerification.SignalSession.Inputs →
    Option CryptoVerification.SignalSession.Outcome → Prop :=
  runFnToRelation (cliRunPlacedSig mpl mmpl elf W)

/-- Progress (no CPU fault, trap, or non-termination) on every guarded `CliCall` at any turn
reachable from `initDirs` under `elfRelPlaced mpl mmpl elf`. -/
def CliElfProgressPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : CliHooks, HooksMatchInterpretation interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn,
    CliReachable (elfRelPlaced mpl mmpl elf interp W) interp r
      (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    cliRunPlacedSig mpl mmpl elf W i ≠ none

/-- Whole-protocol refinement and progress guarantee for ELF image `bytes` at placements
`(mpl, mmpl)`. -/
def CompRefinesCliBinaryPlacedAt (mpl mmpl : Obj.MultiPlacement) (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl mmpl elf ∧
    CliElfProgressPlaced mpl mmpl elf ∧
    CompRefinesCli HooksMatchInterpretation (elfRelPlaced mpl mmpl elf)

/-- Relocatable whole-protocol refinement and progress guarantee quantified over all valid
placements `(mpl, mmpl)` of `libsignalSessionLib` and `mallocngLib` in `bytes`. -/
def CompRefinesCliBinaryPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CompRefinesCliBinaryPlacedAt mpl mmpl bytes

end DY.Libsignal.Composed.Refinement.Cli
