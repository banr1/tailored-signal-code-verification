/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Split
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

/-!
# CLI Refinement Instance of `RefinementShape`

Instantiates `RefinementShape` for `CompRefinesCliElf` (`cliCompShape`, `cliCompFits`), defines
witness setup records and byte-decoding helpers (`PQXDHSpqrSetup`, `CompKyberCorrectOn`,
`compFits`, `natBytes`, `hexBytes`), and proves `not_signalSessionSecure_of_witness`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli

/-- Initial key material, registration IDs, Kyber ciphertexts, and torsion shifts of a CLI witness. -/
structure PQXDHSpqrSetup where
  /-- Alice's identity secret (`secretBytes r 0`). -/
  aliceId : HwBytes
  /-- Bob's identity secret (`secretBytes r 1`). -/
  bobId : HwBytes
  /-- Bob's signed-prekey secret (`secretBytes r 2`). -/
  spk : HwBytes
  /-- Signature on Bob's signed prekey (`setupPublic r 5`). -/
  spkSig : HwBytes
  /-- Bob's Kyber public key without type byte (`setupPublic r 6`). -/
  kyberPk : HwBytes
  /-- Signature on Bob's Kyber public key (`setupPublic r 7`). -/
  kyberPkSig : HwBytes
  /-- Bob's Kyber secret key including its type byte. -/
  kyberSec : HwBytes
  regIdA : BitVec 32
  regIdB : BitVec 32
  spkId : BitVec 32
  kpkId : BitVec 32
  /-- Kyber ciphertexts (without type byte) from prekey messages received by Bob. -/
  kyberCts : List HwBytes
  /-- Attacker-applied X25519 8-torsion shifts as `(point, point + T)` byte pairs with `8 • T = 0`. -/
  torsionShifts : List (HwBytes × HwBytes) := []

/-- Every ciphertext in `cts` produced by `kyberEncapsBytes` decapsulates to the same shared secret
under `kyberDecapsBytes`. -/
def CompKyberCorrectOn (i : ExternInterpretation) (r : ProtocolSetup) (cts : List HwBytes) : Prop :=
  ∀ ct ∈ cts, ∀ e ss, e.length = 32 → kyberEncapsBytes i r e = some (ct, ss) →
    kyberDecapsBytes i r ct = some ss

/-- Binds `ProtocolSetup` `r` to witness setup `w` (without one-time prekeys) and requires
`ExternCryptoLawsHold`, `X25519PubCanonical`, and `CompKyberCorrectOn` under `i`. -/
def compFits (w : PQXDHSpqrSetup) (i : ExternInterpretation) (r : ProtocolSetup) : Prop :=
  ProtocolSetupWF r ∧ r.withOpk = false ∧ r.regIdA = w.regIdA ∧ r.regIdB = w.regIdB ∧
    r.spkId = w.spkId ∧ r.kpkId = w.kpkId ∧ secretBytes r 0 = w.aliceId ∧
    secretBytes r 1 = w.bobId ∧ secretBytes r 2 = w.spk ∧
    r.opaqueBytes (setupPublic r 5) = w.spkSig ∧ r.opaqueBytes (setupPublic r 6) = w.kyberPk ∧
    r.opaqueBytes (setupPublic r 7) = w.kyberPkSig ∧ r.kyberSecB = w.kyberSec ∧
    DY.Libsignal.Refinement.ExternCryptoLawsHold i ∧ X25519PubCanonical i ∧
    CompKyberCorrectOn i r w.kyberCts

/-- Little-endian `len`-byte encoding of `n`. -/
def natBytes (len n : Nat) : HwBytes := leBytes len n

/-- Decodes a hexadecimal string into bytes (`"0a1b"` ↦ `[0x0a, 0x1b]`). -/
def hexBytes (s : String) : HwBytes :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let rec go : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (16 * digit a + digit b) :: go rest
    | _ => []
  go s.toList

/-- `CompRefinesCliElf` packaged as a `RefinementShape`, with `InvertsGuarded` CLI traces from
`initDirs` and explanation by `Explains` or `CollisionAfterExplainedPrefix`. -/
def cliCompShape : RefinementShape where
  Setup := Arm64.Process.ElfImage
  Interp := ExternInterpretation × CryptoVerification.SignalSession.CliHooks
  Rec := DY.Libsignal.Composed.Refinement.ProtocolSetup
  Ghost := DY.Libsignal.Composed.Refinement.OpaqueSymbolSemantics
  Event := CliEvent
  contracts := fun iw _ => ExternContractsHoldCli iw.1 ∧ HooksMatchInterpretation iw.1 iw.2
  wf := DY.Libsignal.Composed.Refinement.ProtocolSetupWF
  ghostOk := fun _ _ _ => True
  traces := fun elf iw r evs =>
    CliTraces (elfRel elf iw.1 iw.2) iw.1 r (CliTurn.init (initDirs iw.1 r)) evs ∧
      InvertsGuarded iw.1 r evs
  explained := fun iw r S evs =>
    (∃ g ss vis, Explains iw.1 r S g ss vis evs) ∨ CollisionAfterExplainedPrefix iw.1 r S evs

theorem cliCompShape_refines_iff (elf : Arm64.Process.ElfImage) :
    cliCompShape.Refines elf ↔ CompRefinesCliElf elf := by
  constructor
  · intro h interp hc W ha r hwf
    obtain ⟨S, _, hall⟩ := h (interp, W) ⟨hc, ha⟩ r hwf
    exact ⟨S, fun evs htr hg => hall evs ⟨htr, hg⟩⟩
  · intro h ⟨interp, W⟩ ⟨hc, ha⟩ r hwf
    obtain ⟨S, hall⟩ := h interp hc W ha r hwf
    exact ⟨S, trivial, fun evs ⟨htr, hg⟩ => hall evs htr hg⟩

/-- Combines `compFits w iw.1 r` with `ExternContractsHoldCli` and `HooksMatchInterpretation`. -/
def cliCompFits (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) : Prop :=
  compFits w iw.1 r ∧ ExternContractsHoldCli iw.1 ∧ HooksMatchInterpretation iw.1 iw.2

/-- Refutes `SignalSessionSecure bytes` from `cliCompShape.SpecHalf fits τ`, a conditional
`cliCompShape.ImplHalf fits elf τ` for the parsed ELF image, and `CoinsFresh` under `fits`.
`SpecHalf` of `cliCompShape` suffices because `SignalSessionSecure` strengthens
`CompRefinesCliElf` with `CoinsFresh` and security-query postconditions on `τ` and any collision
prefix. -/
theorem not_signalSessionSecure_of_witness {fits : cliCompShape.Interp → cliCompShape.Rec → Prop}
    {τ : List CliEvent} {bytes : List (BitVec 8)} (hs : cliCompShape.SpecHalf fits τ)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      cliCompShape.ImplHalf fits elf τ)
    (hcf : ∀ iw r, fits iw r → CoinsFresh r τ) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecure bytes := by
  rintro ⟨elf, hparse, _hcode, _hprog, hsec⟩
  obtain ⟨⟨interp, W⟩, r, hfit, ⟨hc, hW⟩, htr, hg⟩ := hi elf hparse
  obtain ⟨hwf, hne⟩ := hs (interp, W) r hfit
  obtain ⟨S, hall⟩ := hsec interp hc W hW r hwf
  refine hne S trivial ?_
  rcases hall τ htr hg (hcf (interp, W) r hfit) with ⟨hex, _⟩ | ⟨evs₁, ev, evs₂, heq, ⟨g, ss, vis, hE, hN⟩, _⟩
  · exact Or.inl hex
  · exact Or.inr ⟨evs₁, ev, evs₂, g, ss, vis, heq, hE, hN⟩

end Symbolic.BugInjection
