/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps

/-!
# Relocatable Stage P2 Alignment, Error Reassembly, and `.rodata` Helpers

Relocatable `[LibsignalPlacement]` `.rodata..Lanon.86` conjuring lemmas and re-exports of the pure
realignment and `InvalidMessage` reassembly helpers from `Matched.M2Aux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced

theorem mismatchRemoteIkStr_length_placed [LibsignalPlacement] :
    mismatchRemoteIkStr.length = 70 :=
  mismatchRemoteIkStr_length

/-- Conjures `.rodata..Lanon.86` (70 bytes at `lsρ "signal_session_handshake:.rodata..Lanon.86"`)
into the spatial precondition from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem rodata_mismatchRemoteIk_placed_intro [LibsignalPlacement]
    {s : State} (hro : CryptoVerification.LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStr) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

/-- `SepWPp` wrapper conjuring `(lsρ "signal_session_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStr`
into the precondition when `LibsignalCodeRoLoaded lsmpl s.mem` holds. -/
theorem SepWPp.intro_rodata_mismatchRemoteIk_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStr) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStr) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_mismatchRemoteIk_placed_intro hcro.2 hm
  exact h R hm' hL

/-- Image-free `.rodata..Lanon.86` bytes extracted directly from `libsignalSessionLib`. -/
def mismatchRemoteIkStrPlaced : List (BitVec 8) :=
  lsroBytes "libsignal_cli_handshake:.rodata..Lanon.86"

theorem mismatchRemoteIkStrPlaced_length :
    mismatchRemoteIkStrPlaced.length = 70 := by
  rfl_kernel

/-- Image-free `.rodata..Lanon.86` introduction from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem rodata_mismatchRemoteIk_placed_intro' [LibsignalPlacement]
    {s : State} (hro : CryptoVerification.LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStrPlaced) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

/-- Image-free `SepWPp` wrapper conjuring `mismatchRemoteIkStrPlaced`. -/
theorem SepWPp.intro_rodata_mismatchRemoteIk_placed' [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStrPlaced) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.86") ↦ᵣ mismatchRemoteIkStrPlaced) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_mismatchRemoteIk_placed_intro' hcro.2 hm
  exact h R hm' hL

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
