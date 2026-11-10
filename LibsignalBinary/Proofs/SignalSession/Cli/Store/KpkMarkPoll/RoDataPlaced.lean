/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BridgeReloc
import all Init.Data.String.Defs

/-!
# `.rodata` Loading Witness & Overlapping Error-String Store Helpers for `KpkMarkPoll` (`[LibsignalPlacement]`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev dotBaseKeSym : String := "libsignal_cli:.rodata..Lanon.29"
abbrev reusedStrSym : String := "libsignal_cli:.rodata..Lanon.32"
abbrev malformedStrSym : String := "libsignal_cli:.rodata..Lanon.67"

/-- `.rodata` address of the 8-byte `".base-ke"` slice (`+320` / `+324`) under `[LibsignalPlacement]`. -/
abbrev dotBaseKeAddrPlaced [LibsignalPlacement] : BitVec 64 :=
  lsρ dotBaseKeSym

/-- `.rodata` address of the 15-byte `"reused base key"` slice (`+580` / `+584`) under `[LibsignalPlacement]`. -/
abbrev reusedStrAddrPlaced [LibsignalPlacement] : BitVec 64 :=
  lsρ reusedStrSym

/-- `.rodata` address of the 14-byte `"malformed file"` slice (`+696` / `+700`) under `[LibsignalPlacement]`. -/
abbrev malformedStrAddrPlaced [LibsignalPlacement] : BitVec 64 :=
  lsρ malformedStrSym

/-- Read-only spatial bundle carried across `kpkMarkPollName` under `[LibsignalPlacement]`. -/
def kpkMarkRoBundlePlaced [LibsignalPlacement] (wDot wR0 wR7 wM0 wM6 : BitVec 64) : SepProp :=
  (dotBaseKeAddrPlaced ↦₆₄ᵣ wDot) ∗
  (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
  ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
  (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
  ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6)

/-- Every `LibsignalRoLoaded` memory supplies `kpkMarkRoBundlePlaced` with
`unpack64 wDot = utf8 ".base-ke"`. -/
theorem kpkMarkRoDataPlaced_of_roLoaded [LibsignalPlacement]
    {s : State} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    ∃ wDot wR0 wR7 wM0 wM6 : BitVec 64,
      unpack64 wDot = utf8 ".base-ke" ∧
      s.mem ⊨ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗ P := by
  have hlen_r0 : (utf8 "reused b").length = 8 := by rfl_kernel
  have hlen_r7 : (utf8 "base key").length = 8 := by rfl_kernel
  have hlen_m0 : (utf8 "malforme").length = 8 := by rfl_kernel
  have hlen_m6 : (utf8 "med file").length = 8 := by rfl_kernel
  obtain ⟨wDot, hwDot⟩ := exists_unpack64_of_length_8 utf8_dot_base_ke_length
  obtain ⟨wR0, hwR0⟩ := exists_unpack64_of_length_8 hlen_r0
  obtain ⟨wR7, hwR7⟩ := exists_unpack64_of_length_8 hlen_r7
  obtain ⟨wM0, hwM0⟩ := exists_unpack64_of_length_8 hlen_m0
  obtain ⟨wM6, hwM6⟩ := exists_unpack64_of_length_8 hlen_m6
  refine ⟨wDot, wR0, wR7, wM0, wM6, hwDot.symm, ?_⟩
  have s1 := lsro_slice_intro hro (sym := malformedStrSym) (off := 6)
    (addr := malformedStrAddrPlaced + 6#64) (bs := utf8 "med file") rfl (by rfl_kernel) hP
  have s2 := lsro_slice_intro hro (sym := malformedStrSym) (off := 0)
    (addr := malformedStrAddrPlaced) (bs := utf8 "malforme") (BitVec.add_zero _).symm (by rfl_kernel) s1
  have s3 := lsro_slice_intro hro (sym := reusedStrSym) (off := 7)
    (addr := reusedStrAddrPlaced + 7#64) (bs := utf8 "base key") rfl (by rfl_kernel) s2
  have s4 := lsro_slice_intro hro (sym := reusedStrSym) (off := 0)
    (addr := reusedStrAddrPlaced) (bs := utf8 "reused b") (BitVec.add_zero _).symm (by rfl_kernel) s3
  have s5 := lsro_slice_intro hro (sym := dotBaseKeSym) (off := 0)
    (addr := dotBaseKeAddrPlaced) (bs := utf8 ".base-ke") (BitVec.add_zero _).symm (by rfl_kernel) s4
  rw [hwDot, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwR0, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwR7, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwM0, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwM6, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  unfold kpkMarkRoBundlePlaced
  simpa only [sepConj_assoc] using s5

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
