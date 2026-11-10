/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure -- shake: keep

/-!
# `.rodata` Loading Witness & Overlapping Error-String Store Helpers for `KpkMarkPoll`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

/-- `.rodata` address of the 8-byte `".base-ke"` slice (`+320` / `+324`). -/
abbrev dotBaseKeAddr (b : BitVec 64) : BitVec 64 :=
  b + bv% (ls_xref%
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324))

/-- `.rodata` address of the 15-byte `"reused base key"` slice (`+580` / `+584`). -/
abbrev reusedStrAddr (b : BitVec 64) : BitVec 64 :=
  b + bv% (ls_xref%
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584))

/-- `.rodata` address of the 14-byte `"malformed file"` slice (`+696` / `+700`). -/
abbrev malformedStrAddr (b : BitVec 64) : BitVec 64 :=
  b + bv% (ls_xref%
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
    (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700))

/-- Read-only spatial bundle carried across `kpkMarkPollName`. -/
def kpkMarkRoBundle (b : BitVec 64) (wDot wR0 wR7 wM0 wM6 : BitVec 64) : SepProp :=
  ((dotBaseKeAddr b) ↦₆₄ᵣ wDot) ∗
  ((reusedStrAddr b) ↦₆₄ᵣ wR0) ∗
  ((reusedStrAddr b + 7#64) ↦₆₄ᵣ wR7) ∗
  ((malformedStrAddr b) ↦₆₄ᵣ wM0) ∗
  ((malformedStrAddr b + 6#64) ↦₆₄ᵣ wM6)

/-- Every loaded image of `libsignalSessionImage` supplies `kpkMarkRoBundle` with
`unpack64 wDot = utf8 ".base-ke"`. -/
theorem kpkMarkRoData_of_loads {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp}
    (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    ∃ wDot wR0 wR7 wM0 wM6 : BitVec 64,
      unpack64 wDot = utf8 ".base-ke" ∧
      s.mem ⊨ kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗ P := by
  have hdot : Arm64.Obj.HoldsBytes s.mem (dotBaseKeAddr img.base) (utf8 ".base-ke") (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324)))
      (n := 8)
      (by decide)
      (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) utf8_dot_base_ke_length
      (by rw [utf8_dot_base_ke]; rfl_kernel)
  let r0 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584)) -
       num% (ls_field% dataOff))).take 8
  let r7 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) + 7) -
       num% (ls_field% dataOff))).take 8
  let m0 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700)) -
       num% (ls_field% dataOff))).take 8
  let m6 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) + 6) -
       num% (ls_field% dataOff))).take 8
  have hlen_r0 : r0.length = 8 := by rfl_kernel
  have hlen_r7 : r7.length = 8 := by rfl_kernel
  have hlen_m0 : m0.length = 8 := by rfl_kernel
  have hlen_m6 : m6.length = 8 := by rfl_kernel
  obtain ⟨wDot, hwDot⟩ := exists_unpack64_of_length_8 utf8_dot_base_ke_length
  obtain ⟨wR0, hwR0⟩ := exists_unpack64_of_length_8 hlen_r0
  obtain ⟨wR7, hwR7⟩ := exists_unpack64_of_length_8 hlen_r7
  obtain ⟨wM0, hwM0⟩ := exists_unpack64_of_length_8 hlen_m0
  obtain ⟨wM6, hwM6⟩ := exists_unpack64_of_length_8 hlen_m6
  have hr0 : Arm64.Obj.HoldsBytes s.mem (reusedStrAddr img.base) r0 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584)))
      (n := 8) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen_r0 rfl
  have hr7 : Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) + 7))
      r7 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) + 7))
      (n := 8) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen_r7 rfl
  have hm0 : Arm64.Obj.HoldsBytes s.mem (malformedStrAddr img.base) m0 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700)))
      (n := 8) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen_m0 rfl
  have hm6 : Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) + 6))
      m6 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
        (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) + 6))
      (n := 8) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen_m6 rfl
  have had_r7 : img.base + bv% (ls_xref%
      (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
      (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) + 7) =
      reusedStrAddr img.base + 7#64 := by
    unfold reusedStrAddr; bv_omega
  have had_m6 : img.base + bv% (ls_xref%
      (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
      (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) + 6) =
      malformedStrAddr img.base + 6#64 := by
    unfold malformedStrAddr; bv_omega
  rw [had_r7] at hr7
  rw [had_m6] at hm6
  refine ⟨wDot, wR0, wR7, wM0, wM6, hwDot.symm, ?_⟩
  have s1 := Satisfies.of_holdsBytes_ro hm6 (by rw [hlen_m6]; decide) hP
  have s2 := Satisfies.of_holdsBytes_ro hm0 (by rw [hlen_m0]; decide) s1
  have s3 := Satisfies.of_holdsBytes_ro hr7 (by rw [hlen_r7]; decide) s2
  have s4 := Satisfies.of_holdsBytes_ro hr0 (by rw [hlen_r0]; decide) s3
  have s5 := Satisfies.of_holdsBytes_ro hdot (by rw [utf8_dot_base_ke_length]; decide) s4
  rw [hwDot, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwR0, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwR7, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwM0, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  rw [hwM6, ← pointsTo64RO_eq_pointsToBytesRO] at s5
  unfold kpkMarkRoBundle
  simpa only [sepConj_assoc] using s5

/-! ## Layout-Independent `ADRP + ADD` Address Resolution -/

theorem adrp_add_dotBaseKe_eq {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (he : fnBase = b + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) :
    (((fnBase + 320#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320))) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324) % 4096) =
    dotBaseKeAddr b := by
  subst he
  have hpage :
      ((bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") + 320#64 : BitVec 64) &&&
        0xfffffffffffff000#64) =
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)) := by
    decide
  have hsum :
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324) % 4096) =
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 320)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 324)) := by
    decide
  rw [BitVec.add_assoc b, ProofLib.ObjectLoad.adrp_page_of_aligned hb, hpage]
  unfold dotBaseKeAddr
  rw [← hsum]
  bv_omega

theorem adrp_add_reused_eq {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (he : fnBase = b + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) :
    (((fnBase + 580#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580))) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) % 4096) =
    reusedStrAddr b := by
  subst he
  have hpage :
      ((bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") + 580#64 : BitVec 64) &&&
        0xfffffffffffff000#64) =
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)) := by
    decide
  have hsum :
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584) % 4096) =
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 580)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 584)) := by
    decide
  rw [BitVec.add_assoc b, ProofLib.ObjectLoad.adrp_page_of_aligned hb, hpage]
  unfold reusedStrAddr
  rw [← hsum]
  bv_omega

theorem adrp_add_malformed_eq {b fnBase : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (he : fnBase = b + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) :
    (((fnBase + 696#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696))) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) % 4096) =
    malformedStrAddr b := by
  subst he
  have hpage :
      ((bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") + 696#64 : BitVec 64) &&&
        0xfffffffffffff000#64) =
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)) := by
    decide
  have hsum :
      bv% (page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700)) -
           page% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700) % 4096) =
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 696)
            (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}" + 700)) := by
    decide
  rw [BitVec.add_assoc b, ProofLib.ObjectLoad.adrp_page_of_aligned hb, hpage]
  unfold malformedStrAddr
  rw [← hsum]
  bv_omega

/-! ## Writable Overlapping Store Helpers (`[0..8)` + `[7..15)` and `[0..8)` + `[6..14)`) -/

theorem write_15_overlap_mid (buf w0 : BitVec 64) :
    (buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 7 ⊢
      (buf ↦ₛ (unpack64 w0).take 7) ∗ memRegion (buf + 7#64) 8 := by
  have h1 : (unpack64 w0).length = 8 := unpack64_length w0
  have h7 : ((unpack64 w0).take 7).length = 7 := by simp [h1]
  have hrem : ((unpack64 w0).drop 7).length = 1 := by simp [h1]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 7 (unpack64 w0),
      pointsToBytes_append, h7]
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [memRegion_split (buf + 7#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (hrem ▸ pointsToBytes_entails_memRegion _ _)

theorem write_15_overlap_done (buf w0 w7 : BitVec 64) :
    (buf ↦ₛ (unpack64 w0).take 7) ∗ ((buf + 7#64) ↦₆₄ w7) ⊢
      buf ↦ₛ ((unpack64 w0).take 7 ++ unpack64 w7) := by
  have h7 : ((unpack64 w0).take 7).length = 7 := by simp [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, h7]
  exact Entails.refl _

theorem write_14_overlap_mid (buf w0 : BitVec 64) :
    (buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 6 ⊢
      (buf ↦ₛ (unpack64 w0).take 6) ∗ memRegion (buf + 6#64) 8 := by
  have h1 : (unpack64 w0).length = 8 := unpack64_length w0
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [h1]
  have hrem : ((unpack64 w0).drop 6).length = 2 := by simp [h1]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 6 (unpack64 w0),
      pointsToBytes_append, h6]
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [memRegion_split (buf + 6#64) 2 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (hrem ▸ pointsToBytes_entails_memRegion _ _)

theorem write_14_overlap_done (buf w0 w6 : BitVec 64) :
    (buf ↦ₛ (unpack64 w0).take 6) ∗ ((buf + 6#64) ↦₆₄ w6) ⊢
      buf ↦ₛ ((unpack64 w0).take 6 ++ unpack64 w6) := by
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, h6]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
