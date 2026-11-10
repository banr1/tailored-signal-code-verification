/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure

/-!
# `.rodata` Loading Witness (`Obj.Loads libsignalSessionImage img → DirGetRoData img`)

Kept in its own small leaf module so kernel byte-slice checks over `libsignalSessionImage.data`
compile once and remain cached across edits to the control-flow proof files.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- Every loaded image of `libsignalSessionImage` satisfies `DirGetRoData img`. -/
theorem dirGetRoData_of_loads {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    DirGetRoData img := by
  intro s P hF hP
  have hread : Arm64.Obj.HoldsBytes s.mem (readOpStrAddr img.base) (utf8 "read") (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 448)))
      (n := 4)
      (by decide)
      (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) utf8_read_length (by rw [utf8_read]; rfl_kernel)
  let bs0 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404)) -
       num% (ls_field% dataOff))).take 8
  let bs8 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 8) -
       num% (ls_field% dataOff))).take 8
  let bs14 : List (BitVec 8) :=
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 14) -
       num% (ls_field% dataOff))).take 8
  have hlen0 : bs0.length = 8 := by rfl_kernel
  have hlen8 : bs8.length = 8 := by rfl_kernel
  have hlen14 : bs14.length = 8 := by rfl_kernel
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 hlen0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 hlen8
  obtain ⟨wTail, hwt⟩ := exists_unpack64_of_length_8 hlen14
  have hb0 : Arm64.Obj.HoldsBytes s.mem (unreadableStrAddr img.base) bs0 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404)))
      (n := 8)
      (by decide)
      (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen0 rfl
  have hb8 : Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 8)) bs8 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 8))
      (n := 8)
      (by decide)
      (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen8 rfl
  have hb14 : Arm64.Obj.HoldsBytes s.mem
      (img.base + bv% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 14)) bs14 (fun _ => .ro) :=
    ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
      (off := num% (ls_xref%
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
        (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 14))
      (n := 8)
      (by decide)
      (Nat.le_of_ble_eq_true (by rfl_kernel))
      (by rfl_kernel) (by rfl_kernel) hlen14 rfl
  have hadd8 : img.base + bv% (ls_xref%
      (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
      (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 8) =
      unreadableStrAddr img.base + 8#64 := by
    unfold unreadableStrAddr; bv_omega
  have hadd14 : img.base + bv% (ls_xref%
      (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
      (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) + 14) =
      unreadableStrAddr img.base + 14#64 := by
    unfold unreadableStrAddr; bv_omega
  rw [hadd8] at hb8
  rw [hadd14] at hb14
  refine ⟨w0, w1, wTail, ?_⟩
  have s1 := Satisfies.of_holdsBytes_ro hread (by rw [utf8_read_length]; decide) hP
  have s2 := Satisfies.of_holdsBytes_ro hb14 (by rw [hlen14]; decide) s1
  have s3 := Satisfies.of_holdsBytes_ro hb8 (by rw [hlen8]; decide) s2
  have s4 := Satisfies.of_holdsBytes_ro hb0 (by rw [hlen0]; decide) s3
  rw [hw0, ← pointsTo64RO_eq_pointsToBytesRO] at s4
  rw [hw1, ← pointsTo64RO_eq_pointsToBytesRO] at s4
  rw [hwt, ← pointsTo64RO_eq_pointsToBytesRO] at s4
  unfold dirGetRoBundle
  simpa only [sepConj_assoc] using s4

end CryptoVerification.SignalSession.Cli.Get.Helpers
