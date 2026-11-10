/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# SPQR V1 Polynomial Coefficient and State Encoding Size Bounds

Linear byte-length upper bounds on decoded `GF(2^16)` polynomial coefficients
(`decodePbPolysTotal`) and protobuf-encoded `PqRatchetState` and `V1State` values.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds

open CryptoVerification.LibsignalSpqrV1 (Bytes Poly PqRatchetState V1State)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (decodePbPolysTotal polyDeserializeTotal polyDeserialize_eq_ok)
open CryptoVerification.SpqrV1.Top.StateSize
  (encodeState_length_le_rawPqState rawPqState rawV1State v1State_encodeRaw_length_le)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto)

/-- If `decodePbPolysTotal bss = .ok out`, then `out.length = bss.length` and twice the total
decoded coefficient count is bounded by `(bss.map (fun b => b.length + 22)).sum`. -/
theorem decodePbPolysTotal_len_and_sum :
    ∀ (bss : List Bytes) (out : List Poly),
      decodePbPolysTotal bss = .ok out →
      out.length = bss.length ∧
        2 * (out.map (fun p => p.coefficients.length)).sum ≤
          (bss.map (fun b => b.length + 22)).sum
  | [], out, hdec => by
    simp only [decodePbPolysTotal, Except.ok.injEq] at hdec
    subst hdec
    simp
  | bs :: rest, out, hdec => by
    dsimp only [decodePbPolysTotal] at hdec
    cases hp : polyDeserializeTotal bs with
    | error _ => simp [hp] at hdec
    | ok p =>
      simp only [hp] at hdec
      cases hrest : decodePbPolysTotal rest with
      | error _ => simp [hrest] at hdec
      | ok tail =>
        simp only [hrest, Except.ok.injEq] at hdec
        subst hdec
        have hdes : Poly.deserialize bs = .ok (.ok p) := by
          rw [polyDeserialize_eq_ok bs, hp]
        have hp_len := CryptoVerification.SpqrV1.Top.StateSize.Poly.deserialize_length hdes
        obtain ⟨hlen_tail, hsum_tail⟩ := decodePbPolysTotal_len_and_sum rest tail hrest
        refine ⟨by simp [hlen_tail], ?_⟩
        simp only [List.map_cons, List.sum_cons]
        omega

theorem pqRatchetStateEncodeToVec_len_le (st : PqRatchetState) :
    pqRatchetStatePBEncodedLen st ≤ rawPqState st + 752 := by
  rw [← pqRatchetStatePBEncodedLen_eq_proto st]
  exact encodeState_length_le_rawPqState st

theorem v1StateEncodeRaw_len_le (m : V1State) :
    (V1State.encodeRaw m).length ≤ rawV1State m + 400 :=
  v1State_encodeRaw_length_le m

end LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds
