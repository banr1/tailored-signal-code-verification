/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement

/-!
# Equivalence of `StdinBounded` and its Pre-Key-Only Variant

Compares `StdinBounded` with the variant omitting the raw `c.stdin.length < 2 ^ 32` guard on
`.recv`: proves the unconditional forward implication (`stdinBounded_imp_p3`), definitional
equivalence on `.init` and `.send`, and equivalence across all whisper and canonical pre-key
`.recv` inputs (`stdinBounded_iff_p3`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.ParStdinIff

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyProto)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Address Cmd)
open CryptoVerification.LibsignalProtoCodec (WireType encodeBytesField encodeKey encodeUint32Field
  encodeVarint encodeVarintAux)

private theorem encodeVarintAux_length_le : ∀ (n : Nat) (v : BitVec 64),
    (encodeVarintAux n v).length ≤ n
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have h := encodeVarintAux_length_le k (v >>> 7)
      omega

private theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

private theorem encodeKey_length_le (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le _

private theorem encodeUint32Field_length_le (tag : Nat) (opt : Option (BitVec 32)) :
    (encodeUint32Field tag opt).length ≤ 20 := by
  cases opt with
  | none => simp [encodeUint32Field]
  | some v =>
    unfold encodeUint32Field
    simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.zeroExtend 64)
    omega

private theorem encodeBytesField_some_length_le (tag : Nat) (bs : List (BitVec 8)) :
    (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
  unfold encodeBytesField
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 bs.length)
  omega

private theorem preKeyWire_typed_length_le (preKeyId : Option (BitVec 32))
    (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes)
    (hik : ik.length = 32) (hek : ek.length = 32) (hct : ct.length = 1568) :
    (preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg).length ≤ msg.length + 1797 := by
  unfold preKeyWire PreKeyProto.encode
  simp only [List.length_cons, List.length_append]
  have hf1 := encodeUint32Field_length_le 1 preKeyId
  have hf2 := encodeBytesField_some_length_le 2 (ecKey ek)
  have hf3 := encodeBytesField_some_length_le 3 (ecKey ik)
  have hf4 := encodeBytesField_some_length_le 4 msg
  have hf5 := encodeUint32Field_length_le 5 (some regId)
  have hf6 := encodeUint32Field_length_le 6 (some spkId)
  have hf7 := encodeUint32Field_length_le 7 (some kpkId)
  have hf8 := encodeBytesField_some_length_le 8 (kyberKey ct)
  simp only [ecKey, kyberKey, List.length_cons] at hf2 hf3 hf8 ⊢
  omega

/-- `StdinBounded` unconditionally implies the `.recv` payload-only bound predicate. -/
theorem stdinBounded_imp_p3 : ∀ c,
    StdinBounded c →
    (
      match c.cmd with
      | .init _ _ => True
      | .send _ => c.stdin.length < 2 ^ 32
      | .recv _ =>
        (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
        (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) ∧
        (∀ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
          ik.length = 32 → ek.length = 32 → ct.length = 1568 →
          c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg →
          msg.length + 2048 < 2 ^ 32)
    ) := by
  intro c h
  unfold StdinBounded at h
  cases hc : c.cmd with
  | init peer dir =>
    exact trivial
  | send peer =>
    simp only [hc] at h
    exact h
  | recv peer =>
    simp only [hc] at h
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem stdinBounded_iff_p3_init : ∀ (c : CliCall) (peer : Address) (dir : String),
    c.cmd = .init peer dir →
    (StdinBounded c ↔
      match c.cmd with
      | .init _ _ => True
      | .send _ => c.stdin.length < 2 ^ 32
      | .recv _ =>
        (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
        (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) ∧
        (∀ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
          ik.length = 32 → ek.length = 32 → ct.length = 1568 →
          c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg →
          msg.length + 2048 < 2 ^ 32)
    ) := by
  intro c peer dir hc
  unfold StdinBounded
  rw [hc]

theorem stdinBounded_iff_p3_send : ∀ (c : CliCall) (peer : Address),
    c.cmd = .send peer →
    (StdinBounded c ↔
      match c.cmd with
      | .init _ _ => True
      | .send _ => c.stdin.length < 2 ^ 32
      | .recv _ =>
        (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
        (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) ∧
        (∀ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
          ik.length = 32 → ek.length = 32 → ct.length = 1568 →
          c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg →
          msg.length + 2048 < 2 ^ 32)
    ) := by
  intro c peer hc
  unfold StdinBounded
  rw [hc]

/-- Equivalence of `StdinBounded` and the payload-only bound predicate on `.init`, `.send`,
and whisper or canonical pre-key `.recv` calls. -/
theorem stdinBounded_iff_p3 : ∀ c,
    (match c.cmd with
    | .init _ _ => True
    | .send _ => True
    | .recv _ =>
      (∃ body, c.stdin = wireWhisperTag :: body) ∨
      (
        ∃ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
          ik.length = 32 ∧ ek.length = 32 ∧ ct.length = 1568 ∧
          c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
      )) →
    (StdinBounded c ↔
      match c.cmd with
      | .init _ _ => True
      | .send _ => c.stdin.length < 2 ^ 32
      | .recv _ =>
        (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
        (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) ∧
        (∀ (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes),
          ik.length = 32 → ek.length = 32 → ct.length = 1568 →
          c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg →
          msg.length + 2048 < 2 ^ 32)
    ) := by
  intro c
  unfold StdinBounded
  cases hc : c.cmd with
  | init peer dir =>
    intro _
    exact Iff.rfl
  | send peer =>
    intro _
    exact Iff.rfl
  | recv peer =>
    simp only
    intro hdom
    constructor
    · intro h
      exact ⟨h.1, h.2.2.1, h.2.2.2⟩
    · intro hp3
      refine ⟨hp3.1, ?_, hp3.2.1, hp3.2.2⟩
      intro hnotw
      rcases hdom with ⟨body, hst⟩ | ⟨preKeyId, spkId, kpkId, regId, ik, ek, ct, msg, hik, hek, hct, hst⟩
      · exfalso
        apply hnotw
        simp [hst]
      · have hmsg := hp3.2.2 preKeyId spkId kpkId regId ik ek ct msg hik hek hct hst
        have hwire := preKeyWire_typed_length_le preKeyId spkId kpkId regId ik ek ct msg hik hek hct
        rw [hst]
        omega

end Symbolic.Proofs.Tests.Refinement.Cli.ParStdinIff
