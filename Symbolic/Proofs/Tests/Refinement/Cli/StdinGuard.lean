/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement

/-!
# Bounds and Narrowing Checks on `StdinBounded`

Compares `StdinBounded` with the parse-only variant `StdinBoundedR6`, proving that `StdinBounded`
implies `StdinBoundedR6`, that the two agree when `stdin.length + 2048 < 2 ^ 32`, and that any
canonical pre-key with `2 ^ 32 <= msg.length + 2048` fails `StdinBounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.StdinGuard

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession (Cmd)

/-- Parse-only variant of `StdinBounded` omitting the canonical pre-key field bound. -/
def StdinBoundedR6 (c : CliCall) : Prop :=
  match c.cmd with
  | .init _ _ => True
  | .send _ => c.stdin.length < 2 ^ 32
  | .recv _ =>
    (∀ body, c.stdin = wireWhisperTag :: body → body.length < 2 ^ 32) ∧
    (∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32)

theorem stdinBoundedR6_of_stdinBounded (c : CliCall) (h : StdinBounded c) : StdinBoundedR6 c := by
  unfold StdinBounded at h; unfold StdinBoundedR6
  cases hc : c.cmd <;> simp only [hc] at h ⊢
  · exact h
  · exact ⟨h.1, h.2.2.1⟩

theorem msg_length_le_preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32)
    (ik ek ct msg : HwBytes) :
    msg.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length := by
  unfold preKeyWire DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [List.length_cons, List.length_append]; omega

/-- On `stdin` with `stdin.length + 2048 < 2 ^ 32`, `StdinBoundedR6` implies `StdinBounded`. -/
theorem stdinBounded_of_r6_of_short (c : CliCall) (h : StdinBoundedR6 c)
    (hshort : c.stdin.length + 2048 < 2 ^ 32) : StdinBounded c := by
  unfold StdinBoundedR6 at h; unfold StdinBounded
  cases hc : c.cmd <;> simp only [hc] at h ⊢
  · exact h
  · refine ⟨h.1, fun _ => by omega, h.2, fun preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst => ?_⟩
    have := msg_length_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg
    rw [← hst] at this; omega

/-- A canonical pre-key with `2 ^ 32 <= msg.length + 2048` fails `StdinBounded`, whether or not
the inner message parses. -/
theorem not_stdinBounded_of_long_inner (c : CliCall) (peer : _)
    (hc : c.cmd = .recv peer) (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32)
    (ik ek ct msg : HwBytes) (hik : ik.length = 32) (hek : ek.length = 32) (hct : ct.length = 1568)
    (hst : c.stdin = preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg)
    (hlong : 2 ^ 32 ≤ msg.length + 2048) : ¬ StdinBounded c := by
  unfold StdinBounded; rw [hc]; simp only
  intro h; have := h.2.2.2 preKeyId spkId kpkId regId ik ek ct msg hik hek hct hst; omega

end Symbolic.Proofs.Tests.Refinement.Cli.StdinGuard
