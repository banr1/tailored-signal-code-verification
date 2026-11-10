/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
import Symbolic.Proofs.Swarm.CREF.Prelude

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

/-!
# Pre-Key Promote Specializations of `cBadStep`

Specializes `cBadStep_whisper_before_c13` and `cBadStep_whisper_c13` to pre-key promote calls
(`parsePreKeyWire (tag :: body) = some p` with `KnownBaseKey`).
-/

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

variable (interpretation : ExternInterpretation)

theorem cBadStep_promote_before_c13 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₀ : Ghost} {ms₀ : List Move} {acc τ₂ : List MachineEvent}
    {tag : BitVec 8} {body pt : HwBytes} {p : PreKeyFields} {t₀ : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g₀ ms₀ p.message)
    (hpt : (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt))
    (hp : parsePreKeyWire (tag :: body) = some p)
    (hkb : KnownBaseKey interpretation r S g₀ ms₀ p) :
    (∃ g_clean ms_clean t_clean,
      CleanBy interpretation r S who ok g_clean ms_clean acc ∧
      t_clean ∈ recvRepresentations interpretation r S g_clean ms_clean p.message ∧
      ¬ RecvCollision interpretation r S g_clean ms_clean t_clean ∧
      RecvExcuseFree interpretation r S who ok g_clean ms_clean acc (.recv (tag :: body)) τ₂ p.message t_clean) ∨
    CollisionAt interpretation r S who ok (acc ++ .recv (tag :: body) :: τ₂) :=
  cBadStep_whisper_before_c13 hc₀ ht₀ hpt (Or.inr ⟨p, hp, rfl, hkb⟩)

theorem cBadStep_promote_c13 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g₀ : Ghost} {ms₀ : List Move} {acc mid : List MachineEvent}
    {tag : BitVec 8} {body pt : HwBytes} {p : PreKeyFields} {t₀ : DY.Bytes}
    (hc₀ : CleanBy interpretation r S who ok g₀ ms₀ acc)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r S g₀ ms₀ p.message)
    (hmid_no_recv : ∀ e ∈ mid, ∀ x, e ≠ .recv x)
    (hpt : ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt))
    (hp : parsePreKeyWire (tag :: body) = some p)
    (hkb : KnownBaseKey interpretation r S g₀ ms₀ p)
    (hG2 : CBadG2Hyp interpretation r S who ok acc mid pt tag body p.message) :
    (∃ g_clean ms_clean,
      CleanBy interpretation r S who ok g_clean ms_clean
        (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))) ∨
    CollisionAt interpretation r S who ok
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt])) :=
  cBadStep_whisper_c13 hc₀ ht₀ hmid_no_recv hpt (Or.inr ⟨p, hp, rfl, hkb⟩) hG2

end Symbolic.Swarm.CREF
