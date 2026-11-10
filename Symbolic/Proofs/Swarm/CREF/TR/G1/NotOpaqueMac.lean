/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Specifications.Model.EquationalTheory.Kem
import all DY.EquationalTheory.Sign
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR

/-!
# Non-Opaque Head of Parsed Signal Message MACs

Proves `notOpaqueHeaded_mac_of_parseTrSignalMsg`: every parsed `TRSignalMsg` has symbolic MAC
length at most 8, whereas all opaque KEM and signature constructors have length at least 32, so
`notOpaqueHeaded msg₀.mac` holds unconditionally.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)

theorem length_pack_kemPk (x : DY.PQKem.Pk.SubF DY.Bytes) :
    (BytesView.pack x : DY.Bytes).length = 1568 := by
  rw [DY.Bytes.length.eq]; rfl

theorem length_pack_kemEncap (x : DY.PQKem.Encap.SubF DY.Bytes) :
    (BytesView.pack x : DY.Bytes).length = 1568 := by
  rw [DY.Bytes.length.eq]; rfl

theorem length_pack_kemSharedSecret (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    (BytesView.pack x : DY.Bytes).length = 32 := by
  rw [DY.Bytes.length.eq]; rfl

theorem length_pack_sigVk (x : DY.Signature.Vk.SubF DY.Bytes) :
    (BytesView.pack x : DY.Bytes).length = 32 := by
  rw [DY.Bytes.length.eq]; rfl

theorem length_pack_sigSign (x : DY.Signature.Sign.SubF DY.Bytes) :
    (BytesView.pack x : DY.Bytes).length = 64 := by
  rw [DY.Bytes.length.eq]; rfl

private theorem view?_isNone_of_pack_length_gt
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    {u : DY.Bytes} {n : Nat}
    (hlen : ∀ x : SubF DY.Bytes, (BytesView.pack x : DY.Bytes).length = n)
    (hle : u.length ≤ 8) (hgt : 8 < n) :
    (u.view? SubF).isNone = true := by
  have hv := DY.Bytes.pack_view? SubF u
  cases h : u.view? SubF with
  | none => rfl
  | some x =>
    rw [h] at hv
    dsimp only at hv
    rw [← hv, hlen x] at hle
    omega

theorem notOpaqueHeaded_of_length_le_8 {u : DY.Bytes} (hle : u.length ≤ 8) :
    notOpaqueHeaded u :=
  ⟨view?_isNone_of_pack_length_gt length_pack_kemPk hle (by decide),
   view?_isNone_of_pack_length_gt length_pack_kemEncap hle (by decide),
   view?_isNone_of_pack_length_gt length_pack_kemSharedSecret hle (by decide),
   view?_isNone_of_pack_length_gt length_pack_sigVk hle (by decide),
   view?_isNone_of_pack_length_gt length_pack_sigSign hle (by decide)⟩

/-- For any `t₀` and `msg₀` with `parseTrSignalMsg t₀ = some msg₀`, `notOpaqueHeaded msg₀.mac`
holds unconditionally. -/
theorem notOpaqueHeaded_mac_of_parseTrSignalMsg
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    notOpaqueHeaded msg₀.mac :=
  notOpaqueHeaded_of_length_le_8
    (parseTrSignalMsg_eq_some_concat_and_mac_length_le_8_tr32 hparse₀).2

end Symbolic.Swarm.CREF.TR.G1
