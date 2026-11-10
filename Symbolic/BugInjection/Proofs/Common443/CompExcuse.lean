/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompExcuse2
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompExcuse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
def IsKemSlotTerm (u z : DY.Bytes) : Prop := ∃ salt d dh1 dh2 dh3 rest, z = DY.Libsignal.TripleRatchet.hmac salt (DY.Concat.concat d (DY.Concat.concat dh1 (DY.Concat.concat dh2 (DY.Concat.concat dh3 rest)))) ∧ (u = rest ∨ ∃ dh4, rest = DY.Concat.concat dh4 u)
def KemSlot (i : ExternInterpretation) (S : Sem) (g : Ghost) (t u : DY.Bytes) : Prop := ∃ x ∈ (gamma' i S g t).memo, IsKemSlotTerm u x.1
def OnlyKemSlot (ss₀ : DY.Bytes) (i : ExternInterpretation) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := ∀ u, KemSlot i S g t u → u = ss₀
theorem concat_inj {a₁ b₁ a₂ b₂ : DY.Bytes} (h : DY.Concat.concat a₁ b₁ = DY.Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by have hv := congrArg (fun x : DY.Bytes => x.view? DY.Concat.Concat.SubF) h; simp only [DY.Concat.concat, DY.Concat.CanConcat.concat, DY.BytesView.view_pack, Option.some.injEq, DY.Concat.Concat.SubF.mk.injEq] at hv; exact hv
theorem hmac_inj {k₁ m₁ k₂ m₂ : DY.Bytes} (h : DY.Libsignal.TripleRatchet.hmac k₁ m₁ = DY.Libsignal.TripleRatchet.hmac k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.KdfExtract.KdfExtract.SubF) h; dsimp only [DY.Libsignal.TripleRatchet.hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract] at hv; rw [DY.BytesView.view_pack, DY.BytesView.view_pack] at hv
  injection hv with hv'
  cases hv'; exact ⟨rfl, rfl⟩
theorem view_concat_lit (b : ByteArray) : (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).view? DY.Concat.Concat.SubF = none :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.view_pack_none ({ lit := b } : DY.Literal.Literal.SubF DY.Bytes) (by decide)
theorem spqrRecv_spqrInit_spqrB2A_eq {pqr pq st' own : DY.Bytes} {idx : UInt32} (h : DY.Spqr.spqrRecv (DY.Spqr.spqrInit pqr DY.Libsignal.TripleRatchet.spqrB2A) pq idx = some (st', own)) : own = if idx = 0 then DY.Spqr.zeroKey else DY.Spqr.spqrChainKey pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx idx) :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.spqrRecv_spqrInit_spqrB2A_eq_bridge h
theorem not_bobOwnKeyMacGuess_of_idx_zero_or_one {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {ms : List Move} {p : PreKeyFields} {x : PreKeyRep} {keys : DY.Libsignal.PQXDH.HandshakeKeys} (hkeys : bobKeys r p x = some keys) (hidx : spqrIdx p = 0 ∨ (spqrIdx p = 1 ∧ DY.Spqr.spqrChainKey keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∈ honestSalts r ms)) : ¬ BobOwnKeyMacGuess i r S g known ms p x := by
  rintro ⟨keys₁, msg, seed, c', own, st', hkeys₁, _, _, _, hrecv, _, hne_all⟩
  rw [hkeys] at hkeys₁; injection hkeys₁ with hkeys_eq; subst hkeys_eq
  have hown := spqrRecv_spqrInit_spqrB2A_eq hrecv
  rcases hidx with h0 | ⟨h1, hmem1⟩
  · simp only [h0, ↓reduceIte] at hown; subst hown; exact hne_all DY.Spqr.zeroKey List.mem_cons_self rfl
  · simp only [h1, show (1 : UInt32) ≠ 0 by decide, ↓reduceIte] at hown; subst hown; exact hne_all _ hmem1 rfl
theorem gamma_concatPrefixes (i : ExternInterpretation) (S : Sem) (g : Ghost) : ∀ (ps : List DY.Bytes) (s : DY.Bytes), gamma i S g (Comparse.concatPrefixes ps s) = (ps.flatMap (gamma i S g)) ++ gamma i S g s
  | [], s => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]; rfl
  | p :: ps, s => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, gamma_concatPrefixes i S g ps s, List.flatMap_cons, List.append_assoc]
theorem concatPrefixes_append (ps₁ ps₂ : List DY.Bytes) (s : DY.Bytes) : Comparse.concatPrefixes ps₁ (Comparse.concatPrefixes ps₂ s) = Comparse.concatPrefixes (ps₁ ++ ps₂) s :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_append_eq ps₁ ps₂ s
theorem mem_memo_concatPrefixes {i : ExternInterpretation} {S : Sem} {g : Ghost} {x : DY.Bytes × DY.Bytes × HwBytes} : ∀ (ps : List DY.Bytes) (s : DY.Bytes), x ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo → (∃ p ∈ ps, x ∈ (gamma' i S g p).memo) ∨ x ∈ (gamma' i S g s).memo ∨ (assumedInjective x.1 = false ∧ (gamma i S g s).length ≤ x.2.2.length)
  | [], s, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil] at hx
    exact Or.inr (Or.inl hx)
  | p :: ps, s, hx => by
    have hx' : x ∈ (gamma' i S g (DY.Concat.concat p (Comparse.concatPrefixes ps s))).memo := by
      rwa [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons] at hx
    unfold gamma' at hx'; rw [show DY.Concat.concat p (Comparse.concatPrefixes ps s) = ({ lhs := p, rhs := Comparse.concatPrefixes ps s } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)] at hx'; dsimp only [gConcat0, concretizeConcat, node] at hx'; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append] at hx'
    rcases hx' with rfl | hxp | hx_rest
    · refine Or.inr (Or.inr ⟨Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq p (Comparse.concatPrefixes ps s), ?_⟩)
      show (gamma i S g s).length ≤ (gamma i S g p ++ gamma i S g (Comparse.concatPrefixes ps s)).length
      rw [gamma_concatPrefixes i S g ps s, List.length_append, List.length_append]; omega
    · exact Or.inl ⟨p, List.mem_cons_self, hxp⟩
    · rcases mem_memo_concatPrefixes ps s hx_rest with ⟨q, hq, hxq⟩ | hxs | hspine
      · exact Or.inl ⟨q, List.mem_cons_of_mem p hq, hxq⟩
      · exact Or.inr (Or.inl hxs)
      · exact Or.inr (Or.inr hspine)
def trStatePrefixes (ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : List DY.Bytes := Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++ (Comparse.NonExtensibleMessageFormat.slowString.serialize ls.state.peer ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.myIk ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.peerIk ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.rk ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.dhs ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.cks ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize ls.state.ns ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize ls.state.pn ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.sid ++ (Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.initiator ++ (Comparse.NonExtensibleMessageFormat.slowNat.serialize ls.state.rIdx ++ Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.spqr)))))))))))
end Symbolic.BugInjection.Proofs.Common443.CompExcuse
