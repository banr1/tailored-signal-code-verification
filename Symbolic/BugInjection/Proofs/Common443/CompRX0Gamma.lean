/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
def coinHeads (es : List MachineEvent) : HwBytes := es.map fun e => (eventBytes e).headD 0
theorem gamma_of_kyberCoins {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {t : DY.Bytes} {es : List MachineEvent} (h : List.Forall₂ (EventMatchesEntry i r S g) es (kyberCoinEntries t)) : gamma i S g t = coinHeads es := by
  have hlen : es.length = 32 := by rw [h.length_eq]; simp [kyberCoinEntries]
  have hγlen : (gamma i S g t).length = 32 := by
    have h0 : 0 < es.length := by omega
    obtain ⟨hk, hm⟩ := (List.forall₂_iff_get.mp h).2 0 h0 (by rw [← h.length_eq]; exact h0); simp only [kyberCoinEntries, List.get_eq_getElem, List.getElem_map, List.getElem_range] at hm; obtain ⟨_, t', ht', hl, _⟩ := hm; cases ht'; exact hl
  apply List.ext_getElem?; intro j
  by_cases hj : j < 32
  · have hjes : j < es.length := by omega
    obtain ⟨_, hm⟩ := (List.forall₂_iff_get.mp h).2 j hjes (by rw [← h.length_eq]; exact hjes); simp only [kyberCoinEntries, List.get_eq_getElem, List.getElem_map, List.getElem_range] at hm; obtain ⟨hb4, t', ht', _, hhd⟩ := hm; cases ht'; rw [← hhd, coinHeads, List.getElem?_map, List.getElem?_eq_getElem hjes, Option.map_some]
    cases hb : eventBytes es[j] with
    | nil => rw [hb] at hb4; simp at hb4
    | cons x xs => rfl
  · rw [List.getElem?_eq_none (by omega), coinHeads, List.getElem?_eq_none (by simp; omega)]
theorem aliceVis_rng_coins {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun b₀ : HwBytes} {rs' : List MachineEvent} (hvis : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: .rng b₀ :: rs') (aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb)) : [gamma i S g (randTerm tr₁.length 32)] = [b₀] ∧ gamma i S g (randTerm (tr₁.length + 1) 32) = coinHeads (rs'.take 32) := by have hv : aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb = _ := aliceVis_iniAliceStartTr tr₁ a b o hb; rw [hv] at hvis; obtain ⟨_, hvis₁⟩ := List.forall₂_cons.mp hvis; obtain ⟨h₀, hrest⟩ := List.forall₂_cons.mp hvis₁; refine ⟨h₀.2, ?_⟩; have htk := List.forall₂_take 32 hrest; rw [List.take_left' (by simp [kyberCoinEntries])] at htk; exact gamma_of_kyberCoins htk
theorem gamma_iniAliceOut_ek_compI0 {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {b₀ : HwBytes} (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (h : [gamma compI0 S g (randTerm tr₁.length 32)] = [b₀]) : gamma compI0 S g (iniAliceOut tr₁ ikA ikB spk pqpk opk).ek = compLookupPub (clamp b₀) := by
  show gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = _
  rw [CompFreshDistinct.gamma_dhPk_compI0, (List.cons.inj h).1]
theorem gamma_iniAliceOut_ct {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (he : (gamma i S g (randTerm (tr₁.length + 1) 32)).length = 32) : gamma i S g (iniAliceOut tr₁ ikA ikB spk pqpk opk).ct = ((i kyberEncapsSymbol [gamma i S g pqpk, gamma i S g (randTerm (tr₁.length + 1) 32)]).getD []).take 1568 := by
  unfold gamma gamma' at he ⊢
  show ((({pk := pqpk, entropy := randTerm (tr₁.length + 1) 32} : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)]; simp only [gKemEncap, concretizeKemEncap, he, ↓reduceIte, node]
end Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
