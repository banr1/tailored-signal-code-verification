/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKIR
open CryptoProofLib.Refinement DY DY.Libsignal
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff QKdfInjRest)
def KirVal (v : HwBytes) : Prop := KdfFree v ∨ v.length ≠ 32
theorem kirVal_of_nonInjOff {v : HwBytes} (h : NonInjOff v) : KirVal v := if h32 : v.length = 32 then .inl (h.1 h32) else .inr h32
def Split40KirDraws (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop := KirVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧ KirVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧ (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 ∧ KirVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧ (gamma compI0 S g (randTerm tr₃.length 32)).length < 16 ∧ KirVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂))
section DecideKdfFree
set_option maxRecDepth 200000
theorem ws1_aliceId_kdfFree : KdfFree setup.aliceId := by decide +kernel
theorem ws1_bobId_kdfFree : KdfFree setup.bobId := by decide +kernel
theorem ws1_spk_kdfFree : KdfFree setup.spk := by decide +kernel
theorem compKyberE1_kdfFree : KdfFree compKyberE1 := by decide +kernel
end DecideKdfFree
theorem kdfFree_kemEncap_snd_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : KdfFree (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32]
  have h : compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] =
      some (compKyberEncaps (gamma compI0 S g e)) := rfl
  rw [h, Option.getD_some, he, show compKyberEncaps compKyberE1 = compKyberCt1 ++ compKyberSs1 by decide +kernel,
    List.drop_left' Census443Memo.kyberCtVals_lengths.2.1]
  decide +kernel
private theorem iniAliceOut_bridge (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : Census443Defs.iniAliceOut tr ikA ikBPk spkPk pqPk opk = CompPrefixInvAlice.iniAliceOut tr ikA ikBPk spkPk pqPk opk := rfl
private theorem iniAliceStartState_bridge (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Census443Defs.iniAliceStartState tr b o = CompPrefixInvAlice.iniAliceStartState tr b o := rfl
private theorem encSt_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : Census443Defs.encSt tr₂ stA cl = CompPrefixInvEnc.encSt tr₂ stA cl := rfl
private theorem encOut_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : Census443Defs.encOut tr₂ stA cl pq = CompPrefixInvEnc.encOut tr₂ stA cl pq := rfl
theorem kirc_prefixAtom40 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1) (hd : Split40KirDraws S g tr₁ tr₂ tr₃ cl₁ cl₂) {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : KdfInjRestCensus compI0 S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨h0, h5, h10, h16⟩ := CompC3KdfInjRest38HB.kirc_setup_of_compFits hfits.1 hc ws1_aliceId_kdfFree ws1_bobId_kdfFree ws1_spk_kdfFree; obtain ⟨hekV, hdhsV, hpt₁, hc₁V, hpt₂, hc₂V⟩ := hd; have hek := kirc_randTerm_of (i := compI0) hekV; have hent := kirc_randTerm_of (i := compI0) (.inl (hent₁.symm ▸ compKyberE1_kdfFree)); have hss := kdfFree_kemEncap_snd_of_e1 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₁
  have hc₁ := kirc_randTerm_of (i := compI0) hc₁V; have hc₂ := kirc_randTerm_of (i := compI0) hc₂V; have ho := kirc_aliceOut (r := r) hNe tr₁ h0 h5 h10 h16 hek hent hss; have hst₁ := trStateKIRC_stA hNe tr₁ h0 h5 h10 h16 hek hent hss (kirc_randTerm_of (i := compI0) hdhsV); have hst₁' := trStateKIRC_encSt tr₂ cl₁ hst₁ hc₁; unfold Split40PrefixAtom at hu; simp only [iniAliceOut_bridge, iniAliceStartState_bridge, encSt_bridge, encOut_bridge] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.2.2.2.1
  · exact ho.2.2.2.2.1
  · exact kirc_encOut_self tr₂ cl₁ hst₁ hpt₁ hc₁
  · exact kirc_encOut_self tr₃ cl₂ hst₁' hpt₂ hc₂
  · exact kirc_randTerm_of (.inr (by omega))
  · exact kirc_randTerm_of (.inr (by omega))
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁'
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) (trStateKIRC_encSt tr₃ cl₂ hst₁' hc₂)
theorem split40PreKIROwn_of_enum (hE : Split40PrefixEnum) (hD : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Split40KirDraws S g tr₁ tr₂ tr₃ cl₁ cl₂) : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x₁ ∈ preMemo40 r S g ms', ∀ x₂ ∈ preMemo40 r S g ms', x₁.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → x₂.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → QKdfInjRest S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (plaintextTerms (runVis r ms') ++ []) x₁ x₂ := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ _ x₂ hx₂ _ _; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₂
  exact qKdfInjRest_of_entry ((hE r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu).elim
    (fun ha => kirc_prefixAtom40 hfits hinv.compat hinv.hent₁
      (hD r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown) ha x₂ hxu)
    (fun hs => CompC3KdfInjRest38HB.kirc_storedSecrets_of_compFits hfits.1 hinv.compat
      ws1_aliceId_kdfFree ws1_bobId_kdfFree ws1_spk_kdfFree hinv.mp.2.1.2.1 hinv.reach u hs x₂ hxu))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKIR
