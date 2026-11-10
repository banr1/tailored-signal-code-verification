/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreSalt
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc (encSalt_self)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
section Census
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem kdfCensus_spqrSendKey {st c : DY.Bytes} (hst : KdfCensus i S g st) (hc : KdfCensus i S g c) : KdfCensus i S g (DY.Spqr.spqrSend st c).2.1 := by
  unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => exact memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := memoOK_spqrInit_elim hst; exact kdfCensus_spqrChainKey hk hpar (kdfCensus_lit _)
private theorem iniAliceOut_bridge (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : Census443Defs.iniAliceOut tr ikA ikBPk spkPk pqPk opk = CompPrefixInvAlice.iniAliceOut tr ikA ikBPk spkPk pqPk opk := rfl
private theorem iniAliceStartState_bridge (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Census443Defs.iniAliceStartState tr b o = CompPrefixInvAlice.iniAliceStartState tr b o := rfl
private theorem encSt_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : Census443Defs.encSt tr₂ stA cl = CompPrefixInvEnc.encSt tr₂ stA cl := rfl
private theorem encOut_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : Census443Defs.encOut tr₂ stA cl pq = CompPrefixInvEnc.encOut tr₂ stA cl pq := rfl
theorem kdfCensus_encOut_self (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateKC i S g stA) : KdfCensus i S g (CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)) := by
  refine kdfCensus_encOut tr₂ cl _ hst ?_ ?_ <;> rw [encSalt_self]
  · exact WsIdx1Split40OwnSalt.gamma_spqrSendKey_length _ _
  · exact kdfCensus_spqrSendKey hst.spqr (kdfCensus_randTerm _ _)
theorem kdfCensus_prefixAtom40 {r : Records} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : KdfCensus i S g u := by
  unfold Split40PrefixAtom at hu; simp only [iniAliceOut_bridge, iniAliceStartState_bridge, encSt_bridge, encOut_bridge] at hu; have ho := kdfCensus_aliceOut (i := i) (S := S) (g := g) (r := r) hNe tr₁; have hst₁ := trStateKC_stA_split38 (i := i) (S := S) (g := g) hNe tr₁; have hst₁' := trStateKC_encSt tr₂ cl₁ hst₁
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.2.2.2.1
  · exact ho.2.2.2.2.1
  · exact kdfCensus_encOut_self tr₂ cl₁ hst₁
  · exact kdfCensus_encOut_self tr₃ cl₂ hst₁'
  · exact kdfCensus_randTerm _ _
  · exact kdfCensus_randTerm _ _
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁'
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) (trStateKC_encSt tr₃ cl₂ hst₁')
end Census
theorem split40PreSalt32Own_of_enum (hE : Split40PrefixEnum) : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms', KdfSalt32 S g x := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  exact (hE r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu).elim
    (fun ha => kdfCensus_prefixAtom40 hfits.1.1.1 ha x hxu)
    (fun hs => kdfCensus_storedSecrets_of_reachable hinv.reach u hs x hxu)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreSalt
