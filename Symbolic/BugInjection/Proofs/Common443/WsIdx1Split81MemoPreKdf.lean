/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnA
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreSalt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKIR
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.Specifications.Concrete.ByteSpecs
public import Symbolic.Specifications.Concrete.ExternInterpretation
public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public meta import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins
public meta import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Common443.CompRTag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public meta import Symbolic.Specifications.Concrete.ByteSpecs
public meta import Symbolic.Specifications.Concrete.ExternInterpretation
public meta import Symbolic.Specifications.Refinement.TraceExplanation

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreKdf
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreSalt Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKIR Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff QKdfInjRest)
section SaltCensus81
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem kdfCensus_spqrRecv_state {st msg : DY.Bytes} {idx : UInt32} {st' : DY.Bytes} (hst : KdfCensus i S g st) (hm : KdfCensus i S g msg) (h : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some st') : KdfCensus i S g st' := by
  rcases hres : DY.Spqr.spqrRecv st msg idx with _ | res <;> rw [hres] at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h; subst h
    rw [DY.Spqr.spqrRecv_state st msg idx res hres]; exact memoOK_spqrRecvState_pack hst hm
private theorem iniAliceOut_bridge (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : Census443Defs.iniAliceOut tr ikA ikBPk spkPk pqPk opk = CompPrefixInvAlice.iniAliceOut tr ikA ikBPk spkPk pqPk opk := rfl
private theorem iniAliceStartState_bridge (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Census443Defs.iniAliceStartState tr b o = CompPrefixInvAlice.iniAliceStartState tr b o := rfl
private theorem encSt_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : Census443Defs.encSt tr₂ stA cl = CompPrefixInvEnc.encSt tr₂ stA cl := rfl
private theorem encOut_bridge (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : Census443Defs.encOut tr₂ stA cl pq = CompPrefixInvEnc.encOut tr₂ stA cl pq := rfl
theorem trStateKC_bobSt81 {r : Records} (hNe : r.alice ≠ r.bob)
    {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {cl₁ cl₂ : Nat} {spqrMsgIdx₂ : UInt32} {spqr₂' : DY.Bytes}
    (hspqr : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (CompPrefixInvEnc.encSt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    TRStateKC i S g (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1) := by
  dsimp only
  have ho₁ := kdfCensus_aliceOut (i := i) (S := S) (g := g) (r := r) hNe tr₁
  have hst₁ := trStateKC_stA_split38 (i := i) (S := S) (g := g) hNe tr₁
  have hst₁' := trStateKC_encSt tr₂ cl₁ hst₁
  have hrt₂ := kdfCensus_dhPk hst₁.dhs
  have hsec2 : KdfCensus i S g (setupSecret r 2) := by
    rw [CompSetupSecrecy.setupSecret_2 hNe]; exact kdfCensus_randTerm _ _
  have hcc1 := kdfCensus_createChain (aliceOut_rk_length tr₁ _ _ _ _ _) ho₁.2.2.2.2.2.1 hrt₂ hsec2
  have hdhsB : KdfCensus i S g (randTerm tr_bob.length 32) := kdfCensus_randTerm _ _
  have hcc2 := kdfCensus_createChain (CompFreshDistinct.gamma_hmac_length S g _ _) hcc1.1 hrt₂ hdhsB
  have hck1' := (kdfCensus_kdfCk (CompRSplit38Untagged.gamma_createChain_snd_length S g _ _ _) hcc1.2).1
  have hck1'' := (kdfCensus_kdfCk (CompFreshDistinct.gamma_hmac_length S g _ _) hck1').1
  refine {
    myIk := hst₁.peerIk, rk := hcc2.1, dhs := hdhsB, cks := hcc2.2
    peerIk := by
      dsimp only [bobSt81]; rw [show DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = _ by
        change _ = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0))
        rw [CompSetupSecrecy.setupPublic_0 hNe, CompSetupSecrecy.setupSecret_0 hNe]]; exact hst₁.myIk
    sid := kdfCensus_concat (kdfCensus_x25519Key hrt₂) ho₁.2.2.2.2.2.1
    spqr := kdfCensus_spqrRecv_state (kdfCensus_spqrInit ho₁.2.2.2.2.2.2.2 (kdfCensus_lit _)) (kdfCensus_spqrSendMsg hst₁'.spqr (kdfCensus_randTerm _ _)) hspqr
    recv := fun d hd => by simp only [bobSt81, List.mem_singleton] at hd; subst hd; exact ⟨hrt₂, hck1''⟩
    cksL := CompRSplit38Untagged.gamma_createChain_snd_length S g _ _ _ }
theorem kdfCensus_prefixAtom81 {r : Records} {S' : Sem} {g' : Ghost} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {u : DY.Bytes} (hu : Split81PrefixAtom r S' g' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ u) : KdfCensus i S g u := by
  unfold Split81PrefixAtom at hu; simp only [iniAliceOut_bridge, iniAliceStartState_bridge, encSt_bridge, encOut_bridge] at hu; have ho₁ := kdfCensus_aliceOut (i := i) (S := S) (g := g) (r := r) hNe tr₁; have hst₁ := trStateKC_stA_split38 (i := i) (S := S) (g := g) hNe tr₁; have hst₁' := trStateKC_encSt tr₂ cl₁ hst₁; have hst₁'' := trStateKC_encSt tr₃ cl₂ hst₁'; have ho₂ := kdfCensus_aliceOut (i := i) (S := S) (g := g) (r := r) hNe tr₄
  have hst₂ := trStateKC_stA_split38 (i := i) (S := S) (g := g) hNe tr₄; have hst₂' := trStateKC_encSt tr₅ cl₅ hst₂
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', _, hspqr, rfl⟩
  · exact ho₁.2.2.2.1
  · exact ho₁.2.2.2.2.1
  · exact kdfCensus_encOut_self tr₂ cl₁ hst₁
  · exact kdfCensus_encOut_self tr₃ cl₂ hst₁'
  · exact ho₂.2.2.2.1
  · exact ho₂.2.2.2.2.1
  · exact kdfCensus_encOut_self tr₅ cl₅ hst₂
  · exact kdfCensus_randTerm _ _
  · exact kdfCensus_randTerm _ _
  · exact kdfCensus_randTerm _ _
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁'
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁''
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂'
  · exact kdfCensus_serialize_local_tr (ls := ⟨r.bob, _⟩) (trStateKC_bobSt81 hNe hspqr)
end SaltCensus81
theorem split81PreSalt32Own_of_enum (hE : Split81PrefixEnum) : Split81PreSalt32Own := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  rcases hE r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu with ha | hs
  · exact kdfCensus_prefixAtom81 hfits.1.1.1 ha x hxu
  · exact kdfCensus_storedSecrets_of_reachable hinv.reach u hs x hxu
def Split81KirDraws (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop := KirVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧ KirVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧ (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 ∧ KirVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧ (gamma compI0 S g (randTerm tr₃.length 32)).length < 16 ∧ KirVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)) ∧ KirVal (gamma compI0 S g (randTerm tr₄.length 32)) ∧ KirVal (gamma compI0 S g (randTerm (tr₄.length + 2) 32)) ∧ (gamma compI0 S g (randTerm tr₅.length 32)).length < 16 ∧ KirVal (gamma compI0 S g (randTerm (tr₅.length + 1) cl₅))
def Split81DrawPins' (_r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop := CompC2RestR38.RVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)) ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm tr₄.length 32)) ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm (tr₄.length + 2) 32)) ∧ gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3 ∧ CompC2RestR38.RVal (gamma compI0 S g (randTerm (tr₅.length + 1) cl₅))
def Split81DrawPinsOwn' : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Split81DrawPins' r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
theorem kirDraws81_of_drawPins {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (h : Split81DrawPins' r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : Split81KirDraws S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨kirVal_of_nonInjOff h1.1, kirVal_of_nonInjOff h2.1, by rw [h3]; decide +kernel,
    kirVal_of_nonInjOff h4.1, by rw [h5]; decide +kernel, kirVal_of_nonInjOff h6.1,
    kirVal_of_nonInjOff h7.1, kirVal_of_nonInjOff h8.1, by rw [h9]; decide +kernel,
    kirVal_of_nonInjOff h10.1⟩
set_option maxRecDepth 200000 in theorem compKyberE2_kdfFree : KdfFree compKyberE2 := by decide +kernel
set_option maxRecDepth 200000 in theorem compKyberSs2_kdfFree : KdfFree compKyberSs2 := by decide +kernel
set_option maxRecDepth 200000 in theorem bobRng41Bytes_kdfFree : KdfFree bobRng41Bytes := by unfold KdfFree bobRng41Bytes; decide +kernel
theorem kdfFree_kemEncap_snd_of_e2 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : KdfFree (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by rw [WsIdx1Split81MemoVals.gamma_kemEncap_snd_of_e2 he]; exact compKyberSs2_kdfFree
theorem trStateKIRC_bobSt81 {r : Records} {S : Sem} {g : Ghost}
    (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {cl₁ cl₂ : Nat} {spqrMsgIdx₂ : UInt32} {spqr₂' : DY.Bytes}
    (h0 : KdfInjRestCensus compI0 S g (randTerm 0 32)) (h5 : KdfInjRestCensus compI0 S g (randTerm 5 32))
    (h10 : KdfInjRestCensus compI0 S g (randTerm 10 32)) (h16 : KdfInjRestCensus compI0 S g (randTerm 16 64))
    (hek : KdfInjRestCensus compI0 S g (randTerm tr₁.length 32)) (hent : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32))
    (hss : KdfFree (gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2))
    (hdhs : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 2) 32))
    (hc₁ : KdfInjRestCensus compI0 S g (randTerm (tr₂.length + 1) cl₁))
    (hc₂ : KdfInjRestCensus compI0 S g (randTerm (tr₃.length + 1) cl₂))
    (hbob : KdfInjRestCensus compI0 S g (randTerm tr_bob.length 32))
    (hspqr : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (CompPrefixInvEnc.encSt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    TRStateKIRC compI0 S g (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1) := by
  dsimp only
  have ho₁ := kirc_aliceOut hNe tr₁ h0 h5 h10 h16 hek hent hss
  have hst₁ := trStateKIRC_stA hNe tr₁ h0 h5 h10 h16 hek hent hss hdhs
  have hst₁' := trStateKIRC_encSt tr₂ cl₁ hst₁ hc₁
  have hrt₂ := kirc_dhPk hst₁.dhs
  have hsec2 : KdfInjRestCensus compI0 S g (setupSecret r 2) := by rw [CompSetupSecrecy.setupSecret_2 hNe]; exact h10
  have hcc1 := kirc_createChain ho₁.2.2.2.2.2.1 hrt₂ hsec2
  have hcc2 := kirc_createChain hcc1.1 hrt₂ hbob
  refine {
    myIk := hst₁.peerIk
    peerIk := by
      dsimp only [bobSt81]
      rw [show DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = _ by
        change _ = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0))
        rw [CompSetupSecrecy.setupPublic_0 hNe, CompSetupSecrecy.setupSecret_0 hNe]]
      exact hst₁.myIk
    rk := hcc2.1, dhs := hbob, cks := hcc2.2
    sid := kirc_concat (kirc_x25519Key hrt₂) ho₁.2.2.2.2.2.1
    spqr := kirc_spqrRecv_state (kirc_spqrInit ho₁.2.2.2.2.2.2.2 (kirc_lit _)) (kirc_spqrSendMsg hst₁'.spqr hc₂) hspqr
    recv := fun d hd => by
      simp only [bobSt81, List.mem_singleton] at hd; subst hd
      exact ⟨hrt₂, (kirc_kdfCk (kirc_kdfCk hcc1.2).1).1⟩ }
theorem kirc_prefixAtom81 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1) (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) (hd : Split81KirDraws S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {u : DY.Bytes} (hu : Split81PrefixAtom r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ u) : KdfInjRestCensus compI0 S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨h0, h5, h10, h16⟩ := CompC3KdfInjRest38HB.kirc_setup_of_compFits hfits.1 hc ws1_aliceId_kdfFree ws1_bobId_kdfFree ws1_spk_kdfFree; obtain ⟨hek₁V, hdhs₁V, hpt₁, hc₁V, hpt₂, hc₂V, hek₂V, hdhs₂V, hpt₅, hc₅V⟩ := hd; have hek₁ := kirc_randTerm_of (i := compI0) hek₁V
  have hent₁C : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32) := kirc_randTerm_of (.inl (by rw [hent₁]; exact compKyberE1_kdfFree))
  have hss₁ := kdfFree_kemEncap_snd_of_e1 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₁; have hdhs₁ := kirc_randTerm_of (i := compI0) hdhs₁V; have hc₁ := kirc_randTerm_of (i := compI0) hc₁V; have hc₂ := kirc_randTerm_of (i := compI0) hc₂V; have hek₂ := kirc_randTerm_of (i := compI0) hek₂V
  have hent₂C : KdfInjRestCensus compI0 S g (randTerm (tr₄.length + 1) 32) := kirc_randTerm_of (.inl (by rw [hent₂]; exact compKyberE2_kdfFree))
  have hss₂ := kdfFree_kemEncap_snd_of_e2 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₂; have hdhs₂ := kirc_randTerm_of (i := compI0) hdhs₂V; have hc₅ := kirc_randTerm_of (i := compI0) hc₅V; have ho₁ := kirc_aliceOut (r := r) hNe tr₁ h0 h5 h10 h16 hek₁ hent₁C hss₁; have hst₁ := trStateKIRC_stA hNe tr₁ h0 h5 h10 h16 hek₁ hent₁C hss₁ hdhs₁; have hst₁' := trStateKIRC_encSt tr₂ cl₁ hst₁ hc₁; have hst₁'' := trStateKIRC_encSt tr₃ cl₂ hst₁' hc₂
  have ho₂ := kirc_aliceOut (r := r) hNe tr₄ h0 h5 h10 h16 hek₂ hent₂C hss₂; have hst₂ := trStateKIRC_stA hNe tr₄ h0 h5 h10 h16 hek₂ hent₂C hss₂ hdhs₂; have hst₂' := trStateKIRC_encSt tr₅ cl₅ hst₂ hc₅; unfold Split81PrefixAtom at hu; simp only [iniAliceOut_bridge, iniAliceStartState_bridge, encSt_bridge, encOut_bridge] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', hbob_pin, hspqr, rfl⟩
  · exact ho₁.2.2.2.1
  · exact ho₁.2.2.2.2.1
  · exact kirc_encOut_self tr₂ cl₁ hst₁ hpt₁ hc₁
  · exact kirc_encOut_self tr₃ cl₂ hst₁' hpt₂ hc₂
  · exact ho₂.2.2.2.1
  · exact ho₂.2.2.2.2.1
  · exact kirc_encOut_self tr₅ cl₅ hst₂ hpt₅ hc₅
  · exact kirc_randTerm_of (.inr (by omega))
  · exact kirc_randTerm_of (.inr (by omega))
  · exact kirc_randTerm_of (.inr (by omega))
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁'
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁''
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂
  · exact kirc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂'
  · exact kirc_serialize_local_tr (ls := ⟨r.bob, _⟩) (trStateKIRC_bobSt81 hNe h0 h5 h10 h16 hek₁ hent₁C hss₁ hdhs₁ hc₁ hc₂
      (kirc_randTerm_of (.inl (by rw [hbob_pin]; exact bobRng41Bytes_kdfFree))) hspqr)
theorem split81PreKIROwn_of_enum_draws (hE : Split81PrefixEnum) (hD : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Split81KirDraws S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : Split81PreKIROwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; dsimp only; intro x₁ _ x₂ hx₂ _ _; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₂
  have hcen : KdfInjRestCensus compI0 S g u := by
    rcases hE r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu with ha | hs
    · exact kirc_prefixAtom81 hfits hinv.compat hinv.hent₁ hinv.hent₂ (hD r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown) ha
    · exact CompC3KdfInjRest38HB.kirc_storedSecrets_of_compFits hfits.1 hinv.compat ws1_aliceId_kdfFree ws1_bobId_kdfFree ws1_spk_kdfFree hinv.mp.2.1.2.1 hinv.reach u hs
  exact qKdfInjRest_of_entry (hcen x₂ hxu)
theorem split81PreKIROwn_of_enum (hE : Split81PrefixEnum) (hD : Split81DrawPinsOwn') : Split81PreKIROwn := split81PreKIROwn_of_enum_draws hE (fun r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown => kirDraws81_of_drawPins (hD r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown))
theorem agree_bob_chain1_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2) =
      DY.Libsignal.PQXDH.agree o₁.spk (randTerm (tr₁.length + 2) 32) := by
  dsimp only [CompPrefixInvAlice.iniAliceStartState, CompPrefixInvAlice.iniAliceOut]
  rw [CompSetupSecrecy.setupSecret_2 hNe, CompSetupSecrecy.setupPublic_4 hNe]
  exact Symbolic.Swarm.COMPOSED.CompTermAlgebra.agree_comm (randTerm (tr₁.length + 2) 32) (randTerm 10 32)
theorem createChain_eq_kdfRk_agree (rk pk sk : DY.Bytes) : DY.Libsignal.TripleRatchet.createChain rk pk sk = DY.Libsignal.TripleRatchet.kdfRk rk (DY.Libsignal.PQXDH.agree pk sk) := rfl
theorem createChain_bob_chain1_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2) =
      DY.Libsignal.TripleRatchet.createChain o₁.keys.rk o₁.spk (randTerm (tr₁.length + 2) 32) := by
  dsimp only; rw [createChain_eq_kdfRk_agree, createChain_eq_kdfRk_agree, agree_bob_chain1_eq hNe tr₁]
open Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK
theorem peerIk_bob_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = (stA38 r tr₁).myIk := by change _ = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0)); rw [CompSetupSecrecy.setupPublic_0 hNe, CompSetupSecrecy.setupSecret_0 hNe]
attribute [local irreducible] setupSecret setupPublic setupTrace
theorem createChain_bob_chain1_fst_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (setupSecret r 2)).1 = (stA38 r tr₁).rk := congrArg Prod.fst (createChain_bob_chain1_eq hNe tr₁)
theorem createChain_bob_chain1_snd_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (setupSecret r 2)).2 = (stA38 r tr₁).cks := congrArg Prod.snd (createChain_bob_chain1_eq hNe tr₁)
theorem chainKeyAt_one (ck : DY.Bytes) : DY.Libsignal.TripleRatchet.chainKeyAt ck (1 : UInt32).toNat = (DY.Libsignal.TripleRatchet.kdfCk ck).1 := rfl
def bob3Node3 (r : Records) (tr₁ tr_bob : ExecTrace) : Fin 3 → DY.Bytes :=
  let o₁ := o38 r tr₁; let stA₁ := stA38 r tr₁
  let rt₂ := DY.DiffieHellman.dhPk stA₁.dhs
  let rk1 := (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk rt₂ (setupSecret r 2)).1
  let dhsB := randTerm tr_bob.length 32
  fun
  | ⟨0, _⟩ => DY.Libsignal.TripleRatchet.hmac rk1 (DY.Libsignal.PQXDH.agree rt₂ dhsB)
  | ⟨1, _⟩ => (DY.Libsignal.TripleRatchet.createChain rk1 rt₂ dhsB).1
  | ⟨2, _⟩ => (DY.Libsignal.TripleRatchet.createChain rk1 rt₂ dhsB).2
structure NodesBob3 (P : DY.Bytes → Prop) (r : Records) (tr₁ tr_bob : ExecTrace) : Prop where
  prk2 : P (bob3Node3 r tr₁ tr_bob ⟨0, by decide⟩)
  rk2 : P (bob3Node3 r tr₁ tr_bob ⟨1, by decide⟩)
  cks : P (bob3Node3 r tr₁ tr_bob ⟨2, by decide⟩)
theorem kc_spqrRecv_state {S : Sem} {g : Ghost} {P : DY.Bytes → Prop} {st msg : DY.Bytes} {idx : UInt32} {st' : DY.Bytes} (hst : KC S g P st) (hm : KC S g P msg) (h : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some st') : KC S g P st' := by
  rcases hres : DY.Spqr.spqrRecv st msg idx with _ | res <;> rw [hres] at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h; subst h
    rw [DY.Spqr.spqrRecv_state st msg idx res hres]; exact CompRMemoKnown.memoOK_spqrRecvState_pack hst hm
theorem kc_createChain_step {S : Sem} {g : Ghost} {P : DY.Bytes → Prop} {rk pk sk : DY.Bytes} (hprk : P (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk))) (hrk' : P (DY.Libsignal.TripleRatchet.createChain rk pk sk).1) (hck' : P (DY.Libsignal.TripleRatchet.createChain rk pk sk).2) (hrk : KC S g P rk) (hpk : KC S g P pk) (hsk : KC S g P sk) : KC S g P (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ KC S g P (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hp := kc_kdfExtract hprk hrk (kc_agree hpk hsk); exact ⟨kc_hkdfBlock1 hrk' hp (kc_lit _), kc_hkdfBlock2 hrk' hck' hp (kc_lit _)⟩
theorem trStateP_bobSt81 {S : Sem} {g : Ghost} {P : DY.Bytes → Prop} {r : Records} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {cl₁ cl₂ : Nat} {spqrMsgIdx₂ : UInt32} {spqr₂' : DY.Bytes} (hN₁ : Nodes38 P r tr₁ tr₂ cl₁) (hN₂ : Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂) (hNB : NodesBob3 P r tr₁ tr_bob) (hspqr : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (o38 r tr₁).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (CompPrefixInvEnc.encSt tr₂ (stA38 r tr₁) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') : TRStateP S g P (bobSt81 r (o38 r tr₁) tr_bob (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) spqr₂' 1) := by
  have ho₁ := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁ := trStateP_stA38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁' := trStateP_encSt38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁'' := trStateP_encSt40 (S := S) (g := g) hNe tr₁ tr₂ tr₃ cl₁ cl₂ hN₁ hN₂; have hrt₂ : KC S g P (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) := kc_dhPk hst₁.dhs
  have hrk1 : KC S g P (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (setupSecret r 2)).1 := by rw [createChain_bob_chain1_fst_eq hNe tr₁]; exact hst₁.rk
  have hcc2 := kc_createChain_step hNB.prk2 hNB.rk2 hNB.cks hrk1 hrt₂ (kc_randTerm _ _)
  refine {
    myIk := hst₁.peerIk
    peerIk := by dsimp only [bobSt81]; rw [peerIk_bob_eq hNe tr₁]; exact hst₁.myIk
    rk := hcc2.1, dhs := kc_randTerm _ _, cks := hcc2.2
    sid := kc_concat (kc_x25519Key hrt₂) ho₁.2.2.2.2.2.1
    spqr := kc_spqrRecv_state (kc_spqrInit ho₁.2.2.2.2.2.2.2 (kc_lit _)) (kc_spqrSendMsg hst₁'.spqr (kc_randTerm _ _)) hspqr
    recv := fun d hd => by
      simp only [bobSt81, List.mem_singleton] at hd; subst hd
      refine ⟨hrt₂, ?_⟩; dsimp only [bobSt81]
      rw [chainKeyAt_one, createChain_bob_chain1_snd_eq hNe tr₁]; exact hst₁''.cks }
theorem kc_prefixAtom81_at {S : Sem} {g : Ghost} {P : DY.Bytes → Prop} {r : Records} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hN₁ : Nodes38 P r tr₁ tr₂ cl₁) (hN₂ : Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂) (hN₄ : Nodes38 P r tr₄ tr₅ cl₅) (hNB : NodesBob3 P r tr₁ tr_bob) {u : DY.Bytes} (hu : WsIdx1Split81MemoRestFnA.Split81PrefixAtomAt r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u) : KC S g P u := by
  have ho₁ := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁ := trStateP_stA38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁' := trStateP_encSt38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have hst₁'' := trStateP_encSt40 (S := S) (g := g) hNe tr₁ tr₂ tr₃ cl₁ cl₂ hN₁ hN₂; have henc₁ := kc_encOut38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; have henc₂ := kc_encOut40_2 (S := S) (g := g) hNe tr₁ tr₂ tr₃ cl₁ cl₂ hN₁ hN₂
  have ho₂ := kc_aliceOut (S := S) (g := g) hNe tr₄ tr₅ cl₅ hN₄; have hst₂ := trStateP_stA38 (S := S) (g := g) hNe tr₄ tr₅ cl₅ hN₄; have hst₂' := trStateP_encSt38 (S := S) (g := g) hNe tr₄ tr₅ cl₅ hN₄; have henc₅ := kc_encOut38 (S := S) (g := g) hNe tr₄ tr₅ cl₅ hN₄; unfold WsIdx1Split81MemoRestFnA.Split81PrefixAtomAt WsIdx1Prefix81Enum.Split81PrefixAtomGen at hu; dsimp only at hu; rw [iniAliceOut_bridge, iniAliceStartState_bridge, encSt_bridge, encOut_bridge] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨spqrMsgIdx₂, spqr₂', hspqr, rfl⟩
  · exact ho₁.2.2.2.1
  · exact ho₁.2.2.2.2.1
  · exact henc₁
  · exact henc₂
  · exact ho₂.2.2.2.1
  · exact ho₂.2.2.2.2.1
  · exact henc₅
  · exact kc_randTerm _ _
  · exact kc_randTerm _ _
  · exact kc_randTerm _ _
  · exact kc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁
  · exact kc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁'
  · exact kc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₁''
  · exact kc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂
  · exact kc_serialize_local_tr (ls := ⟨r.alice, _⟩) hst₂'
  · exact kc_serialize_local_tr (ls := ⟨r.bob, _⟩) (trStateP_bobSt81 hNe hN₁ hN₂ hNB hspqr)
theorem kdfP_extChainRows81 {S : Sem} {g : Ghost} {P : DY.Bytes → Prop} {r : Records} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₄ tr₅ : ExecTrace} {cl₁ cl₅ : Nat} (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) (hN₄ : Nodes38 P r tr₄ tr₅ cl₅) (hBC : ∀ u ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁, P u) {x : Row} (hx : x ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁) : KdfP P x := by
  have ho₂ := kc_aliceOut (S := S) (g := g) hNe tr₄ tr₅ cl₅ hN₄
  rcases extChainRows81_cases r S g tr₁ tr₂ tr₄ cl₁ hent₂ hx with hek | hct | ⟨u, hu, rfl⟩
  · exact ho₂.2.2.2.1 x hek
  · exact ho₂.2.2.2.2.1 x hct
  · intro _ _ _; exact hBC u hu
def wsVal13_S2 : Fin 13 → HwBytes
  | ⟨0, _⟩ => wsPqxdhPrk4 | ⟨1, _⟩ => wsRk4 | ⟨2, _⟩ => wsPqxdhCk4 | ⟨3, _⟩ => wsPqxdhPqr4
  | ⟨4, _⟩ => wsChainPrk4 | ⟨5, _⟩ => wsStARk4 | ⟨6, _⟩ => wsCks4 | ⟨7, _⟩ => wsCks5
  | ⟨8, _⟩ => WsIdx1O4Tag.wsSeed5 | ⟨9, _⟩ => WsIdx1O4Tag.ws5Prk | ⟨10, _⟩ => wsCipherKey5
  | ⟨11, _⟩ => WsIdx1O4Tag.ws5MacKey | ⟨12, _⟩ => wsIv5Full
def bobChainNode5 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : Fin 5 → DY.Bytes :=
  let keys₂ := bobStartKeys r (x81Idx1 r tr₁ tr₂ tr₄ cl₁)
  let rt₁ := DY.DiffieHellman.dhPk (stA81 r tr₁).dhs
  let ck₀ := bobChainCk0 r keys₂.rk rt₁
  fun
  | ⟨0, _⟩ => DY.Libsignal.TripleRatchet.hmac keys₂.rk (DY.Libsignal.PQXDH.agree rt₁ (setupSecret r 2))
  | ⟨1, _⟩ => (DY.Libsignal.TripleRatchet.createChain keys₂.rk rt₁ (setupSecret r 2)).1
  | ⟨2, _⟩ => ck₀
  | ⟨3, _⟩ => (DY.Libsignal.TripleRatchet.kdfCk ck₀).1
  | ⟨4, _⟩ => (DY.Libsignal.TripleRatchet.kdfCk ck₀).2
def wsVal5BobChain : Fin 5 → HwBytes
  | ⟨0, _⟩ => ws6_bob_prk | ⟨1, _⟩ => ws6_bob_rk1 | ⟨2, _⟩ => ws6_bob_ck0
  | ⟨3, _⟩ => ws6_bob_ck1 | ⟨4, _⟩ => WsIdx1O4Tag.wsSeed6
def wsAliceRatchetPk1 : HwBytes := eval_hwbytes81 (((parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvFast).map (fun p => p.inner.senderRatchetKey.bytes.toList)).getD [])
def wsBob3_agree : HwBytes := eval_hwbytes81 (compLookupDh (clamp bobRng41Bytes) wsAliceRatchetPk1)
def wsBob3_prk2 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsStARk0 wsBob3_agree)
def wsBob3_rk2 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wratInfoLit ++ [1#8]))
def wsBob3_cks : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wsBob3_rk2 ++ (wratInfoLit ++ [2#8])))
def wsVal3Bob3 : Fin 3 → HwBytes
  | ⟨0, _⟩ => wsBob3_prk2 | ⟨1, _⟩ => wsBob3_rk2 | ⟨2, _⟩ => wsBob3_cks
def wsVal40_81 (k : Fin 40) : HwBytes :=
  if h1 : k.val < 13 then wsVal13 ⟨k.val, h1⟩
  else if h2 : k.val < 19 then wsVal6Msg2 ⟨k.val - 13, by omega⟩
  else if h3 : k.val < 32 then wsVal13_S2 ⟨k.val - 19, by omega⟩
  else if h4 : k.val < 37 then wsVal5BobChain ⟨k.val - 32, by omega⟩
  else wsVal3Bob3 ⟨k.val - 37, by omega⟩
def wsMacKey3_81 : Fin 3 → HwBytes
  | ⟨0, _⟩ => WsIdx1O4Tag.ws1MacKey | ⟨1, _⟩ => WsIdx1O4Tag.ws2MacKey | ⟨2, _⟩ => WsIdx1O4Tag.ws5MacKey
set_option maxRecDepth 200000 in theorem wsVal40_81_inj_decide : ∀ i j : Fin 40, wsVal40_81 i = wsVal40_81 j → i = j := by decide +kernel
theorem wsVal40_81_inj {i j : Fin 40} (h : wsVal40_81 i = wsVal40_81 j) : i = j := wsVal40_81_inj_decide i j h
set_option maxRecDepth 200000 in theorem wsVal40_81_keyOfTake8_ne : ∀ (i : Fin 40) (m : Fin 3), SP.keyOfTake8 ((wsVal40_81 i).take 8) ≠ some (wsMacKey3_81 m) := by decide +kernel
set_option maxRecDepth 200000 in theorem wsMacKey3_81_inj_decide : ∀ m₁ m₂ : Fin 3, (some (wsMacKey3_81 m₁) : Option HwBytes) = some (wsMacKey3_81 m₂) → m₁ = m₂ := by decide +kernel
theorem wsMacKey3_81_inj {m₁ m₂ : Fin 3} (h : (some (wsMacKey3_81 m₁) : Option HwBytes) = some (wsMacKey3_81 m₂)) : m₁ = m₂ := wsMacKey3_81_inj_decide m₁ m₂ h
set_option maxRecDepth 200000 in
theorem wsBob3_forward :
    compLookupDh (clamp bobRng41Bytes) wsAliceRatchetPk1 = wsBob3_agree ∧
    hmacWith WsIdx1O4Tag.F0 wsStARk0 wsBob3_agree = wsBob3_prk2 ∧
    hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wratInfoLit ++ [1#8]) = wsBob3_rk2 ∧
    hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wsBob3_rk2 ++ (wratInfoLit ++ [2#8])) = wsBob3_cks := by decide +kernel
open Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38PC2_S1 (node13Gen macNode38Gen encPrk_eq_kdfExtract_ini encKeys_eq_trMsgKeys_ini)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK (node6Msg2Gen macNode40Msg2Gen wsVal13 wsVal6Msg2)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin (gamma_bobSeed81)
def node40_81 (r : Records) (tr₁ tr₂ tr₃ tr_bob tr₄ : ExecTrace) (cl₁ cl₂ : Nat) (k : Fin 40) : DY.Bytes :=
  if h1 : k.val < 13 then node13Gen tr₁ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨k.val, h1⟩
  else if h2 : k.val < 19 then node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨k.val - 13, by omega⟩
  else if h3 : k.val < 32 then node13Gen tr₄ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨k.val - 19, by omega⟩
  else if h4 : k.val < 37 then bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨k.val - 32, by omega⟩
  else bob3Node3 r tr₁ tr_bob ⟨k.val - 37, by omega⟩
def macNode3_81 (r : Records) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Fin 3 → DY.Bytes
  | ⟨0, _⟩ => macNode38Gen tr₁ tr₂ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁
  | ⟨1, _⟩ => macNode40Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂
  | ⟨2, _⟩ => macNode38Gen tr₄ tr₅ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₅
def WsNodePin81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (t : DY.Bytes) : Prop := (∃ k : Fin 40, t = node40_81 r tr₁ tr₂ tr₃ tr_bob tr₄ cl₁ cl₂ k ∧ gamma compI0 S g t = wsVal40_81 k) ∨ (∃ m : Fin 3, t = macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ m ∧ SP.keyOfTake8 ((gamma compI0 S g t).take 8) = some (wsMacKey3_81 m))
theorem wsNodePin81_inj {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {t₁ t₂ : DY.Bytes} (h₁ : WsNodePin81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ t₁) (h₂ : WsNodePin81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ t₂) (he : gamma compI0 S g t₁ = gamma compI0 S g t₂) : t₁ = t₂ := by
  rcases h₁ with ⟨i, rfl, hi⟩ | ⟨m₁, rfl, hm₁⟩ <;> rcases h₂ with ⟨j, rfl, hj⟩ | ⟨m₂, rfl, hm₂⟩
  · rw [wsVal40_81_inj (hi.symm.trans (he.trans hj))]
  · rw [← he, hi] at hm₂; exact absurd hm₂ (wsVal40_81_keyOfTake8_ne i m₂)
  · rw [he, hj] at hm₁; exact absurd hm₁ (wsVal40_81_keyOfTake8_ne j m₁)
  · rw [he] at hm₁; rw [wsMacKey3_81_inj (hm₁.symm.trans hm₂)]
private theorem wire6Idx1Bytes_eq_b6' : wire6Idx1Bytes = Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes := by unfold wire6Idx1Bytes Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6Recv_head_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.eventBytes_recv]; rfl
set_option maxRecDepth 200000 in
theorem parse_b6Fast_senderRatchetKey :
    (((parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvFast).map
      (fun p => p.inner.senderRatchetKey.bytes.toList)).getD []) = wsAliceRatchetPk1 := by decide +kernel
private theorem gamma_dh_dhPk_compI0 (S : Sem) (g : Ghost) (sk₁ sk₂ : DY.Bytes) : gamma compI0 S g (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk₁) sk₂) = compLookupDh (clamp (gamma compI0 S g sk₂)) (gamma compI0 S g (DY.DiffieHellman.dhPk sk₁)) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.DiffieHellman.dhPk sk₁); simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk' heq; rw [heq] at hv; simp only at hv
    have hpk : ({ sk := sk' } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack = DY.DiffieHellman.dhPk sk₁ := hv; split
    · rw [hpk]; exact CompFreshDistinct.gamma_dh_pack_compI0 S g (DY.DiffieHellman.dhPk sk₁) sk₂
    · rw [CompFreshDistinct.gamma_dh_pack_compI0,
        show ({ sk := sk₂ } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack = DY.DiffieHellman.dhPk sk₂ from rfl,
        CompFreshDistinct.gamma_dhPk_compI0, CompI0Laws.compLookupDh_comm,
        ← CompFreshDistinct.gamma_dhPk_compI0, ← hpk]; rfl
  · exact CompFreshDistinct.gamma_dh_pack_compI0 S g (DY.DiffieHellman.dhPk sk₁) sk₂
theorem nodes81_wsNodePin81 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields}
    {ms' : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅)
    (hγ_bob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) :
    let P := WsNodePin81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅
    Nodes38 P r tr₁ tr₂ cl₁ ∧ Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂ ∧
      Nodes38 P r tr₄ tr₅ cl₅ ∧ (∀ u ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁, P u) ∧ NodesBob3 P r tr₁ tr_bob := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  obtain ⟨hMacKey1, hPrk1, _hSalt1, hCipherKey1, hIv1, hMacKey2, hPrk2, _hSalt2, hSeed2, hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk, hCk0, hPqr0, hStARk0, hSeed1, hCks2,
      hCipherKey2, hIv2⟩ := split81S1KdfPins r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hp hinv
  obtain ⟨hMacKey5, hPrk5, _hSalt5, hSeed5, hCks4, hChainPrk4, hRk4, hPqxdhPrk4, hCk4, hPqr4,
      hStARk4, hCks5, hCipherKey5, hIv5⟩ := split81S2KdfPins r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hinv
  let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
  let o₂ := CompPrefixInvAlice.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  have hPrk1_gen : gamma compI0 S g (node13Gen tr₁ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨9, by decide⟩) = WsIdx1O4Tag.ws1Prk := by
    change gamma compI0 S g (DY.KdfExtract.kdfExtract _ _) = _; rw [← encPrk_eq_kdfExtract_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hPrk1
  have hCipher1_gen : gamma compI0 S g (node13Gen tr₁ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨10, by decide⟩) = wsCipherKey1 := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).cipherKey = _; rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hCipherKey1
  have hMacKey1_gen : gamma compI0 S g (node13Gen tr₁ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨11, by decide⟩) = WsIdx1O4Tag.ws1MacKey := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).macKey = _; rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hMacKey1
  have hIv1_gen : gamma compI0 S g (node13Gen tr₁ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨12, by decide⟩) = wsIv1Full := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).iv = _; rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hIv1
  have hPrk5_gen : gamma compI0 S g (node13Gen tr₄ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨9, by decide⟩) = WsIdx1O4Tag.ws5Prk := by
    change gamma compI0 S g (DY.KdfExtract.kdfExtract _ _) = _; rw [← encPrk_eq_kdfExtract_ini tr₄ tr₅ r.bob o₂ cl₅]; exact hPrk5
  have hCipher5_gen : gamma compI0 S g (node13Gen tr₄ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨10, by decide⟩) = wsCipherKey5 := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).cipherKey = _; rw [← encKeys_eq_trMsgKeys_ini tr₄ tr₅ r.bob o₂ cl₅]; exact hCipherKey5
  have hMacKey5_gen : gamma compI0 S g (node13Gen tr₄ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨11, by decide⟩) = WsIdx1O4Tag.ws5MacKey := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).macKey = _; rw [← encKeys_eq_trMsgKeys_ini tr₄ tr₅ r.bob o₂ cl₅]; exact hMacKey5
  have hIv5_gen : gamma compI0 S g (node13Gen tr₄ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) ⟨12, by decide⟩) = wsIv5Full := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys _ _).iv = _; rw [← encKeys_eq_trMsgKeys_ini tr₄ tr₅ r.bob o₂ cl₅]; exact hIv5
  have hok₁ := SP.macChainOk_of_wire sp_wireMacChainOk_wire6Idx1 hp
  have hmac1_pin : SP.keyOfTake8 ((gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨0, by decide⟩)).take 8) = some (wsMacKey3_81 ⟨0, by decide⟩) := by
    have htake8 : (gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨0, by decide⟩)).take 8 = SP.msgMac8 p := by
      rw [← Cheval26WeakStateIdx1.CompRSchedBSeedPins.gamma_trunc8_eq compI0 S g]
      unfold macNode3_81 macNode38Gen; dsimp only; rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]
      exact (hinv.hwire₁ p hp).2.1
    rw [htake8, (Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk_spec hok₁).2.1]; rfl
  obtain ⟨p₂, hp₂⟩ := WsIdx1Split81MemoZPinRun.parse_b2
  have hok₂ := SP.macChainOk_of_wire WsIdx1Split81MemoZPinRun.SP.wireMacChainOk_b2 hp₂
  have hmac2_pin : SP.keyOfTake8 ((gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨1, by decide⟩)).take 8) = some (wsMacKey3_81 ⟨1, by decide⟩) := by
    have htake8 : (gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨1, by decide⟩)).take 8 = SP.msgMac8 p₂ := by
      rw [← Cheval26WeakStateIdx1.CompRSchedBSeedPins.gamma_trunc8_eq compI0 S g]
      exact WsIdx1Split81MemoZPinRun.encMac_msg2_81 hinv hp₂
    rw [htake8, (Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk_spec hok₂).2.1]; rfl
  obtain ⟨p₅, hp₅⟩ := WsIdx1Split81MemoZPinRun.parse_b5
  have hok₅ := SP.macChainOk_of_wire sp_wireMacChainOk_b5 hp₅
  have hmac5_pin : SP.keyOfTake8 ((gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨2, by decide⟩)).take 8) = some (wsMacKey3_81 ⟨2, by decide⟩) := by
    have htake8 : (gamma compI0 S g (macNode3_81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ⟨2, by decide⟩)).take 8 = SP.msgMac8 p₅ := by
      rw [← Cheval26WeakStateIdx1.CompRSchedBSeedPins.gamma_trunc8_eq compI0 S g]
      unfold macNode3_81 macNode38Gen; dsimp only; rw [← encKeys_eq_trMsgKeys_ini tr₄ tr₅ r.bob o₂ cl₅]
      exact WsIdx1Split81MemoZPinRun.encMac_msg5_81 hinv hp₅
    rw [htake8, (Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk_spec hok₅).2.1]; rfl
  have hBC4 : gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨4, by decide⟩) = WsIdx1O4Tag.wsSeed6 := gamma_bobSeed81 hfits hp hinv
  have hck0_len : (gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨2, by decide⟩)).length = 32 := by
    change (gamma compI0 S g (bobChainCk0 r _ _)).length = 32; rw [bobChainCk0_eq_hmac]; exact gamma_hmac_len S g _ _
  have hBC2 : gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨2, by decide⟩) = ws6_bob_ck0 :=
    gamma_key_of_hmac S g hck0_len hBC4 wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 wsS2Kdf_keyOfTake8.2.2.2.2.2
  have hBC0 : gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨0, by decide⟩) = ws6_bob_prk :=
    gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (bobChainCk0_eq_hmac r _ _).symm hBC2) wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 wsS2Kdf_keyOfTake8.2.2.2.2.1
  have hBC1 : gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨1, by decide⟩) = ws6_bob_rk1 := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨0, by decide⟩)
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1))) = ws6_bob_rk1
    rw [gamma_hmac_of S g hBC0 (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_1 S g))]
    exact wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.1
  have hBC3 : gamma compI0 S g (bobChainNode5 r tr₁ tr₂ tr₄ cl₁ ⟨3, by decide⟩) = ws6_bob_ck1 :=
    (split40_fwd_kdfCk S g hBC2 wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.1 wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.2).2
  have hp_fast : parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvFast = some p := by
    have hp' := hp
    rw [wire6Idx1Bytes_eq_b6', Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes_eq] at hp'
    exact hp'
  have hrt₂ : gamma compI0 S g (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) = wsAliceRatchetPk1 := by
    have h₁ : gamma compI0 S g (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) = p.inner.senderRatchetKey.bytes.toList := (hinv.hwire₁ p hp).2.2
    rw [h₁, ← parse_b6Fast_senderRatchetKey, hp_fast]; rfl
  have hagree_bob3 : gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (randTerm tr_bob.length 32)) = wsBob3_agree := by
    rw [show DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (randTerm tr_bob.length 32) = DY.DiffieHellman.dh (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs)) (randTerm tr_bob.length 32) from rfl, CompPlant.x25519Key_dhPk, gamma_dh_dhPk_compI0, hγ_bob, hrt₂]; exact wsBob3_forward.1
  have hrk1_bob3 : gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA38 r tr₁).dhs) (setupSecret r 2)).1 = wsStARk0 := by
    rw [createChain_bob_chain1_fst_eq hNe tr₁]; exact hStARk0
  have hBob3_0 : gamma compI0 S g (bob3Node3 r tr₁ tr_bob ⟨0, by decide⟩) = wsBob3_prk2 := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac _ _) = wsBob3_prk2
    rw [gamma_hmac_of S g hrk1_bob3 hagree_bob3]; exact wsBob3_forward.2.1
  have hBob3_1 : gamma compI0 S g (bob3Node3 r tr₁ tr_bob ⟨1, by decide⟩) = wsBob3_rk2 := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (bob3Node3 r tr₁ tr_bob ⟨0, by decide⟩)
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1))) = wsBob3_rk2
    rw [gamma_hmac_of S g hBob3_0 (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_1 S g))]; exact wsBob3_forward.2.2.1
  have hBob3_2 : gamma compI0 S g (bob3Node3 r tr₁ tr_bob ⟨2, by decide⟩) = wsBob3_cks := by
    change gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (bob3Node3 r tr₁ tr_bob ⟨0, by decide⟩)
      (DY.Concat.concat (bob3Node3 r tr₁ tr_bob ⟨1, by decide⟩)
        (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 2)))) = wsBob3_cks
    rw [gamma_hmac_of S g hBob3_0 (gamma_concat_of S g hBob3_1 (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_2 S g)))]; exact wsBob3_forward.2.2.2
  refine ⟨⟨Or.inl ⟨⟨0, by decide⟩, rfl, hPqxdhPrk⟩, Or.inl ⟨⟨1, by decide⟩, rfl, hRk0⟩,
    Or.inl ⟨⟨2, by decide⟩, rfl, hCk0⟩, Or.inl ⟨⟨3, by decide⟩, rfl, hPqr0⟩,
    Or.inl ⟨⟨4, by decide⟩, rfl, hChainPrk⟩, Or.inl ⟨⟨5, by decide⟩, rfl, hStARk0⟩,
    Or.inl ⟨⟨6, by decide⟩, rfl, hCks0⟩, Or.inl ⟨⟨7, by decide⟩, rfl, hCks1⟩,
    Or.inl ⟨⟨8, by decide⟩, rfl, hSeed1⟩, Or.inl ⟨⟨9, by decide⟩, rfl, hPrk1_gen⟩,
    Or.inl ⟨⟨10, by decide⟩, rfl, hCipher1_gen⟩, Or.inl ⟨⟨11, by decide⟩, rfl, hMacKey1_gen⟩,
    Or.inl ⟨⟨12, by decide⟩, rfl, hIv1_gen⟩, Or.inr ⟨⟨0, by decide⟩, rfl, hmac1_pin⟩⟩,
    ⟨Or.inl ⟨⟨13, by decide⟩, rfl, hCks2⟩, Or.inl ⟨⟨14, by decide⟩, rfl, hSeed2⟩,
    Or.inl ⟨⟨15, by decide⟩, rfl, hPrk2⟩, Or.inl ⟨⟨16, by decide⟩, rfl, hCipherKey2⟩,
    Or.inl ⟨⟨17, by decide⟩, rfl, hMacKey2⟩, Or.inl ⟨⟨18, by decide⟩, rfl, hIv2⟩,
    Or.inr ⟨⟨1, by decide⟩, rfl, hmac2_pin⟩⟩,
    ⟨Or.inl ⟨⟨19, by decide⟩, rfl, hPqxdhPrk4⟩, Or.inl ⟨⟨20, by decide⟩, rfl, hRk4⟩,
    Or.inl ⟨⟨21, by decide⟩, rfl, hCk4⟩, Or.inl ⟨⟨22, by decide⟩, rfl, hPqr4⟩,
    Or.inl ⟨⟨23, by decide⟩, rfl, hChainPrk4⟩, Or.inl ⟨⟨24, by decide⟩, rfl, hStARk4⟩,
    Or.inl ⟨⟨25, by decide⟩, rfl, hCks4⟩, Or.inl ⟨⟨26, by decide⟩, rfl, hCks5⟩,
    Or.inl ⟨⟨27, by decide⟩, rfl, hSeed5⟩, Or.inl ⟨⟨28, by decide⟩, rfl, hPrk5_gen⟩,
    Or.inl ⟨⟨29, by decide⟩, rfl, hCipher5_gen⟩, Or.inl ⟨⟨30, by decide⟩, rfl, hMacKey5_gen⟩,
    Or.inl ⟨⟨31, by decide⟩, rfl, hIv5_gen⟩, Or.inr ⟨⟨2, by decide⟩, rfl, hmac5_pin⟩⟩,
    ?_,
    ⟨Or.inl ⟨⟨37, by decide⟩, rfl, hBob3_0⟩, Or.inl ⟨⟨38, by decide⟩, rfl, hBob3_1⟩,
    Or.inl ⟨⟨39, by decide⟩, rfl, hBob3_2⟩⟩⟩
  intro u hu; simp only [bobChainTerms81, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨⟨32, by decide⟩, rfl, hBC0⟩
  · exact Or.inl ⟨⟨33, by decide⟩, rfl, hBC1⟩
  · exact Or.inl ⟨⟨34, by decide⟩, rfl, hBC2⟩
  · exact Or.inl ⟨⟨35, by decide⟩, rfl, hBC3⟩
  · exact Or.inl ⟨⟨36, by decide⟩, rfl, hBC4⟩
theorem kdfP_extBaseRows81 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hγ_bob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) (henumAt : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), WsIdx1Split81MemoRestFnA.Split81PrefixAtomAt r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u ∨ u ∈ storedSecrets (runTraceMoves r ms')) {x : Row} (hx : x ∈ extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁) {k m : DY.Bytes} (hkdf : x.1 = DY.KdfExtract.kdfExtract k m) : WsNodePin81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x.1 := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨hN₁, hN₂, hN₄, hBC, hNB⟩ := nodes81_wsNodePin81 hfits hp hinv hγ_bob
  rcases List.mem_append.mp hx with hpre | hext
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpre
    rcases henumAt u hu with hatom | hsec
    · exact kc_prefixAtom81_at hNe hN₁ hN₂ hN₄ hNB hatom x hxu k m hkdf
    · exact kc_storedSecrets_of_reachable hinv.reach u hsec x hxu k m hkdf
  · exact kdfP_extChainRows81 hNe hinv.hent₂ hN₄ hBC hext k m hkdf
theorem split81ExtKKOwn : Split81ExtKKOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hlinks; dsimp only; intro x₁ hx₁ x₂ hx₂ _ _ k₁ m₁ k₂ m₂ e₁ e₂ _ _ he; obtain ⟨tr_bob, hγ_bob, henumAt⟩ := WsIdx1Split81MemoRestFnA.split81PrefixEnumAt hinv hlinks; have hteq : x₁.1 = x₂.1 := wsNodePin81_inj (kdfP_extBaseRows81 hfits hp hinv hγ_bob henumAt hx₁ e₁) (kdfP_extBaseRows81 hfits hp hinv hγ_bob henumAt hx₂ e₂) he; rw [e₁, e₂] at hteq
  obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hteq
  exact ⟨.base fun _ _ => rfl, .base fun _ _ => rfl⟩
theorem split81ExtKKOwn_of_enum (_henum : Split81PrefixEnum) : Split81ExtKKOwn := split81ExtKKOwn
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreKdf
