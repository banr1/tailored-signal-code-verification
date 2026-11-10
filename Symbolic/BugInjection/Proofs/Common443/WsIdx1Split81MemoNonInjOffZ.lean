/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNonInjOffZ
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.CompC2Census38 Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs (Cls40)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest (iniAliceOut_eq_comp iniAliceStartState_eq_comp encSt_eq_comp encOut_eq_comp census_spqrSendKey census_storedSecrets_40 census_prefixAtom_40)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff ZVal)
open Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ (NonInjOffXZ)
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (gamma_concat)
open Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct (gamma_hmac_length)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc (encSalt_self)
theorem encWire_eq_comp : Census443Defs.encWire = CompPrefixInvEnc.encWire := rfl
theorem census_spqrB2A {S : Sem} {g : Ghost} : Census compI0 S g DY.Libsignal.TripleRatchet.spqrB2A :=
  census_lit_size _ (by decide) (by decide)
theorem census_spqrRecvState_of_map_fst {i : ExternInterpretation} {S : Sem} {g : Ghost} {st msg spqr' : DY.Bytes} {idx : UInt32} (hst : Census i S g st) (hm : Census i S g msg) (hrecv : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some spqr') : Census i S g spqr' := by obtain ⟨res, hres, rfl⟩ := Option.map_eq_some_iff.mp hrecv; rw [DY.Spqr.spqrRecv_state st msg idx res hres]; exact Census443Memo.memoOK_spqrRecvState_pack hst hm
theorem census_serialize_recv2 {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {rk ck : DY.Bytes} {idx : UInt32} (hrk : Census i S g rk) (hck : Census i S g ck)
    (hckL : (gamma i S g ck).length = 32) :
    let l := (Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
      [{ ratchetKey := rk, chainKey := ck, index := idx, rIdx := 2 }]
    Census i S g l ∧ 33 ≤ (gamma i S g l).length := by
  intro l
  let t0 : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize idx ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize 2) (DY.Literal.literalToBytes .empty)
  have hl : l = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize rk ++ Comparse.NonExtensibleMessageFormat.slowBytes.serialize ck) t0 := by
    have hnil := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil
    have h1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons { ratchetKey := rk, chainKey := ck, index := idx, rIdx := 2 } []
    have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq { ratchetKey := rk, chainKey := ck, index := idx, rIdx := 2 }
    dsimp only [l]
    rw [h1, hser, hnil, ← List.append_assoc, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]
  have hT0 : Census i S g t0 ∧ (gamma i S g t0).length = 7 := by
    have hL : (gamma i S g t0).length = 7 := by
      rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, CompPlant.gamma_uint32_serialize_length, CompPlant.gamma_slowNat_serialize_length, CompPlant.gamma_literalToBytes_length]; rfl
    refine ⟨census_concatPrefixes_lt8 _ (fun p hp => ?_) (census_lit_size _ (by decide) (by decide)) (by change (gamma i S g t0).length < 8; omega), hL⟩
    rcases List.mem_append.mp hp with h | h
    · exact census_mem_uint32 _ h
    · exact census_mem_slowNat _ h
  have hT1 : Census i S g (DY.Concat.concat ck t0) := by
    refine census_concat_len ?_ ?_ hck hT0.1 <;> rw [hckL, hT0.2] <;> decide
  have hT1L : 33 ≤ (gamma i S g (DY.Concat.concat ck t0)).length := by
    rw [gamma_concat, List.length_append, hckL, hT0.2]; decide
  have hc_eq : DY.Concat.concat ck t0 = Comparse.concatPrefixes [ck] t0 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
  rw [hc_eq] at hT1 hT1L
  have hsplit : Comparse.NonExtensibleMessageFormat.slowBytes.serialize ck =
      Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length ck) ++ [ck] := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq ck
  rw [hl, ← CompExcuse.concatPrefixes_append, hsplit, ← CompExcuse.concatPrefixes_append]
  have hcp := census_concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length ck))
    (fun p hp => census_mem_slowNat _ hp) hT1 hT1L
  exact census_concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize rk)
    (fun p hp => census_mem_slowBytes hrk hp) hcp.1 hcp.2
theorem trStateC_bobSt81 {r : Records} {S : Sem} {g : Ghost}
    (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob")
    {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {cl₁ cl₂ : Nat} {spqrMsgIdx₂ : UInt32} {spqr₂' : DY.Bytes}
    (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32)
    (hspqr : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    TRStateC S g (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1) := by
  dsimp only; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp] at hspqr ⊢; rw [encSt_eq_comp] at hspqr
  have ho₁ := census_aliceOut (S := S) (g := g) hNe tr₁ hent₁
  have hst₁ := trStateC_stA (S := S) (g := g) hNe hB tr₁ hent₁
  have hst₁' := trStateC_encSt tr₂ cl₁ hst₁
  let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
  let rt₂ := DY.DiffieHellman.dhPk stA₁.dhs
  have hrt₂ : Census compI0 S g rt₂ := census_dhPk hst₁.dhs
  have hsec2 : Census compI0 S g (setupSecret r 2) := by
    rw [CompSetupSecrecy.setupSecret_2 hNe]; exact census_randTerm 10 32
  have hcc1 := census_createChain ho₁.2.2.2.2.2.1 hrt₂ hsec2
  have hdhsB : Census compI0 S g (randTerm tr_bob.length 32) := census_randTerm tr_bob.length 32
  have hcc2 := census_createChain hcc1.1 hrt₂ hdhsB
  have hck1' : Census compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
        (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk rt₂ (setupSecret r 2)).2 (1 : UInt32).toNat)).1 :=
    (census_kdfCk (census_kdfCk hcc1.2).1).1
  obtain ⟨hrecv, hrecvL⟩ := census_serialize_recv2 (i := compI0) (S := S) (g := g)
    (idx := (1 : UInt32) + 1) hrt₂ hck1' (gamma_hmac_length S g _ _)
  have hpeerIk : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = stA₁.myIk := by
    change DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0))
    rw [CompSetupSecrecy.setupPublic_0 hNe, CompSetupSecrecy.setupSecret_0 hNe]
  have hrkL : (gamma compI0 S g o₁.keys.rk).length = 32 := CompRPreMemo38KdfCensus.aliceOut_rk_length tr₁ _ _ _ _ _
  have hrt₂_key : DY.X25519.x25519Key rt₂ = rt₂ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _
  refine {
    peer := participant_size_ne (Or.inl hA), myIk := hst₁.peerIk,
    peerIk := by dsimp only [bobSt81]; rw [hpeerIk]; exact hst₁.myIk,
    rk := hcc2.1, dhs := hdhsB, cks := hcc2.2,
    sid := by
      dsimp only [bobSt81]; rw [hrt₂_key]
      exact census_concat_len (by rw [CompFreshDistinct.gamma_dhPk_length S g _, hrkL]; decide)
        (by rw [CompFreshDistinct.gamma_dhPk_length S g _, hrkL]; decide) hrt₂ ho₁.2.2.2.2.2.1,
    spqr := census_spqrRecvState_of_map_fst (census_spqrInit ho₁.2.2.2.2.2.2.2 census_spqrB2A) (census_spqrSendMsg hst₁'.spqr (census_randTerm (tr₃.length + 1) cl₂)) hspqr,
    recv := hrecv, recvL := hrecvL }
theorem census_prefixAtom_81 {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob") {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) (hent₂ : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32) {u : DY.Bytes} (hu : Split81PrefixAtom r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ u) : Census compI0 S g u := by
  have ho₁ := census_aliceOut (S := S) (g := g) hNe tr₁ hent₁; have hst₁ := trStateC_stA (S := S) (g := g) hNe hB tr₁ hent₁; have hst₁' := trStateC_encSt tr₂ cl₁ hst₁; have henc₁ := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl₁ hent₁
  have hsalt₂ : Census compI0 S g (CompPrefixInvEnc.encSalt tr₃ (CompPrefixInvEnc.encSt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by rw [encSalt_self]; exact census_spqrSendKey hst₁'.spqr (census_randTerm (tr₃.length + 1) cl₂)
  have henc₂ := census_enc tr₃ cl₂ (tr₃.length + 2) hst₁' hsalt₂ (encWire_len_ge33 _ _ _ _); have ho₂ := census_aliceOut (S := S) (g := g) hNe tr₄ hent₂; have hst₂ := trStateC_stA (S := S) (g := g) hNe hB tr₄ hent₂; have henc₅ := census_encOut_stA (S := S) (g := g) hNe hB tr₄ tr₅ cl₅ hent₂; have hpaA := participant_size_ne (Or.inl hA); unfold Split81PrefixAtom at hu; dsimp only at hu; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encSt_eq_comp, encOut_eq_comp] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', _, hspqr, rfl⟩
  · exact ho₁.2.2.2.1
  · exact ho₁.2.2.2.2.1
  · exact henc₁.2.1
  · exact henc₂.2.1
  · exact ho₂.2.2.2.1
  · exact ho₂.2.2.2.2.1
  · exact henc₅.2.1
  · exact census_randTerm _ _
  · exact census_randTerm _ _
  · exact census_randTerm _ _
  · exact census_serialize_local_tr hpaA hst₁
  · exact census_serialize_local_tr hpaA hst₁'
  · exact census_serialize_local_tr hpaA (trStateC_encSt tr₃ cl₂ hst₁')
  · exact census_serialize_local_tr hpaA hst₂
  · exact census_serialize_local_tr hpaA (trStateC_encSt tr₅ cl₅ hst₂)
  · rw [← iniAliceOut_eq_comp, ← iniAliceStartState_eq_comp] at hspqr ⊢; rw [← encSt_eq_comp] at hspqr
    exact census_serialize_local_tr (participant_size_ne (Or.inr hB)) (trStateC_bobSt81 hNe hA hB hent₁ hspqr)
theorem census_honestSalts_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') : Census compI0 S g salt := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  have hent₁L : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have hent₂L : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32 := by rw [hinv.hent₂]; decide +kernel
  have ho₁ := census_aliceOut (S := S) (g := g) hNe tr₁ hent₁L; have hst₁ := trStateC_stA (S := S) (g := g) hNe (CompFitsNames.compFits_bob hfits) tr₁ hent₁L; have ho₂ := census_aliceOut (S := S) (g := g) hNe tr₄ hent₂L
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl | rfl
  · exact census_zeroKey
  · exact census_spqrChainKey ho₁.2.2.2.2.2.2.2 census_spqrA2B (census_spqrIdx 1)
  · exact census_spqrSendKey (trStateC_encSt tr₂ cl₁ hst₁).spqr (census_randTerm (tr₃.length + 1) cl₂)
  · exact census_spqrChainKey ho₂.2.2.2.2.2.2.2 census_spqrA2B (census_spqrIdx 1)
theorem split81NewCensus {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∀ u ∈ split81NewTerms r ms' p (x81Idx1 r tr₁ tr₂ tr₄ cl₁), Census compI0 S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfits; have hopk : p.preKeyId = none := wire6Idx1Bytes_preKeyId hp
  have hent₁L : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have hent₂L : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32 := by rw [hinv.hent₂]; decide +kernel
  have ho₂ := census_aliceOut (S := S) (g := g) hNe tr₄ hent₂L; have henc₁ := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl₁ hent₁L
  have hsec2 : Census compI0 S g (setupSecret r 2) := by rw [CompSetupSecrecy.setupSecret_2 hNe]; exact census_randTerm 10 32
  have hcc := census_createChain ho₂.2.2.2.2.2.1 (census_dhPk (census_randTerm (tr₁.length + 2) 32)) hsec2; have hkdf := census_kdfCk hcc.2; intro u hu; rw [split81NewTerms_x81Idx1_eq r ms' p tr₁ tr₂ tr₄ cl₁] at hu; simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
  rcases hu with rfl | rfl | rfl | hu_bob
  · dsimp only [x81Idx1]; rw [iniAliceOut_eq_comp]; exact ho₂.2.2.2.1
  · dsimp only [x81Idx1]; rw [iniAliceOut_eq_comp]; exact ho₂.2.2.2.2.1
  · dsimp only [x81Idx1]; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encOut_eq_comp]; exact henc₁.2.1
  · rcases mem_bobTerms_x81Idx1_iff hNe hopk hu_bob with hu_ch | ⟨salt, hsalt, hu_salt⟩
    · unfold ws81Idx1ChainTerms at hu_ch; dsimp only at hu_ch; rw [iniAliceOut_eq_comp] at hu_ch
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_ch
      rcases hu_ch with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ho₂.2.2.2.2.2.1
      · exact ho₂.2.2.2.2.2.2.1
      · exact ho₂.2.2.2.2.2.2.2
      · exact hcc.2
      · exact hkdf.1
      · exact census_randTerm tr₂.length 32
    · unfold ws81Idx1SaltTerms at hu_salt; dsimp only at hu_salt
      rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encWire_eq_comp] at hu_salt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_salt; have hmk := census_trMsgKeys (census_honestSalts_81 hfits hinv hsalt) hkdf.2
      rcases hu_salt with rfl | rfl | rfl | rfl
      · exact hmk.1
      · exact hmk.2.1
      · exact hmk.2.2
      · exact henc₁.2.2 _ hmk.2.1
theorem split81NonInjCensusOwn_of_enum (hEnum : Split81PrefixEnum) : Split81NonInjCensusOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x hx _ hai; have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfits; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfits
  have hent₁L : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have hent₂L : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32 := by rw [hinv.hent₂]; decide +kernel
  rcases List.mem_append.mp hx with hpre | hnew
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpre
    rcases hEnum r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu with hatom | hsec
    · exact census_prefixAtom_81 hNe hA hB hent₁L hent₂L hatom x hxu hai
    · exact census_storedSecrets_40 hfits.1 hA hB hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec x hxu hai
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hnew
    exact split81NewCensus hfits hp hinv u hu x hxu hai
theorem split81NonInjOffZOwn_of_enum (hEnum : Split81PrefixEnum) : Split81NonInjOffZOwn := split81NonInjOffZOwn_of_census (split81NonInjCensusOwn_of_enum hEnum)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNonInjOffZ
