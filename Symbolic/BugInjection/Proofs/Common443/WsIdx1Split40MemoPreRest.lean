/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.CompC2Census38
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestR38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (PairQ PairSide)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff)
open Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ (NonInjOffXZ)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestCore Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 Symbolic.BugInjection.Proofs.Common443.CompC2RestFn Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38 Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 Symbolic.BugInjection.Proofs.Common443.CompC2Census38 Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc (encSalt_self)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def liftPairQ40 (Q : PairQ) : PairQ40 := fun S g known pts _ _ x₁ x₂ => Q S g known pts x₁ x₂
def Split40PairsOwn (Q : PairQ40) : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let pre := preMemo40 r S g ms'
    let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
    let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
    ∀ x₁ ∈ new, ∀ x₂ ∈ pre ++ new, Cls40 pre Z x₁ → Cls40 pre Z x₂ →
      Q S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (ptAtoms (runVis r ms') ++ []) pre Z x₁ x₂
def Split40NonInjCensusOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let pre := preMemo40 r S g ms'
    let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
    let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
    ∀ x ∈ pre ++ new, Cls40 pre Z x → assumedInjective x.1 = false → NonInjOffXZ x.2.2
def Split40RestEntryOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let pre := preMemo40 r S g ms'
    let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
    let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
    ∀ x ∈ pre ++ new, Cls40 pre Z x → RestEntry S g x
def Split40RestFnOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let pre := preMemo40 r S g ms'
    let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
    let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
    ∃ (fn : HwBytes → DY.Bytes) (Rv : HwBytes → Prop), ∀ x ∈ pre ++ new, Cls40 pre Z x → RestFnEntry fn Rv S g x
theorem exists_memo_of_mem40 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {p : PreKeyFields} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : Row} (hx : x ∈ preMemo40 r S g ms' ++ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂) : x.2.2 = gamma compI0 S g x.1 := (sound_of_mem_pre_new hx).2
theorem split40PairsOwn_qRest_of_entry_fn (hN : Split40NonInjCensusOwn) (hE : Split40RestEntryOwn) (hF : Split40RestFnOwn) : Split40PairsOwn (liftPairQ40 QRest) := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown _ _ _ x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨fn, Rv, hfn⟩ := hF r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hx₁_mem := List.mem_append_right (preMemo40 r S g ms') hx₁; have hv₁ := exists_memo_of_mem40 hx₁_mem; have hv₂ := exists_memo_of_mem40 hx₂; have hf₁ := hfn x₁ hx₁_mem hc₁; have hf₂ := hfn x₂ hx₂ hc₂
  exact qRest_of_entries S g _ _ x₁ x₂ hv₁ hv₂ (hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁_mem hc₁) (hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₂ hx₂ hc₂) (hE r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁_mem hc₁) (hE r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₂ hx₂ hc₂) (qRestNR_of_fn hv₁ hv₂ hf₁ hf₂) (qRestRR_of_fn hv₁ hv₂ hf₁ hf₂) (qRestXX_of_fn hv₁ hv₂ hf₁ hf₂) (qRestTT_of_fn hv₁ hv₂ hf₁ hf₂)
theorem census_spqrSendKey {i : ExternInterpretation} {S : Sem} {g : Ghost} {st c : DY.Bytes} (hst : Census i S g st) (hc : Census i S g c) : Census i S g (DY.Spqr.spqrSend st c).2.1 := by
  unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => exact memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := memoOK_spqrInit_elim hst
    exact census_spqrChainKey hk hpar (census_lit _ (nonInjOffXZ_of_len
      (by rw [CompPlant.gamma_literalToBytes_length]; simp [ByteArray.size])
      (by rw [CompPlant.gamma_literalToBytes_length]; simp [ByteArray.size])))
theorem census_storedSecrets_40 {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hfits : compFits w compI0 r) (hA : r.alice = "alice") (hB : r.bob = "bob") (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), Census compI0 S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1; have hopk : r.withOpk = false := hfits.2.1; have hinv := CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach
  have hL : ∀ ts sz, (ts, sz) ∈ setupRandomsAt r → sz ≠ 0 → 32 ≤ sz → 32 ≤ (gamma compI0 S g (randTerm ts sz)).length := by intro ts sz hp hsz h32; rw [gamma_setup_len hc hfits.1 hp hsz]; exact h32
  intro u hu; obtain ⟨j, _, ⟨part, ⟨kind, sk⟩⟩, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu; have hkind := hinv.stOK part ⟨kind, sk⟩ j hat; dsimp only [CompInv.KindOK] at hkind
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨hp, rfl, _⟩ | ⟨hp, rfl, _⟩
    · refine census_serialize_local_pqxdh (participant_size_ne (Or.inl (hp.trans hA))) ?_ ?_ <;>
        dsimp only <;> rw [CompSetupSecrecy.setupSecret_0 hNe]
      · exact census_randTerm _ _
      · exact hL 0 32 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inl rfl))) (by decide) le_rfl
    · refine census_serialize_local_pqxdh (participant_size_ne (Or.inr (hp.trans hB))) ?_ ?_ <;>
        dsimp only <;> rw [CompSetupSecrecy.setupSecret_1 hNe]
      · exact census_randTerm _ _
      · exact hL 5 32 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inl rfl)))) (by decide) le_rfl
  | signedPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind
    refine census_serialize_local_pqxdh (participant_size_ne (Or.inr (hp.trans hB))) ?_ ?_ <;>
      dsimp only <;> rw [CompSetupSecrecy.setupSecret_2 hNe]
    · exact census_randTerm _ _
    · exact hL 10 32 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inr rfl)))) (by decide) le_rfl
  | pqPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind
    refine census_serialize_local_pqxdh (participant_size_ne (Or.inr (hp.trans hB))) ?_ ?_ <;>
      dsimp only <;> rw [CompSetupSecrecy.setupSecret_4 hNe]
    · exact census_randTerm _ _
    · exact hL 16 64 (CompPrefixInvFresh.mem_setupRandomsAt_64 r hNe (by simp)) (by decide) (by decide)
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe
        (CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev) with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩ <;>
      [cases heq; cases heq; cases heq; cases heq; (rw [hopk] at hopk_true; cases hopk_true)]
theorem iniAliceOut_eq_comp : @Census443Defs.iniAliceOut = @CompPrefixInvAlice.iniAliceOut := rfl
theorem iniAliceStartState_eq_comp : @Census443Defs.iniAliceStartState = @CompPrefixInvAlice.iniAliceStartState := rfl
theorem encSt_eq_comp : @Census443Defs.encSt = @CompPrefixInvEnc.encSt := rfl
theorem encOut_eq_comp : @Census443Defs.encOut = @CompPrefixInvEnc.encOut := rfl
theorem census_prefixAtom_40 {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob") {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : Census compI0 S g u := by
  have ho := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have hst₁ := trStateC_stA (S := S) (g := g) hNe hB tr₁ hent; have hst₁' := trStateC_encSt tr₂ cl₁ hst₁
  have hsalt₂ : Census compI0 S g (CompPrefixInvEnc.encSalt tr₃ (CompPrefixInvEnc.encSt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by rw [encSalt_self]; exact census_spqrSendKey hst₁'.spqr (census_randTerm (tr₃.length + 1) cl₂)
  have hpaA := participant_size_ne (Or.inl hA); unfold Split40PrefixAtom at hu; dsimp only at hu; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encSt_eq_comp, encOut_eq_comp] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.2.2.2.1
  · exact ho.2.2.2.2.1
  · exact (census_encOut_stA hNe hB tr₁ tr₂ cl₁ hent).2.1
  · exact (census_enc tr₃ cl₂ (tr₃.length + 2) hst₁' hsalt₂ (encWire_len_ge33 _ _ _ _)).2.1
  · exact census_randTerm _ _
  · exact census_randTerm _ _
  · exact census_serialize_local_tr hpaA hst₁
  · exact census_serialize_local_tr hpaA hst₁'
  · exact census_serialize_local_tr hpaA (trStateC_encSt tr₃ cl₂ hst₁')
theorem split40NonInjCensusOwn_of_enum (hEnum : Split40PrefixEnum) (hNew : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ u ∈ split40NewTerms r ms' p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂), Census compI0 S g u) : Split40NonInjCensusOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown _ _ _ x hx _ hai; have hA := CompFitsNames.compFits_alice hfits; have hB := CompFitsNames.compFits_bob hfits
  have hentL : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  rcases List.mem_append.mp hx with hpre | hnew
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpre
    exact (hEnum r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu).elim
      (fun hatom => census_prefixAtom_40 hfits.1.1.1 hA hB hentL hatom x hxu hai)
      (fun hsec => census_storedSecrets_40 hfits.1 hA hB hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec x hxu hai)
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hnew
    exact hNew r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu x hxu hai
theorem restEntry_of_saltedNodes40 {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : Row} (hz : x.1 ∈ saltedNodes40 salt tr stA cl) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := by
  simp only [saltedNodes40, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | h <;> [exact restEntry_of_kdf h; exact restEntry_of_kdf h;
    exact restEntry_of_kdf h; exact restEntry_of_kdf h; exact restEntry_of_kdf h;
    exact restEntry_of_trunc8_kdf h hv]
theorem restEntry_of_z40Terms {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : Row} (hz : x.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := (List.mem_append.mp hz).elim (fun h => restEntry_of_saltedNodes40 h hv) (fun h => restEntry_of_saltedNodes40 h hv)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
section DecideRVal
set_option maxRecDepth 200000
theorem rVal_wsIdx1_aliceId : RVal setup.aliceId := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_wsIdx1_bobId : RVal setup.bobId := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_wsIdx1_spk : RVal setup.spk := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_compKyberE1 : RVal compKyberE1 := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_compKyberSs1 : RVal compKyberSs1 := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem compKyberEncaps_e1 : compKyberEncaps compKyberE1 = compKyberCt1 ++ compKyberSs1 := by decide +kernel
theorem rVal_compAesPt1 : RVal compAesPt1 := rVal_of_len (by decide +kernel) (by decide +kernel)
theorem rVal_compAesPt2 : RVal compAesPt2 := rVal_of_len (by decide +kernel) (by decide +kernel)
end DecideRVal
theorem rVal_kemEncap_snd_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : RVal (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32]
  have h : compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] =
      some (compKyberEncaps (gamma compI0 S g e)) := rfl
  rw [h, Option.getD_some, he, compKyberEncaps_e1, List.drop_left' Census443Memo.kyberCtVals_lengths.2.1]; exact rVal_compKyberSs1
theorem rVal_compAesPerm_pt1 (k iv : HwBytes) : RVal (compAesPerm k iv compAesPt1) :=
  rVal_of_len (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt1 (by decide)]; decide)
    (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt1 (by decide)]; decide)
theorem rVal_compAesPerm_pt2 (k iv : HwBytes) : RVal (compAesPerm k iv compAesPt2) :=
  rVal_of_len (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt2 (by decide)]; decide)
    (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt2 (by decide)]; decide)
private theorem rc_encOut_self_of_rVal {S : Sem} {g : Ghost} (tr : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateRC S g stA) (hpt : RVal (gamma compI0 S g (randTerm tr.length 32))) (hct_v : ∀ k iv : DY.Bytes, RVal (gamma compI0 S g (DY.SymEnc.symEnc k iv (randTerm tr.length 32)))) (hc : RC S g (randTerm (tr.length + 1) cl)) : RC S g (CompPrefixInvEnc.encOut tr stA cl (tr.length + 2)) := by
  have hsalt : RC S g (CompPrefixInvEnc.encSalt tr stA cl (tr.length + 2)) := by rw [encSalt_self]; exact rc_spqrSendKey hst.spqr hc
  dsimp only [CompPrefixInvEnc.encOut, CompPrefixInvEnc.encWire, CompPrefixInvEnc.encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]; have hmk := rc_trMsgKeys hsalt hst.cks; have hct := rc_symEnc (hct_v _ _) hmk.1 hmk.2.2 (rc_randTerm hpt); have hdhsPk := rc_dhPk hst.dhs; have hpqMsg := rc_spqrSendMsg hst.spqr hc; exact rc_concat (rc_trWire hdhsPk hct hpqMsg) (rc_computeMac_trWire hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
theorem rc_encOut_self_pt1 {S : Sem} {g : Ghost}
    (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl₁ : Nat)
    (hst : TRStateRC S g stA)
    (hpt : gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1)
    (hc : RC S g (randTerm (tr₂.length + 1) cl₁)) :
    RC S g (CompPrefixInvEnc.encOut tr₂ stA cl₁ (tr₂.length + 2)) :=
  rc_encOut_self_of_rVal tr₂ cl₁ hst (hpt ▸ rVal_compAesPt1)
    (fun k iv => by rw [gamma_symEnc_eq', hpt]; exact rVal_compAesPerm_pt1 _ _) hc
theorem rc_encOut_self_pt2 {S : Sem} {g : Ghost}
    (tr₃ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl₂ : Nat)
    (hst : TRStateRC S g stA)
    (hpt : gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2)
    (hc : RC S g (randTerm (tr₃.length + 1) cl₂)) :
    RC S g (CompPrefixInvEnc.encOut tr₃ stA cl₂ (tr₃.length + 2)) :=
  rc_encOut_self_of_rVal tr₃ cl₂ hst (hpt ▸ rVal_compAesPt2)
    (fun k iv => by rw [gamma_symEnc_eq', hpt]; exact rVal_compAesPerm_pt2 _ _) hc
theorem rc_setup_wsIdx1 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) : RC S g (randTerm 0 32) ∧ RC S g (randTerm 5 32) ∧ RC S g (randTerm 10 32) ∧ RC S g (randTerm 16 64) := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  refine ⟨rc_randTerm ?_, rc_randTerm ?_, rc_randTerm ?_, rc_randTerm ?_⟩
  · rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRX0Bytes.gamma_setupSecret_0 hNe hc, hfits.1.2.2.2.2.2.2.1]
    exact rVal_wsIdx1_aliceId
  · rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.1.2.2.2.2.2.2.2.1]
    exact rVal_wsIdx1_bobId
  · rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.1.2.2.2.2.2.2.2.2.1]
    exact rVal_wsIdx1_spk
  · rw [← CompSetupSecrecy.setupSecret_4 hNe, gamma_setupSecret_4' hNe hc, (CompFitsNames.compFits_secretBytes_fresh hfits).2.1]
    exact rVal_fillFresh_16_64
theorem rc_storedSecrets_40 {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), RC S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hopk : r.withOpk = false := hfits.1.2.1; obtain ⟨h0, h5, h10, h16⟩ := rc_setup_wsIdx1 hfits hc; have hinv := CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; intro u hu; obtain ⟨j, _, ⟨part, ⟨kind, sk⟩⟩, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu
  refine rc_serialize_local_pqxdh ?_
  have hkind := hinv.stOK part ⟨kind, sk⟩ j hat; dsimp only [CompInv.KindOK] at hkind ⊢
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · rw [CompSetupSecrecy.setupSecret_0 hNe]; exact h0
    · rw [CompSetupSecrecy.setupSecret_1 hNe]; exact h5
  | signedPrekey =>
    obtain ⟨_, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind; rw [CompSetupSecrecy.setupSecret_2 hNe]; exact h10
  | pqPrekey =>
    obtain ⟨_, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind; rw [CompSetupSecrecy.setupSecret_4 hNe]; exact h16
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe
        (CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev) with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩ <;>
      [cases heq; cases heq; cases heq; cases heq; (rw [hopk] at hopk_true; cases hopk_true)]
def Split40DrawPins (r : Records) (S : Sem) (g : Ghost)
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop :=
  let _ := r
  RVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧
  RVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧
  gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧
  RVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧
  gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧
  RVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂))
theorem rc_prefixAtom_40 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1) (hdraws : Split40DrawPins r S g tr₁ tr₂ tr₃ cl₁ cl₂) {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : RC S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨h0, h5, h10, h16⟩ := rc_setup_wsIdx1 hfits hc; obtain ⟨hekV, hdhsV, hpt₁, hc₁V, hpt₂, hc₂V⟩ := hdraws; have hekR := rc_randTerm hekV; have hentR := rc_randTerm_of_eq hent₁ rVal_compKyberE1; have hssV := rVal_kemEncap_snd_of_e1 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₁; have hc₁R := rc_randTerm hc₁V; have hc₂R := rc_randTerm hc₂V; have hout := rc_aliceOut hNe tr₁ h0 h5 h10 h16 hekR hentR hssV
  have hst₁ := trStateRC_stA hNe tr₁ h0 h5 h10 h16 hekR hentR hssV (rc_randTerm hdhsV); have hst₁' := trStateRC_encSt tr₂ cl₁ hst₁ hc₁R; unfold Split40PrefixAtom at hu; dsimp only at hu; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encSt_eq_comp, encOut_eq_comp] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hout.2.2.2.1
  · exact hout.2.2.2.2.1
  · exact rc_encOut_self_pt1 tr₂ cl₁ hst₁ hpt₁ hc₁R
  · exact rc_encOut_self_pt2 tr₃ cl₂ hst₁' hpt₂ hc₂R
  · exact rc_randTerm_of_eq hpt₁ rVal_compAesPt1
  · exact rc_randTerm_of_eq hpt₂ rVal_compAesPt2
  · exact rc_serialize_local_tr hst₁
  · exact rc_serialize_local_tr hst₁'
  · exact rc_serialize_local_tr (trStateRC_encSt tr₃ cl₂ hst₁' hc₂R)
theorem split40RestEntryOwn_of_enum (hEnum : Split40PrefixEnum) (hDraws : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Split40DrawPins r S g tr₁ tr₂ tr₃ cl₁ cl₂) : Split40RestEntryOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown _ _ _ x hx hc; have hv := exists_memo_of_mem40 hx
  rcases hc with hpre | hni | hz
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpre
    exact (hEnum r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu).elim
      (fun hatom => rc_prefixAtom_40 hfits hinv.compat hinv.hent₁
        (hDraws r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown) hatom x hxu hv)
      (fun hsec => rc_storedSecrets_40 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec x hxu hv)
  · exact restEntry_of_nonInj hni
  · exact restEntry_of_z40Terms hz hv
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
