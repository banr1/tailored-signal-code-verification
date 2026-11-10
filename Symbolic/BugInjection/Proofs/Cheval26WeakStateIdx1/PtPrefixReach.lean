/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35
public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown hiding bytes_rec_gAll
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section ExtraNodes
variable {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes}
theorem ptAvoidFull_of_attackerKnows (hbase : ∀ t : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows t → PtAvoidFull i r S g ms b t)
    {t : DY.Bytes} (ht : t.AttackerKnows (runTraceMoves r ms)) : PtAvoidFull i r S g ms b t :=
  memoOK_of_attackerKnows (fun _ hak _ _ hnk => False.elim (hnk hak)) (fun _ hni _ hinj _ => by rw [hni] at hinj; cases hinj) hbase ht
theorem ptAvoidFull_of_attackerKnows_le {tr : ExecTrace} {t : DY.Bytes} (hle : tr ≤ runTraceMoves r ms)
    (hbase : ∀ u : DY.Bytes, tr.BaseAttackerKnows u → PtAvoidFull i r S g ms b u) (ht : t.AttackerKnows tr) : PtAvoidFull i r S g ms b t :=
  memoOK_of_attackerKnows (P := fun x => x.1 ∉ ptAtoms (runVis r ms) → assumedInjective x.1 = true → ¬ x.1.AttackerKnows (runTraceMoves r ms) → x.2.2 ≠ b)
    (fun x hak _ _ hnak => absurd (DY.Bytes.AttackerKnows_le x.1 _ _ hle hak) hnak) (fun _ hni _ hinj _ => by rw [hni] at hinj; cases hinj) hbase ht
theorem ptAvoidFull_kemPk {sk : DY.Bytes} (hsk : PtAvoidFull i r S g ms b sk) : PtAvoidFull i r S g ms b (DY.PQKem.kemPk sk) := memoOK_kemPk hsk
theorem ptAvoidFull_vk {sk : DY.Bytes} (hsk : PtAvoidFull i r S g ms b sk) : PtAvoidFull i r S g ms b (DY.Signature.vk sk) := memoOK_vk hsk
theorem ptAvoidFull_sign {sk n m : DY.Bytes} (hsk : PtAvoidFull i r S g ms b sk) (hn : PtAvoidFull i r S g ms b n) (hm : PtAvoidFull i r S g ms b m) : PtAvoidFull i r S g ms b (DY.Signature.sign sk n m) := memoOK_sign hsk hn hm
theorem ptAvoidFull_encodeEC {pk : DY.Bytes} (hpk : PtAvoidFull i r S g ms b pk) : PtAvoidFull i r S g ms b (DY.Libsignal.PQXDH.encodeEC pk) := ptAvoidFull_concat (ptAvoidFull_lit _) hpk
theorem ptAvoidFull_encodeKEM {pk : DY.Bytes} (hpk : PtAvoidFull i r S g ms b pk) : PtAvoidFull i r S g ms b (DY.Libsignal.PQXDH.encodeKEM pk) := ptAvoidFull_concat (ptAvoidFull_lit _) hpk
theorem ptAvoidFull_kemEncap_fst_elim {c : DY.PQKem.Encap.SubF DY.Bytes} (h : PtAvoidFull i r S g ms b c.pack) : PtAvoidFull i r S g ms b c.pk ∧ PtAvoidFull i r S g ms b c.entropy := memoOK_kemEncap_fst_elim h
theorem ptAvoidFull_kemEncap_fst_compI0 {pk e : DY.Bytes} (hb : b.length < 32) (hpk : PtAvoidFull compI0 r S g ms b pk) (he : PtAvoidFull compI0 r S g ms b e) : PtAvoidFull compI0 r S g ms b (DY.PQKem.kemEncap pk e).1 := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemEncap compI0) (gAll compI0 S g)] at hx
  dsimp only [gKemEncap, concretizeKemEncap] at hx; split_ifs at hx
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · intro heq; have hlen := congrArg List.length heq
      change (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).take 1568).length = b.length at hlen; rw [compI0_kyberEncaps, Option.getD_some, compKyberEncaps_take_length] at hlen; omega
    · exact hpk x hxpk hnpt hinj hnk
    · exact he x hxe hnpt hinj hnk
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hpk x h hnpt hinj hnk) (fun h => he x h hnpt hinj hnk)
theorem ptAvoidFull_kemEncap_snd_compI0 {pk e : DY.Bytes} (hb : b.length < 32) (hpk : PtAvoidFull compI0 r S g ms b pk) (he : PtAvoidFull compI0 r S g ms b e) : PtAvoidFull compI0 r S g ms b (DY.PQKem.kemEncap pk e).2 := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)] at hx
  dsimp only [gKemSS, concretizeKemSS] at hx; split_ifs at hx
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe
    · intro heq; have hlen := congrArg List.length heq
      change (((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [_, _]).getD []).drop 1568).length = b.length at hlen; rw [compI0_kyberEncaps, Option.getD_some, compKyberEncaps_drop_length] at hlen; omega
    · exact hpk x hxpk hnpt hinj hnk
    · exact he x hxe hnpt hinj hnk
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    exact hx.elim (fun h => hpk x h hnpt hinj hnk) (fun h => he x h hnpt hinj hnk)
theorem ptAvoidFull_x25519Key {pk : DY.Bytes} (h : PtAvoidFull i r S g ms b pk) : PtAvoidFull i r S g ms b (DY.X25519.x25519Key pk) := memoOK_x25519Key h
theorem ptAvoidFull_dh_pack_compI0 {pk sk : DY.Bytes} (hb : b.length < 32) (hpk : PtAvoidFull compI0 r S g ms b pk) (hsk : PtAvoidFull compI0 r S g ms b sk) : PtAvoidFull compI0 r S g ms b (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gDh compI0) (gAll compI0 S g)] at hx; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk
  · intro heq; have hlen : (compLookupDh (clamp (gamma' compI0 S g sk).val) (gamma' compI0 S g pk).val).length = 32 := compLookupDh_length _ _
    change compLookupDh (clamp (gamma' compI0 S g sk).val) (gamma' compI0 S g pk).val = b at heq; rw [heq] at hlen; omega
  · exact hpk x hxpk hnpt hinj hnk
  · exact hsk x hxsk hnpt hinj hnk
theorem ptAvoidFull_dh_compI0 {pk sk : DY.Bytes} (hb : b.length < 32) (hpk : PtAvoidFull compI0 r S g ms b pk) (hsk : PtAvoidFull compI0 r S g ms b sk) : PtAvoidFull compI0 r S g ms b (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split <;> [exact ptAvoidFull_dh_pack_compI0 hb hpk hsk; exact ptAvoidFull_dh_pack_compI0 hb (ptAvoidFull_dhPk_compI0 hb hsk) (memoOK_dhPk_elim hpk)]
  · exact ptAvoidFull_dh_pack_compI0 hb hpk hsk
theorem ptAvoidFull_pqxdhIkm {dh1 dh2 dh3 : DY.Bytes} {dh4 : Option DY.Bytes} {ss : DY.Bytes} (h1 : PtAvoidFull i r S g ms b dh1) (h2 : PtAvoidFull i r S g ms b dh2) (h3 : PtAvoidFull i r S g ms b dh3) (h4 : ∀ d, dh4 = some d → PtAvoidFull i r S g ms b d) (hss : PtAvoidFull i r S g ms b ss) : PtAvoidFull i r S g ms b (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 ss) := by
  unfold DY.Libsignal.PQXDH.pqxdhIkm
  refine ptAvoidFull_concat (ptAvoidFull_lit _) (ptAvoidFull_concat h1 (ptAvoidFull_concat h2 (ptAvoidFull_concat h3 ?_)))
  cases dh4 with | none => exact hss | some d => exact ptAvoidFull_concat (h4 d rfl) hss
theorem ptAvoidFull_pqxdhKdf {ikm : DY.Bytes} (hb : b.length < 32) (hikm : PtAvoidFull i r S g ms b ikm) :
    let keys := DY.Libsignal.PQXDH.pqxdhKdf ikm
    PtAvoidFull i r S g ms b keys.rk ∧ PtAvoidFull i r S g ms b keys.ck ∧ PtAvoidFull i r S g ms b keys.pqr := by
  have hprk : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm) := ptAvoidFull_hmac hb (ptAvoidFull_lit _) hikm; have hinfo : PtAvoidFull i r S g ms b DY.Libsignal.PQXDH.pqxdhLabel := ptAvoidFull_lit _; exact ⟨ptAvoidFull_hkdfBlock1 hb hprk hinfo, ptAvoidFull_hkdfBlock2 hb hprk hinfo, ptAvoidFull_hkdfBlock3 hb hprk hinfo⟩
theorem ptAvoidFull_spqrRecvKey_of {st m : DY.Bytes} {idx : UInt32} {res : DY.Bytes × DY.Bytes} (hrecv : DY.Spqr.spqrRecv st m idx = some res) (hst : PtAvoidFull i r S g ms b st) (hm : PtAvoidFull i r S g ms b m) : PtAvoidFull i r S g ms b res.2 := by
  unfold DY.Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
    cases hv : st.view? DY.Spqr.InitState.SubF with
    | none => rw [hv] at hrecv; injection hrecv with hrecv'; subst hrecv'; exact memoOK_spqrRecvKey_pack hst hm
    | some x =>
      rw [hv] at hrecv hp; rcases x with ⟨authKey, params⟩; dsimp only at hrecv hp; rw [← hp] at hst; obtain ⟨hk, _⟩ := ptAvoidFull_spqrInit_elim hst
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv; injection hrecv with hrecv'; subst hrecv'; dsimp only
        split <;> [exact ptAvoidFull_literalToBytes _; exact ptAvoidFull_spqrChainKey hk (ptAvoidFull_literalToBytes _) (ptAvoidFull_literalToBytes _)]
end ExtraNodes
def BaseGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ u : DY.Bytes, tr.BaseAttackerKnows u → PtAvoidFull i r S g ms b u
theorem baseAttackerKnows_le {tr tr' : ExecTrace} (hle : tr ≤ tr') {u : DY.Bytes} (hu : tr.BaseAttackerKnows u) : tr'.BaseAttackerKnows u := by induction hle with | equal => exact hu | extend _ _ _ ih => rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2]; exact Or.inr ih
def StepOK (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (k : Nat) : Prop := ∀ (trPre : ExecTrace) (input : reachability.Input), input.1.1 = k → trPre.Reachable reachability → reachability.PreCond input trPre → ((reachability.step input).snd.run trPre).2.val ≤ runTraceMoves r ms → BaseGood i r S g ms b trPre → BaseGood i r S g ms b ((reachability.step input).snd.run trPre).2.val
def NoNewBase (tr₀ tr : ExecTrace) : Prop := ∀ u : DY.Bytes, tr.BaseAttackerKnows u → tr₀.BaseAttackerKnows u
theorem preserves_logPQ_noNewBase {tr₀ : ExecTrace} (ev : DY.Libsignal.PQXDH.PQXDHEvent) : CompTrace.Preserves (NoNewBase tr₀) (ProtocolEvent.logEvent ev) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_pqEv tr ev u).mp ((TR.Runs.logEvent tr ev).2 ▸ hu))
theorem preserves_genRand_noNewBase {tr₀ : ExecTrace} (n : Nat) : CompTrace.Preserves (NoNewBase tr₀) (Random.genRand n : Traceful DY.Bytes) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_rnd tr n u).mp ((TR.Runs.genRand tr n).2 ▸ hu))
theorem hbase_of_openSteps {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hmr : ModelRun r ms) (hopen : ∀ k, k ≠ 0 → k ≠ 2 → k ≠ 9 → k ≠ 19 → k ≠ 20 → StepOK i r S g ms b k) : ∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull i r S g ms b u := by
  have hReach : ∀ (tr : ExecTrace), tr.Reachable reachability → tr ≤ runTraceMoves r ms → BaseGood i r S g ms b tr := by
    intro tr hreach; induction hreach with
    | Base => intro _ _ hu; exact False.elim ((Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 _).mp hu)
    | @Step trPre input hPre hReachPre ih =>
      intro hle; have hpreT : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle; have hgood : BaseGood i r S g ms b trPre := ih hpreT
      rcases input with ⟨⟨k, hk⟩, inp⟩
      by_cases hk0 : k = 0
      · subst hk0; intro u hu
        change ((DY.Network.sendMessage inp).run trPre).2.val.BaseAttackerKnows u at hu
        rw [(TR.Runs.sendMessage trPre inp).2] at hu
        rcases (CompTrace.baseAttackerKnows_append_net trPre inp u).mp hu with rfl | hu'
        · exact ptAvoidFull_of_attackerKnows_le hpreT hgood hPre
        · exact hgood u hu'
      by_cases h2 : k = 2
      · subst h2; rcases inp with ⟨p, skIdx⟩; intro u hu; refine hgood u ?_; revert u hu
        exact (by unfold DY.Libsignal.PQXDH.registerCorruptIdentity
                  exact CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
                    CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ =>
                      CompTrace.Preserves.bind (preserves_logPQ_noNewBase _) fun _ => preserves_logPQ_noNewBase _ :
          CompTrace.Preserves (NoNewBase trPre) (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx)) trPre (fun _ h => h)
      by_cases h9 : k = 9
      · subst h9; rcases inp with ⟨me, stateIdx⟩; intro u hu; refine hgood u ?_; revert u hu
        exact (by unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
                  exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr _ _) fun _ =>
                    CompTrace.Preserves.bind (preserves_genRand_noNewBase _) fun _ => CompTrace.Preserves.failure :
          CompTrace.Preserves (NoNewBase trPre) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx)) trPre (fun _ h => h)
      by_cases h19 : k = 19
      · subst h19; exact fun u hu => hgood u ((preserves_logPQ_noNewBase DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH) trPre (fun _ h => h) u hu)
      by_cases h20 : k = 20
      · subst h20; exact fun u hu => hgood u ((preserves_logPQ_noNewBase DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM) trPre (fun _ h => h) u hu)
      exact hopen k hk0 h2 h9 h19 h20 trPre ⟨⟨k, hk⟩, inp⟩ rfl hReachPre hPre hle hgood
  exact hReach _ hmr.2.2.1.1 (Trace.le_refl _)
def AesSafe (b x : HwBytes) : Prop := x ≠ b ∧ ∀ k iv : HwBytes, compAesPerm k iv x ≠ b
theorem aesSafe_of_len {b x : HwBytes} (hb : b.length ≤ 6) (h6 : 6 < x.length) (_h16 : x.length ≠ 16) : AesSafe b x := by
  refine ⟨fun h => by rw [h] at h6; omega, fun k iv h => ?_⟩
  have hgt := compAesPerm_length_ge_16 k iv x
  rw [h] at hgt; omega
theorem aesSafe_compAesPt1 {b : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) : AesSafe b compAesPt1 := ⟨compAesPt1_ne_pt38_pt78 hb, fun k iv => compAesPerm_compAesPt1_ne k iv hb⟩
def RunRandSafe (g : Ghost) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ j n : Nat, RandAt tr j n → n ≠ 0 → AesSafe b (g.σ j n)
theorem ptAvoidFull_randTerm_of_aesSafe {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {j n : Nat} (h : n ≠ 0 → AesSafe b (g.σ j n)) : PtAvoidFull i r S g ms b (randTerm j n) := by by_cases hn : n = 0 <;> [exact ptAvoidFull_randTerm_ne (.inl hn); exact ptAvoidFull_randTerm_ne (.inr (h hn).1)]
theorem ptAvoidFull_symEnc_randTerm_of_aesSafe {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {key iv : DY.Bytes} {j n : Nat} (hn : n ≠ 0) (hsafe : AesSafe b (g.σ j n)) (hk : PtAvoidFull compI0 r S g ms b key) (hiv : PtAvoidFull compI0 r S g ms b iv) : PtAvoidFull compI0 r S g ms b (DY.SymEnc.symEnc key iv (randTerm j n)) := by
  refine ptAvoidFull_symEnc_compI0_of_perm_ne ?_ hk hiv (ptAvoidFull_randTerm_of_aesSafe fun _ => hsafe)
  rw [gamma_randTerm_eq_σ j n hn]; exact hsafe.2
def TRStGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (st : DY.Libsignal.TripleRatchet.TRState) : Prop := PtAvoidFull i r S g ms b st.myIk ∧ PtAvoidFull i r S g ms b st.peerIk ∧ PtAvoidFull i r S g ms b st.rk ∧ PtAvoidFull i r S g ms b st.dhs ∧ PtAvoidFull i r S g ms b st.cks ∧ PtAvoidFull i r S g ms b st.sid ∧ PtAvoidFull i r S g ms b st.spqr ∧ (∀ d ∈ st.recv, PtAvoidFull i r S g ms b d.ratchetKey ∧ PtAvoidFull i r S g ms b d.chainKey)
theorem mem_memo_concatPrefixes_of_mem_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {x : DY.Bytes × DY.Bytes × HwBytes} :
    ∀ {ps : List DY.Bytes} {s p : DY.Bytes}, p ∈ ps → x ∈ (gamma' i S g p).memo → x ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | q :: ps, s, _, hp, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    unfold gamma'
    rw [show DY.Concat.concat q (Comparse.concatPrefixes ps s) = ({ lhs := q, rhs := Comparse.concatPrefixes ps s } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq gConcat0 (gAll i S g)]
    simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll]
    exact (List.mem_cons.mp hp).elim (fun h => Or.inr (Or.inl (h ▸ hx))) (fun hp' => Or.inr (Or.inr (mem_memo_concatPrefixes_of_mem_left hp' hx)))
theorem mem_memo_concatPrefixes_of_mem_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {x : DY.Bytes × DY.Bytes × HwBytes} :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, x ∈ (gamma' i S g s).memo → x ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | [], _, hx => by rwa [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
  | q :: ps, s, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    unfold gamma'
    rw [show DY.Concat.concat q (Comparse.concatPrefixes ps s) = ({ lhs := q, rhs := Comparse.concatPrefixes ps s } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq gConcat0 (gAll i S g)]
    simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll]; exact Or.inr (Or.inr (mem_memo_concatPrefixes_of_mem_right ps hx))
theorem mem_slowBytes_serialize_self (y : DY.Bytes) : y ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize y := by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
theorem mem_memo_serialize_recvList_of_mem {i : ExternInterpretation} {S : Sem} {g : Ghost} {x : DY.Bytes × DY.Bytes × HwBytes} :
    ∀ (cs : List DY.Libsignal.TripleRatchet.RecvChain) {d : DY.Libsignal.TripleRatchet.RecvChain} {p : DY.Bytes}, d ∈ cs → p ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d → x ∈ (gamma' i S g p).memo → x ∈ (gamma' i S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs)).memo
  | [], _, _, hd, _, _ => absurd hd List.not_mem_nil
  | c :: cs, d, p, hd, hp, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons]
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact mem_memo_concatPrefixes_of_mem_left hp hx
    · exact mem_memo_concatPrefixes_of_mem_right _ (mem_memo_serialize_recvList_of_mem cs hd' hp hx)
def RunTRStatesGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ (p : Participant) (st : DY.Libsignal.TripleRatchet.TRState) (j : Nat), TRStateStoredAt p st j tr → TRStGood i r S g ms b st
theorem runTRStatesGood_of_storedStates {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr : ExecTrace} (hst : ∀ ls ∈ storedStates r tr, PtAvoidFull i r S g ms b (Comparse.serialize ls)) (hmem : ∀ (p : Participant) (st : DY.Libsignal.TripleRatchet.TRState) (j : Nat), TRStateStoredAt p st j tr → (⟨p, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) ∈ storedStates r tr) : RunTRStatesGood i r S g ms b tr := by
  intro p st j hat
  let ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState := ⟨p, st⟩
  have h := hst ls (hmem p st j hat)
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  have hpre : ∀ y, y ∈ trStatePrefixes ls → PtAvoidFull i r S g ms b y :=
    fun y hy x hx => h x (by rw [hser]; exact mem_memo_concatPrefixes_of_mem_left hy hx)
  have hrecv : ∀ d ∈ ls.state.recv, ∀ y, y ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d → PtAvoidFull i r S g ms b y :=
    fun d hd y hy x hx => h x (by rw [hser]; exact mem_memo_concatPrefixes_of_mem_right _ (mem_memo_serialize_recvList_of_mem _ hd hy hx))
  refine ⟨hpre _ ?_, hpre _ ?_, hpre _ ?_, hpre _ ?_, hpre _ ?_, hpre _ ?_, hpre _ ?_, fun d hd => ⟨hrecv d hd _ ?_, hrecv d hd _ ?_⟩⟩
  all_goals first
    | (rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq d]
       first | exact List.mem_append_left _ (mem_slowBytes_serialize_self _) | exact List.mem_append_right _ (List.mem_append_left _ (mem_slowBytes_serialize_self _)))
    | (unfold trStatePrefixes; dsimp only [ls]; simp only [List.mem_append, mem_slowBytes_serialize_self, true_or, or_true])
theorem at?_eq_of_le_of_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr') {j : Nat} (hj : j < tr.length) (_hj' : j < tr'.length) : (tr'.at? j : Option E) = (tr.at? j : Option E) := Symbolic.Swarm.CREF.XplSteps.xat?_le_eq hle hj
theorem mem_storedStates_iff {r : Records} {tr : ExecTrace} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} : ls ∈ storedStates r tr ↔ ∃ j, (setupTrace r).length ≤ j ∧ j < tr.length ∧ (tr.at? j : Option TRStEntry) = some ⟨ls⟩ := by
  unfold storedStates newIndices DY.ExecTrace.getLocalStateAt; simp only [List.mem_filterMap, List.mem_range'_1, Option.map_eq_some_iff]
  exact ⟨fun ⟨j, ⟨hge, _⟩, ⟨_⟩, hat, rfl⟩ => ⟨j, hge, by omega, hat⟩, fun ⟨j, hge, _, hat⟩ => ⟨j, ⟨hge, by omega⟩, ⟨ls⟩, hat, rfl⟩⟩
theorem mem_storedStates_of_storedAt {r : Records} {tr : ExecTrace} (hsle : setupTrace r ≤ tr) {p : Participant} {st : DY.Libsignal.TripleRatchet.TRState} {j : Nat} (hat : TRStateStoredAt p st j tr) : (⟨p, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) ∈ storedStates r tr := by
  have hlt : j < tr.length := by
    have h1 := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr j
    unfold TRStateStoredAt at hat; rwa [hat] at h1
  refine mem_storedStates_iff.mpr ⟨j, ?_, hlt, hat⟩
  by_contra h; have hj : j < (setupTrace r).length := by omega
  have heq := at?_eq_of_le_of_lt (E := TRStEntry) hsle hj hlt; rw [hat, noTRState_setupTrace r j] at heq; cases heq
theorem setupTrace_le_runTrace' (r : Records) (ms : List Move) : setupTrace r ≤ runTraceMoves r ms := by rw [Symbolic.Swarm.CREF.xpl_runTrace_eq]; exact Symbolic.Swarm.CREF.runMoves_le ms (setupTrace r)
def RunPQSecretsGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) (j : Nat), PQXDHStoredAt tr p st j → PtAvoidFull i r S g ms b st.sk
theorem runPQSecretsGood_of_no_setup {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hmr : ModelRun r ms) : RunPQSecretsGood i r S g ms b (runTraceMoves r ms) := by
  have hinv := PtPrefixInv35.storedSecrets_inv_of_no_setup hwf hmr.2.1 hmr.2.2.1.1
  intro p st j hat; refine ptAvoidFull_of_memoInjGt (Nat.le_refl b.length) ?_
  have hsec := memoInjGt_setupSecret hcompat hwf hb
  rcases hinv j ⟨⟨p, st⟩⟩ hat with h0 | h1 | h2 | h4 | ⟨hopk, h22⟩
  · rw [h0]; exact hsec 0
  · rw [h1]; exact hsec 1
  · rw [h2]; exact hsec 2
  · rw [h4]; exact hsec 4
  · rw [h22]; exact memoInjGt_setup_randTerm hcompat hwf hb (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp [hopk])
theorem preserves_logTR_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (ev : DY.Libsignal.TripleRatchet.TREvent) : CompTrace.Preserves (BaseGood i r S g ms b) (ProtocolEvent.logEvent ev) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_trEv tr ev u).mp (by rwa [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq] at hu))
theorem preserves_logPQ_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (ev : DY.Libsignal.PQXDH.PQXDHEvent) : CompTrace.Preserves (BaseGood i r S g ms b) (ProtocolEvent.logEvent ev) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_pqEv tr ev u).mp ((TR.Runs.logEvent tr ev).2 ▸ hu))
theorem preserves_send_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {msg : DY.Bytes} (hmsg : PtAvoidFull i r S g ms b msg) : CompTrace.Preserves (BaseGood i r S g ms b) (Network.sendMessage msg) := by intro tr h u hu; rcases (CompTrace.baseAttackerKnows_append_net tr msg u).mp ((TR.Runs.sendMessage tr msg).2 ▸ hu) with rfl | hu' <;> [exact hmsg; exact h u hu']
theorem preserves_logTR_send_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (ev : DY.Libsignal.TripleRatchet.TREvent) {msg : DY.Bytes} (hmsg : PtAvoidFull i r S g ms b msg) : CompTrace.Preserves (BaseGood i r S g ms b) (ProtocolEvent.logEvent ev >>= fun _ => Network.sendMessage msg) := CompTrace.Preserves.bind (preserves_logTR_baseGood ev) fun _ => preserves_send_baseGood hmsg
theorem preserves_logPQ_send_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (ev : DY.Libsignal.PQXDH.PQXDHEvent) {msg : DY.Bytes} (hmsg : PtAvoidFull i r S g ms b msg) : CompTrace.Preserves (BaseGood i r S g ms b) (ProtocolEvent.logEvent ev >>= fun _ => Network.sendMessage msg) := CompTrace.Preserves.bind (preserves_logPQ_baseGood ev) fun _ => preserves_send_baseGood hmsg
theorem stepOK_exposeSpqr_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hst : RunTRStatesGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 13 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨me, stIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.TripleRatchet.exposeSpqr me stIdx).run trPre).2.val
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine CompTrace.bind_getLocalState_tr_at me stIdx trPre hg fun st hstS => ?_
  exact preserves_logTR_send_baseGood _ (hst me st stIdx (trStateStoredAt_mono hpre hstS)).2.2.2.2.2.2.1 trPre hg
theorem stepOK_exposeKey_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hst : RunTRStatesGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 12 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨me, stIdx, kc⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.TripleRatchet.exposeKey me stIdx kc).run trPre).2.val
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine CompTrace.bind_getLocalState_tr_at me stIdx trPre hg fun st hstS => ?_
  have hG := hst me st stIdx (trStateStoredAt_mono hpre hstS)
  cases kc with
  | rk => exact preserves_logTR_send_baseGood _ hG.2.2.1 trPre hg
  | dhs => exact preserves_logTR_send_baseGood _ hG.2.2.2.1 trPre hg
  | cks => exact preserves_logTR_send_baseGood _ hG.2.2.2.2.1 trPre hg
  | ckr pk =>
    dsimp only; rcases hc : DY.Libsignal.TripleRatchet.findRecvChain st.recv pk with _ | c
    · exact CompTrace.Preserves.failure trPre hg
    · exact preserves_logTR_send_baseGood _ (hG.2.2.2.2.2.2.2 c (List.mem_of_find?_eq_some hc)).2 trPre hg
theorem stepOK_compromiseIK_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsec : RunPQSecretsGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 15 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, stIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.compromiseIK p stIdx).run trPre).2.val
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact CompTrace.bind_getKey_at p stIdx .identity trPre hg fun sk hsk =>
    preserves_logPQ_send_baseGood _ (hsec p _ stIdx (pqxdhStoredAt_mono hpre hsk)) trPre hg
theorem stepOK_compromiseSPK_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsec : RunPQSecretsGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 16 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, stIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.compromiseSPK p stIdx).run trPre).2.val
  unfold DY.Libsignal.PQXDH.compromiseSPK
  exact CompTrace.bind_getKey_at p stIdx .signedPrekey trPre hg fun sk hsk =>
    preserves_logPQ_send_baseGood _ (hsec p _ stIdx (pqxdhStoredAt_mono hpre hsk)) trPre hg
theorem stepOK_compromisePQSPK_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsec : RunPQSecretsGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 17 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, stIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.compromisePQSPK p stIdx).run trPre).2.val
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  exact CompTrace.bind_getKey_at p stIdx .pqPrekey trPre hg fun sk hsk =>
    preserves_logPQ_send_baseGood _ (hsec p _ stIdx (pqxdhStoredAt_mono hpre hsk)) trPre hg
theorem stepOK_compromiseOPK_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsec : RunPQSecretsGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 18 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, stIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.compromiseOPK p stIdx).run trPre).2.val
  unfold DY.Libsignal.PQXDH.compromiseOPK
  exact CompTrace.bind_getKey_at p stIdx .oneTimePrekey trPre hg fun sk hsk =>
    (CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
      preserves_logPQ_send_baseGood _ (hsec p _ stIdx (pqxdhStoredAt_mono hpre hsk))) trPre hg
def RunSkippedGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ s pk n seed rIdx src (j : Nat), tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) j → PtAvoidFull i r S g ms b seed
theorem stepOK_exposeSkipped_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsk : RunSkippedGood i r S g ms b (runTraceMoves r ms)) : StepOK i r S g ms b 14 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.TripleRatchet.exposeSkipped inp).run trPre).2.val
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  rw [run_bind_snd,
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEntry_run_eq (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent) inp trPre).1,
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEntry_run_eq (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent) inp trPre).2]
  try dsimp only
  rcases he : (trPre.at? inp : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) with _ | ⟨⟨ev⟩⟩
  · exact hg
  · cases ev with
    | SkippedKeyStored s pk n seed rIdx src =>
      dsimp only
      exact (CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ =>
        preserves_logTR_send_baseGood _ (hsk s pk n seed rIdx src inp
          ((Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? _ _ _ _).mpr (at?_le_some hpre he)))) trPre hg
    | _ => dsimp only; exact CompTrace.Preserves.failure trPre hg
theorem run_guardOnTrace_bind_of_false {α : Type} (p : ExecTrace → Bool) {f : Unit → Traceful α} {tr : ExecTrace} (hp : p tr = false) : ((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val = tr := by
  rw [run_bind_snd,
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.requireTracePredicate_run_eq p tr).1,
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.requireTracePredicate_run_eq p tr).2]
  try dsimp only
  rw [ite_eq_right_iff.mpr fun h => absurd h (by rw [hp]; decide)]
theorem stepOK_invertDH_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hnb : ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH) : StepOK i r S g ms b 21 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.invertDH inp).run trPre).2.val
  have hp : DY.Libsignal.PQXDH.brokenDHB trPre = false := by
    cases h : DY.Libsignal.PQXDH.brokenDHB trPre <;> [rfl; exact absurd (CompTrace.eventLogged_mono hpre (CompPresPQXDH.eventLogged_of_brokenDHB h)) hnb]
  unfold DY.Libsignal.PQXDH.invertDH; rw [run_guardOnTrace_bind_of_false _ hp]; exact hg
theorem stepOK_invertKEM_of_run {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hnb : ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM) : StepOK i r S g ms b 22 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood i r S g ms b ((DY.Libsignal.PQXDH.invertKEM inp).run trPre).2.val
  have hp : DY.Libsignal.PQXDH.brokenKEMB trPre = false := by
    cases h : DY.Libsignal.PQXDH.brokenKEMB trPre <;> [rfl; exact absurd (CompTrace.eventLogged_mono hpre (CompPresPQXDH.eventLogged_of_brokenKEMB h)) hnb]
  unfold DY.Libsignal.PQXDH.invertKEM; rw [run_guardOnTrace_bind_of_false _ hp]; exact hg
def NoSKS (tr : ExecTrace) : Prop := ∀ (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (n : UInt32) (seed : DY.Bytes) (rIdx src j : Nat), ¬ tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) j
theorem noSKS_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} (h : NoSKS tr) (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) = none) : NoSKS (tr.append e) := fun s pk n seed rIdx src j hj => h s pk n seed rIdx src j (eventLoggedAt_append_other hnone hj)
theorem noSKS_append_tr {tr : ExecTrace} (h : NoSKS tr) (ev : DY.Libsignal.TripleRatchet.TREvent) (hne : ∀ s pk n seed rIdx src, ev ≠ .SkippedKeyStored s pk n seed rIdx src) : NoSKS (tr.append (TREvE ev)) := by
  intro s pk n seed rIdx src j hj; rcases eventLoggedAt_append_same hj with ⟨_, hj'⟩ | ⟨_, heq⟩
  · exact h s pk n seed rIdx src j hj'
  · exact hne s pk n seed rIdx src heq
theorem NoSKS.preserves_genRand (n : Nat) : CompTrace.Preserves NoSKS (DY.Random.genRand n) := fun tr h => (TR.Runs.genRand tr n).2.symm ▸ noSKS_append_other h (RndE n) rfl
theorem NoSKS.preserves_sendMessage (msg : DY.Bytes) : CompTrace.Preserves NoSKS (DY.Network.sendMessage msg) := fun tr h => (TR.Runs.sendMessage tr msg).2.symm ▸ noSKS_append_other h (NetE msg) rfl
theorem NoSKS.preserves_logEvent_pq (ev : DY.Libsignal.PQXDH.PQXDHEvent) : CompTrace.Preserves NoSKS (DY.ProtocolEvent.logEvent ev) := fun tr h => (TR.Runs.logEvent tr ev).2.symm ▸ noSKS_append_other h (PQEvE ev) rfl
theorem NoSKS.preserves_storeLocalState_pq (me : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState) : CompTrace.Preserves NoSKS (DY.PersistentLocalState.storeLocalState me st) := fun tr h => (TR.Runs.storeLocalState tr me st).2.symm ▸ noSKS_append_other h (PQStE me st) rfl
theorem NoSKS.preserves_getKey (p : DY.Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) : CompTrace.Preserves NoSKS (DY.Libsignal.PQXDH.getKey p stateIdx kind) := CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
theorem noSKS_setupTrace (r : Records) : NoSKS (setupTrace r) := by
  have hreg : ∀ p, CompTrace.Preserves NoSKS (DY.Libsignal.PQXDH.registerIdentity p) := fun p => by
    unfold DY.Libsignal.PQXDH.registerIdentity
    exact CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_genRand 32) fun _ =>
      CompTrace.Preserves.bind (NoSKS.preserves_logEvent_pq _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ =>
        CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => NoSKS.preserves_storeLocalState_pq p _
  have hact : CompTrace.Preserves NoSKS (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct DY.Libsignal.PQXDH.genSignedPrekey DY.Libsignal.PQXDH.genPQPrekey DY.Libsignal.PQXDH.genOneTimePrekey
    refine CompTrace.Preserves.bind (hreg r.alice) fun _ => CompTrace.Preserves.bind (hreg r.bob) fun hB =>
      CompTrace.Preserves.bind (CompTrace.Preserves.bind (NoSKS.preserves_getKey r.bob hB .identity) fun _ =>
        CompTrace.Preserves.bind (NoSKS.preserves_genRand 32) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_genRand 64) fun _ =>
          CompTrace.Preserves.bind (NoSKS.preserves_logEvent_pq _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_storeLocalState_pq r.bob _) fun _ =>
            CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.bind (NoSKS.preserves_getKey r.bob hB .identity) fun _ =>
        CompTrace.Preserves.bind (NoSKS.preserves_genRand 64) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_genRand 64) fun _ =>
          CompTrace.Preserves.bind (NoSKS.preserves_logEvent_pq _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_storeLocalState_pq r.bob _) fun _ =>
            CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _) fun _ => ?_
    cases r.withOpk
    · exact CompTrace.Preserves.pure ()
    · simp only [↓reduceIte]
      exact CompTrace.Preserves.bind (CompTrace.Preserves.bind (NoSKS.preserves_genRand 32) fun _ =>
        CompTrace.Preserves.bind (NoSKS.preserves_logEvent_pq _) fun _ => CompTrace.Preserves.bind (NoSKS.preserves_storeLocalState_pq r.bob _) fun _ =>
          CompTrace.Preserves.bind (NoSKS.preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _) fun _ => CompTrace.Preserves.pure ()
  exact hact Trace.nil (fun _ _ _ _ _ _ _ h => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.not_eventLoggedAt_nil h)
theorem noSKS_of_noSessionEffect {tr : ExecTrace} {m : Move} (htr : NoSKS tr) (heff : NoSessionEffect tr m) : NoSKS (m.next tr) := by
  intro s pk n seed rIdx src j h
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at?] at h
  have hj' : j < (m.next tr).length := by
    have h1 := DY.Trace.at?_eq_some_implies_length_le
      (EntryT := DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent) (m.next tr) j
    rwa [h] at h1
  by_cases hj : j < tr.length
  · rw [at?_eq_of_le_of_lt (m.le_next tr) hj hj'] at h
    exact htr s pk n seed rIdx src j ((Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? _ _ _ _).mpr h)
  · rw [(heff j (XplSteps.xpl_mem_newIndices (by omega) hj')).2.2.1] at h; cases h
theorem noSKS_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (htr : NoSKS tr) (hδ : MovesFrom InvisibleNoEffect tr δ) : NoSKS (runMoves δ tr).1 := by induction δ generalizing tr with | nil => exact htr | cons _ _ ih => exact ih (noSKS_of_noSessionEffect htr hδ.1.2) hδ.2
theorem noSKS_iniAliceStartTr {tr : ExecTrace} (h : NoSKS tr) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : NoSKS (iniAliceStartTr tr a b o) := by
  unfold iniAliceStartTr; dsimp only
  exact noSKS_append_other (noSKS_append_other (noSKS_append_tr (noSKS_append_other (noSKS_append_other (noSKS_append_other (noSKS_append_other (noSKS_append_other (noSKS_append_other h _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl)
    _ (fun _ _ _ _ _ _ h => by cases h)) _ rfl) _ rfl
theorem noSKS_encNextTr {tr₂ : ExecTrace} (h : NoSKS tr₂) (me : DY.Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : NoSKS (encNextTr tr₂ me sIdx stA cl pq) := by
  unfold encNextTr encPreSaltTr; dsimp only
  exact noSKS_append_other (noSKS_append_other (noSKS_append_tr (noSKS_append_tr (noSKS_append_other
    (noSKS_append_other (noSKS_append_other h _ rfl) _ rfl) _ rfl) _ (fun _ _ _ _ _ _ h => by cases h))
    _ (fun _ _ _ _ _ _ h => by cases h)) _ rfl) _ rfl
theorem runSkippedGood_of_noSKS {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (h : NoSKS (runTraceMoves r ms)) : RunSkippedGood i r S g ms b (runTraceMoves r ms) := fun s pk n seed rIdx src j hj => absurd hj (h s pk n seed rIdx src j)
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach
