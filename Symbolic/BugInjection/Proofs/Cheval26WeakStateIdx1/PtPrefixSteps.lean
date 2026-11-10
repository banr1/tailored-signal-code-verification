/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Concat

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown hiding bytes_rec_gAll
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def UpTo (T : ExecTrace) (Inv : ExecTrace → Prop) (tr : ExecTrace) : Prop := tr ≤ T → Inv tr
theorem Preserves.upTo {T : ExecTrace} {Inv : ExecTrace → Prop} {α : Type} {m : Traceful α} (h : CompTrace.Preserves Inv m) : CompTrace.Preserves (UpTo T Inv) m := fun tr hI hle => h tr (hI (Trace.le_trans _ _ _ (XplSteps.xrun_le _ tr) hle))
theorem upTo_genRand_bind {T : ExecTrace} {Inv : ExecTrace → Prop} {α : Type} (n : Nat) {f : DY.Bytes → Traceful α} (hInv : ∀ tr : ExecTrace, Inv tr → Inv (tr.append (RndE n))) (hf : ∀ tr : ExecTrace, RandAt T tr.length n → CompTrace.Preserves (UpTo T Inv) (f (mkRand tr.length n))) : CompTrace.Preserves (UpTo T Inv) (Random.genRand n >>= f) := by
  intro tr hI; rw [CompTrace.run_genRand_bind_snd]; intro hle; have h1 : tr.append (RndE n) ≤ T := Trace.le_trans _ _ _ (XplSteps.xrun_le _ _) hle
  exact hf tr (randAt_mono h1 (randAt_here tr n)) _ (fun _ => hInv tr (hI (Trace.le_trans _ _ _ (Trace.append_le _ _) h1))) hle
theorem baseGood_append_rnd {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (tr : ExecTrace) (n : Nat) (h : BaseGood i r S g ms b tr) : BaseGood i r S g ms b (tr.append (RndE n)) := fun u hu => h u ((CompTrace.baseAttackerKnows_append_rnd tr n u).mp hu)
theorem preserves_storePQ_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) : CompTrace.Preserves (BaseGood i r S g ms b) (PersistentLocalState.storeLocalState p st) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_pqSt tr p st u).mp ((TR.Runs.storeLocalState tr p st).2 ▸ hu))
theorem ptAvoidFull_mkRand_of_runRandSafe {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {T : ExecTrace} {j n : Nat} (hrs : RunRandSafe g b T) (hat : RandAt T j n) : PtAvoidFull i r S g ms b (mkRand j n) := ptAvoidFull_randTerm_of_aesSafe fun hn => hrs j n hat hn
theorem stepOK_registerIdentity_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 32) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 1 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg
  refine (?_ : CompTrace.Preserves (UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b)) (DY.Libsignal.PQXDH.registerIdentity inp)) trPre (fun _ => hg) hle
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (Preserves.upTo (CompTrace.Preserves.requireTracePredicate _)) fun _ =>
    upTo_genRand_bind 32 (fun tr h => baseGood_append_rnd tr 32 h) fun tr hat => ?_
  have hik := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat
  exact Preserves.upTo (CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ =>
    CompTrace.Preserves.bind (preserves_send_baseGood (ptAvoidFull_dhPk_compI0 hb hik)) fun _ =>
      CompTrace.Preserves.bind (preserves_send_baseGood (ptAvoidFull_vk hik)) fun _ => preserves_storePQ_baseGood _ _)
theorem stepOK_genOneTimePrekey_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 32) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 5 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg
  refine (?_ : CompTrace.Preserves (UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b)) (DY.Libsignal.PQXDH.genOneTimePrekey inp)) trPre (fun _ => hg) hle
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine upTo_genRand_bind 32 (fun tr h => baseGood_append_rnd tr 32 h) fun tr hat => ?_
  have hopk := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat
  exact Preserves.upTo (CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ =>
    CompTrace.Preserves.bind (preserves_storePQ_baseGood _ _) fun _ =>
      CompTrace.Preserves.bind (preserves_send_baseGood (ptAvoidFull_dhPk_compI0 hb hopk)) fun _ => CompTrace.Preserves.pure _)
theorem stepOK_genSignedPrekey_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 32) (hsec : RunPQSecretsGood compI0 r S g ms b (runTraceMoves r ms)) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 3 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, idx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  refine (?_ : UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b) ((DY.Libsignal.PQXDH.genSignedPrekey p idx).run trPre).2.val) hle
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.bind_getKey_at p idx .identity trPre (fun _ => hg) fun ik hik => ?_
  have hikG : PtAvoidFull compI0 r S g ms b ik := hsec p _ idx (pqxdhStoredAt_mono hpre hik)
  refine upTo_genRand_bind 32 (fun tr h => baseGood_append_rnd tr 32 h) (fun tr hat => ?_) trPre (fun _ => hg)
  refine upTo_genRand_bind 64 (fun tr h => baseGood_append_rnd tr 64 h) fun tr' hat' => ?_
  have hpk := ptAvoidFull_dhPk_compI0 hb (ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat); have hnon := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat'
  exact Preserves.upTo (CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ =>
    CompTrace.Preserves.bind (preserves_storePQ_baseGood _ _) fun _ =>
      CompTrace.Preserves.bind (preserves_send_baseGood hpk) fun _ =>
        CompTrace.Preserves.bind (preserves_send_baseGood (ptAvoidFull_sign hikG hnon (ptAvoidFull_encodeEC hpk))) fun _ => CompTrace.Preserves.pure _)
theorem stepOK_genPQPrekey_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hsec : RunPQSecretsGood compI0 r S g ms b (runTraceMoves r ms)) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 4 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨p, idx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  refine (?_ : UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b) ((DY.Libsignal.PQXDH.genPQPrekey p idx).run trPre).2.val) hle
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.bind_getKey_at p idx .identity trPre (fun _ => hg) fun ik hik => ?_
  have hikG : PtAvoidFull compI0 r S g ms b ik := hsec p _ idx (pqxdhStoredAt_mono hpre hik)
  refine upTo_genRand_bind 64 (fun tr h => baseGood_append_rnd tr 64 h) (fun tr hat => ?_) trPre (fun _ => hg)
  refine upTo_genRand_bind 64 (fun tr h => baseGood_append_rnd tr 64 h) fun tr' hat' => ?_
  have hpk := ptAvoidFull_kemPk (ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat); have hnon := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hat'
  exact Preserves.upTo (CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ =>
    CompTrace.Preserves.bind (preserves_storePQ_baseGood _ _) fun _ =>
      CompTrace.Preserves.bind (preserves_send_baseGood hpk) fun _ =>
        CompTrace.Preserves.bind (preserves_send_baseGood (ptAvoidFull_sign hikG hnon (ptAvoidFull_encodeKEM hpk))) fun _ => CompTrace.Preserves.pure _)
theorem preserves_logC_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (ev : CEvent) : CompTrace.Preserves (BaseGood i r S g ms b) (ProtocolEvent.logEvent ev) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_cEv tr ev u).mp (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq ev tr ▸ hu))
theorem preserves_storeTR_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (p : Participant) (st : DY.Libsignal.TripleRatchet.TRState) : CompTrace.Preserves (BaseGood i r S g ms b) (PersistentLocalState.storeLocalState p st) := fun tr h u hu => h u ((CompTrace.baseAttackerKnows_append_trSt tr p st u).mp (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.storeLocalState_tr_snd_eq p st tr ▸ hu))
theorem stepOK_aliceStart_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 32) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 6 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨a, bb, idIdx, regIdx, bh⟩
  refine (?_ : UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b) ((DY.Libsignal.Composed.aliceStart a bb idIdx regIdx bh).run trPre).2.val) hle
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a bb idIdx regIdx bh trPre (fun _ => hg) (fun _ => baseGood_append_rnd trPre 32 hg) ?_
  intro ikA ikB vkB spk spkSig pqpk pqpkSig opk honest _ _ _ _ hpq _ _ _ _ _ _ hle2; have h2 := Trace.le_trans _ _ _ (XplSteps.xrun_le _ _) hle2; have h1 : trPre.append (RndE 32) ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (Trace.append_le _ _) h2; have hekPk := ptAvoidFull_dhPk_compI0 hb (ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs (randAt_mono h1 (randAt_here trPre 32)))
  have he := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs (randAt_mono h2 (randAt_here (trPre.append (RndE 32)) 32)); have hct := ptAvoidFull_kemEncap_fst_compI0 hb (hg pqpk hpq.baseAttackerKnows) he; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq] at hct; have hg2 : BaseGood compI0 r S g ms b ((trPre.append (RndE 32)).append (RndE 32)) := baseGood_append_rnd _ 32 (baseGood_append_rnd trPre 32 hg); revert hle2
  refine upTo_genRand_bind 32 (fun tr h => baseGood_append_rnd tr 32 h) (fun tr _ => ?_) _ (fun _ => hg2)
  refine Preserves.upTo ?_; split; dsimp only [aliceOut, DY.Libsignal.PQXDH.aliceAgreement]
  exact CompTrace.Preserves.bind (preserves_send_baseGood hekPk) fun _ =>
    CompTrace.Preserves.bind (preserves_send_baseGood hct) fun _ =>
      CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
        CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ =>
          CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
            CompTrace.Preserves.bind (preserves_logC_baseGood _) fun _ => preserves_storeTR_baseGood _ _
theorem attackerKnows_pqRatchet_of_parseTrSignalMsg {tr : ExecTrace} {t : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} (ht : t.AttackerKnows tr) (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg) : msg.pqRatchet.AttackerKnows tr := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse; dsimp only [bind, Option.bind] at hparse
  rcases hsp : Concat.split t (t.length - DY.Trunc.trunc8Length) with _ | ⟨wire, mac⟩ <;> rw [hsp] at hparse
  · cases hparse
  · dsimp only at hparse
    rcases hfw : DY.TrWire.trWireMsgFields? wire with _ | x <;> rw [hfw] at hparse
    · cases hparse
    · injection hparse with hmsg; subst hmsg
      have hsp_ak := Concat.attacker_knows_split t (t.length - DY.Trunc.trunc8Length) tr ht; rw [hsp] at hsp_ak; have hw := hsp_ak.1; rw [DY.TrWire.trWireMsg_of_fields? hfw] at hw; exact (DY.TrWire.attacker_knows_trWireMsg_args x.version x.senderRatchetKey x.counter x.previousCounter x.ciphertext x.pqRatchet x.encodingVariation tr hw).2.2
theorem bind_receiveSignalMsg_ak {Inv : ExecTrace → Prop} {α : Type} (msgH : Nat) {f : DY.Libsignal.TripleRatchet.TRSignalMsg → Traceful α} (tr : ExecTrace) (hInv : Inv tr) (hf : ∀ msg : DY.Libsignal.TripleRatchet.TRSignalMsg, msg.pqRatchet.AttackerKnows tr → Inv ((f msg).run tr).2.val) : Inv ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH >>= f).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at msgH tr hInv fun raw _ hraw => ?_
  rcases hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw with _ | msg
  · dsimp only
    simp only [CompTrace.run_bind_snd,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_failure_fst,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_failure_snd]
    exact hInv
  · dsimp only; rw [CompTrace.run_bind_assoc_snd]
    exact CompTrace.bind_guardP_at _ tr hInv fun _ => hf msg (attackerKnows_pqRatchet_of_parseTrSignalMsg hraw hp)
theorem preserves_ensureReceiverChain_bind {Inv : ExecTrace → Prop} {α : Type} (st₀ : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) {f : DY.Libsignal.TripleRatchet.TRState × DY.Libsignal.TripleRatchet.RecvChain × Bool → Traceful α} (hInv : ∀ tr : ExecTrace, Inv tr → Inv (tr.append (RndE 32))) (hf : ∀ x : DY.Libsignal.TripleRatchet.TRState × DY.Libsignal.TripleRatchet.RecvChain × Bool, x.1.spqr = st₀.spqr → CompTrace.Preserves Inv (f x)) : CompTrace.Preserves Inv (DY.Libsignal.TripleRatchet.ensureReceiverChain st₀ pk >>= f) := by
  intro tr h
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · rw [CompTrace.run_pure_bind_snd]; exact hf _ rfl tr h
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr h fun _ => ?_
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_genRand_bind_snd]
    dsimp only
    rw [CompTrace.run_pure_bind_snd, CompTrace.run_pure_bind_snd]
    exact hf _ rfl _ (hInv tr h)
  · simp only [CompTrace.run_bind_snd,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_failure_fst,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_failure_snd]
    exact h
theorem preserves_logSkippedKeys_baseGood {i : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {ms : List Move} {b : HwBytes} (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (count : Nat) (ck : DY.Bytes) (idx : UInt32), CompTrace.Preserves (BaseGood i r S g ms b) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck idx count)
  | 0, _, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact CompTrace.Preserves.pure ()
  | count + 1, ck, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logSkippedKeys_baseGood s pk rIdx src count _ _
theorem preserves_logMessageKeyAndStore_baseGood {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) (st : DY.Libsignal.TripleRatchet.TRState) : CompTrace.Preserves (BaseGood i r S g ms b) (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_storeTR_baseGood _ _
theorem stepOK_messageDecrypt_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hst : RunTRStatesGood compI0 r S g ms b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 10 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨me, stIdx, msgIdx, pqIdx, spqrIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood compI0 r S g ms b ((DY.Libsignal.TripleRatchet.messageDecrypt me stIdx msgIdx pqIdx spqrIdx).run trPre).2.val
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine CompTrace.bind_getLocalState_tr_at me stIdx trPre hg fun st hstS => ?_
  have hG := hst me st stIdx (trStateStoredAt_mono hpre hstS)
  refine bind_receiveSignalMsg_ak msgIdx trPre hg fun msg hmsg => ?_
  have hpq : PtAvoidFull compI0 r S g ms b msg.pqRatchet := ptAvoidFull_of_attackerKnows_le hpre hg hmsg
  refine preserves_ensureReceiverChain_bind st msg.ratchetKey (fun tr h => baseGood_append_rnd tr 32 h) (fun x hx => ?_) trPre hg
  rcases x with ⟨st', c, ratcheted⟩; dsimp only at hx ⊢
  rcases hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact CompTrace.Preserves.failure
  rcases hrecv : DY.Spqr.spqrRecv st'.spqr msg.pqRatchet spqrIdx with _ | ⟨spqr', kk⟩
  · exact CompTrace.Preserves.failure
  have hkey : PtAvoidFull compI0 r S g ms b kk := ptAvoidFull_spqrRecvKey_of hrecv (by rw [hx]; exact hG.2.2.2.2.2.2.1) hpq
  dsimp only
  refine CompTrace.Preserves.bind (preserves_send_baseGood hkey) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
  split
  · exact CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
      CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
        CompTrace.Preserves.bind (preserves_logSkippedKeys_baseGood _ _ _ _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _
  · exact CompTrace.Preserves.bind (preserves_logSkippedKeys_baseGood _ _ _ _ _ _ _) fun _ =>
      CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _
theorem stepOK_messageDecryptSkipped_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hst : RunTRStatesGood compI0 r S g ms b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 11 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨me, stIdx, msgIdx, skIdx, pqIdx, spqrIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  show BaseGood compI0 r S g ms b ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stIdx msgIdx skIdx pqIdx spqrIdx).run trPre).2.val
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine CompTrace.bind_getLocalState_tr_at me stIdx trPre hg fun st hstS => ?_
  have hG := hst me st stIdx (trStateStoredAt_mono hpre hstS)
  refine bind_receiveSignalMsg_ak msgIdx trPre hg fun msg hmsg => ?_
  have hpq : PtAvoidFull compI0 r S g ms b msg.pqRatchet := ptAvoidFull_of_attackerKnows_le hpre hg hmsg
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry _) (fun e => ?_) trPre hg
  split
  · refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.guardTrace _) fun _ => ?_
    rcases hrecv : DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrIdx with _ | ⟨spqr', kk⟩
    · exact CompTrace.Preserves.failure
    have hkey : PtAvoidFull compI0 r S g ms b kk := ptAvoidFull_spqrRecvKey_of hrecv hG.2.2.2.2.2.2.1 hpq; dsimp only
    exact CompTrace.Preserves.bind (preserves_send_baseGood hkey) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ =>
        CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
          CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
            CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _
  · exact CompTrace.Preserves.failure
theorem upTo_receiveMessage_bind {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {α : Type} (h : Nat) {f : DY.Bytes → Traceful α} (hf : ∀ (x : DY.Bytes) (tr : ExecTrace), tr ≤ runTraceMoves r ms → BaseGood i r S g ms b tr → x.AttackerKnows tr → UpTo (runTraceMoves r ms) (BaseGood i r S g ms b) ((f x).run tr).2.val) : CompTrace.Preserves (UpTo (runTraceMoves r ms) (BaseGood i r S g ms b)) (Network.receiveMessage h >>= f) := by
  intro tr hI
  refine CompTrace.bind_receiveMessage_at h tr hI fun x _ hx hle => ?_
  have htr : tr ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ tr) hle; exact hf x tr htr (hI htr) hx hle
theorem stepOK_messageEncrypt_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 8) (hst : RunTRStatesGood compI0 r S g ms b (runTraceMoves r ms)) (hrs : RunRandSafe g b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 8 := by
  have hb32 : b.length < 32 := by omega
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨me, stIdx, coinsLen, pqIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  refine (?_ : UpTo (runTraceMoves r ms) (BaseGood compI0 r S g ms b) ((DY.Libsignal.TripleRatchet.messageEncrypt me stIdx coinsLen pqIdx).run trPre).2.val) hle
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine CompTrace.bind_getLocalState_tr_at me stIdx trPre (fun _ => hg) fun st hstS => ?_
  have hG := hst me st stIdx (trStateStoredAt_mono hpre hstS)
  refine CompTrace.Preserves.bind (Preserves.upTo (CompTrace.Preserves.guardP _)) (fun _ => ?_) trPre (fun _ => hg)
  refine upTo_genRand_bind 32 (fun tr h => baseGood_append_rnd tr 32 h) fun trm hatm => ?_
  refine upTo_genRand_bind coinsLen (fun tr h => baseGood_append_rnd tr coinsLen h) fun trc hatc => ?_
  have hcoins := ptAvoidFull_mkRand_of_runRandSafe (i := compI0) (r := r) (S := S) (ms := ms) hrs hatc; have hspqr := hG.2.2.2.2.2.2.1; have hkey := ptAvoidFull_spqrSendKey hspqr hcoins; have hpqMsg := ptAvoidFull_spqrSendMsg hspqr hcoins
  rcases hsend : DY.Spqr.spqrSend st.spqr (mkRand trc.length coinsLen) with ⟨spqr', kk, pqMsg⟩
  rw [hsend] at hkey hpqMsg; dsimp only at hkey hpqMsg ⊢
  refine CompTrace.Preserves.bind (Preserves.upTo (preserves_send_baseGood hkey)) fun _ => ?_
  have hseed := ptAvoidFull_kdfCk_snd hb32 hG.2.2.2.2.1
  rcases hkdf : DY.Libsignal.TripleRatchet.kdfCk st.cks with ⟨ck', seed⟩
  rw [hkdf] at hseed; dsimp only at hseed ⊢
  refine upTo_receiveMessage_bind pqIdx fun pqSalt tr htr hgood hak => ?_
  have hkeys := ptAvoidFull_trMsgKeys hb32 (ptAvoidFull_of_attackerKnows_le htr hgood hak) hseed
  have hct := ptAvoidFull_symEnc_randTerm_of_aesSafe (by decide) (hrs _ _ hatm (by decide)) hkeys.1 hkeys.2.2
  have hdhs := ptAvoidFull_dhPk_compI0 hb32 hG.2.2.2.1
  refine Preserves.upTo ?_ tr (fun _ => hgood)
  exact CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
    CompTrace.Preserves.bind (preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _) fun _ =>
      preserves_send_baseGood (ptAvoidFull_concat (ptAvoidFull_trWireMsg hdhs hct hpqMsg) (ptAvoidFull_computeMac hb hkeys.2.1 hG.1 hG.2.1 (ptAvoidFull_trWireMsg hdhs hct hpqMsg)))
def RunPKIGood (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (tr : ExecTrace) : Prop := ∀ (p : Participant) (ik vk : DY.Bytes) (hon : Bool) (j : Nat), tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p ik vk hon) j → PtAvoidFull i r S g ms b ik
theorem runPKIGood_of_no_setup {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hns : ∀ m ∈ ms, m.isSetup = false) : RunPKIGood compI0 r S g ms b (runTraceMoves r ms) := by
  intro p ik vk hon j hev; have h0 := noNewNonMovePQEv_runTrace r ms hns _ j rfl hev
  have hpk : ∀ t, (t, 32) ∈ setupRandomsAt r → PtAvoidFull compI0 r S g ms b (DY.DiffieHellman.dhPk (randTerm t 32)) :=
    fun t ht => ptAvoidFull_of_memoInjGt (Nat.le_refl _) (memoInjGt_dhPk_compI0 hb (memoInjGt_setup_randTerm hcompat hwf hb ht))
  rcases setupTrace_eventLoggedAt_cases hwf.1 h0 with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, _, heq⟩
  · injection heq with _ hik; rw [hik, Common443.CompSetupSecrecy.setupPublic_0 hwf.1]; exact hpk 0 (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · injection heq with _ hik; rw [hik, Common443.CompSetupSecrecy.setupPublic_2 hwf.1]; exact hpk 5 (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  all_goals cases heq
private theorem ai_kemRejKey_eq (sk ct : DY.Bytes) :
    assumedInjective (DY.PQKem.kemRejKey sk ct) = false := by
  let x : DY.PQKem.RejKey.SubF DY.Bytes := { sk := sk, cipher := ct }
  rw [show DY.PQKem.kemRejKey sk ct = DY.BytesView.pack x from rfl]
  unfold assumedInjective
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ x]
  rfl

theorem ptAvoidFull_kemRejKey {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {b : HwBytes} {sk ct : DY.Bytes}
    (hsk : PtAvoidFull i r S g ms b sk) (hct : PtAvoidFull i r S g ms b ct) :
    PtAvoidFull i r S g ms b (DY.PQKem.kemRejKey sk ct) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.PQKem.kemRejKey sk ct = ({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemRej S) (gAll i S g)] at hx
  simp only [gKemRej, concretizeKemRej, node, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk | hxct
  · rw [show (({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack) = DY.PQKem.kemRejKey sk ct from rfl,
      ai_kemRejKey_eq] at hinj
    cases hinj
  · exact hsk x hxsk hnpt hinj hnk
  · exact hct x hxct hnpt hinj hnk

theorem ptAvoidFull_bobAgreement_keys {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes}
    {ikB spk pqsk : DY.Bytes} {opk : Option DY.Bytes} {ikA ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hb32 : b.length < 32)
    (hikB : PtAvoidFull compI0 r S g ms b ikB)
    (hspk : PtAvoidFull compI0 r S g ms b spk)
    (hpqsk : PtAvoidFull compI0 r S g ms b pqsk)
    (hopk : ∀ o, opk = some o → PtAvoidFull compI0 r S g ms b o)
    (hikA : PtAvoidFull compI0 r S g ms b ikA)
    (hek : PtAvoidFull compI0 r S g ms b ek)
    (hct : PtAvoidFull compI0 r S g ms b ct)
    (hagree : DY.Libsignal.PQXDH.bobAgreement ikB spk pqsk opk ikA ek ct = some keys) :
    PtAvoidFull compI0 r S g ms b keys.rk ∧
    PtAvoidFull compI0 r S g ms b keys.ck ∧
    PtAvoidFull compI0 r S g ms b keys.pqr := by
  unfold DY.Libsignal.PQXDH.bobAgreement at hagree
  simp only [Pure.pure, Option.some.injEq] at hagree
  have hss : PtAvoidFull compI0 r S g ms b ((DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct)).getD (DY.PQKem.kemRejKey pqsk ct)) := by
    cases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct) with
    | none => exact ptAvoidFull_kemRejKey hpqsk hct
    | some ss =>
      obtain ⟨e, hct_eq, rfl⟩ := CompTermAlgebra.kemDecap_eq_some_iff.mp hdec
      rw [hct_eq] at hct
      have hce := ptAvoidFull_kemEncap_fst_elim (i := compI0) (r := r) (S := S) (g := g) (ms := ms) (b := b)
        (c := { pk := DY.PQKem.kemPk pqsk, entropy := e }) hct
      exact ptAvoidFull_kemEncap_snd_compI0 hb32 hce.1 hce.2
  have hag : ∀ {pk sk : DY.Bytes}, PtAvoidFull compI0 r S g ms b pk → PtAvoidFull compI0 r S g ms b sk →
      PtAvoidFull compI0 r S g ms b (DY.Libsignal.PQXDH.agree pk sk) :=
    fun hpk hsk => ptAvoidFull_dh_compI0 hb32 (ptAvoidFull_x25519Key hpk) hsk
  have hdh4 : ∀ d, opk.map (fun x => DY.Libsignal.PQXDH.agree ek x) = some d → PtAvoidFull compI0 r S g ms b d := by
    intro d hd; cases hopk_eq : opk with
    | none => rw [hopk_eq] at hd; cases hd
    | some o => rw [hopk_eq, Option.map_some, Option.some.injEq] at hd; subst hd; exact hag hek (hopk o hopk_eq)
  rw [← hagree]
  exact ptAvoidFull_pqxdhKdf hb32 (ptAvoidFull_pqxdhIkm (hag hikA hspk) (hag hek hikB) (hag hek hspk) hdh4 hss)

theorem stepOK_bobStart_of_run {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 8) (hsec : RunPQSecretsGood compI0 r S g ms b (runTraceMoves r ms)) (hpki : RunPKIGood compI0 r S g ms b (runTraceMoves r ms)) : StepOK compI0 r S g ms b 7 := by
  rintro trPre ⟨⟨k, hk'⟩, inp⟩ rfl _ _ hle hg; rcases inp with ⟨bb, a, kh, regIdxA, mh, pqIdx, spqrIdx⟩
  have hpre : trPre ≤ runTraceMoves r ms := Trace.le_trans _ _ _ (XplSteps.xrun_le _ trPre) hle
  have hb32 : b.length < 32 := Nat.lt_of_lt_of_le hb (by decide)
  show BaseGood compI0 r S g ms b ((DY.Libsignal.Composed.bobStart bb a kh regIdxA mh pqIdx spqrIdx).run trPre).2.val
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at bb a kh regIdxA _ _ trPre hg ?_
  intro ikB spkSk pqsk opkSk ikA vkA ek ct honest keys hik hspk hpqS hopk hreg hek hct hcan hagree; have hikB : PtAvoidFull compI0 r S g ms b ikB := hsec bb _ _ (pqxdhStoredAt_mono hpre hik); have hspkG : PtAvoidFull compI0 r S g ms b spkSk := hsec bb _ _ (pqxdhStoredAt_mono hpre hspk)
  have hopkG : ∀ o, opkSk = some o → PtAvoidFull compI0 r S g ms b o := by
    intro o ho; rcases hopk with ⟨_, hn⟩ | ⟨idx, o', _, ho', hst⟩ <;> [rw [hn] at ho; rw [ho'] at ho] <;> cases ho
    exact hsec bb _ _ (pqxdhStoredAt_mono hpre hst)
  have hikA : PtAvoidFull compI0 r S g ms b ikA := hpki a ikA vkA honest regIdxA (CompTrace.eventLoggedAt_mono hpre hreg); have hekG : PtAvoidFull compI0 r S g ms b ek := ptAvoidFull_of_attackerKnows_le hpre hg (NetMsgAt.attackerKnows hek); have hctG : PtAvoidFull compI0 r S g ms b ct := ptAvoidFull_of_attackerKnows_le hpre hg (NetMsgAt.attackerKnows hct)
  have hpqskG : PtAvoidFull compI0 r S g ms b pqsk := hsec bb _ _ (pqxdhStoredAt_mono hpre hpqS)
  have hpqr : PtAvoidFull compI0 r S g ms b keys.pqr :=
    (ptAvoidFull_bobAgreement_keys hb32 hikB hspkG hpqskG hopkG hikA hekG hctG hagree).2.2
  have hinit : PtAvoidFull compI0 r S g ms b (DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) := ptAvoidFull_spqrInit hpqr (ptAvoidFull_literalToBytes _); dsimp only
  refine bind_receiveSignalMsg_ak mh.msg trPre hg fun msg hmsg => ?_
  have hpq : PtAvoidFull compI0 r S g ms b msg.pqRatchet := ptAvoidFull_of_attackerKnows_le hpre hg hmsg
  refine preserves_ensureReceiverChain_bind _ msg.ratchetKey (fun tr h => baseGood_append_rnd tr 32 h) (fun x hx => ?_) trPre hg
  rcases x with ⟨st', c, ratcheted⟩; dsimp only at hx ⊢
  rcases hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact CompTrace.Preserves.failure
  rcases hrecv : DY.Spqr.spqrRecv st'.spqr msg.pqRatchet spqrIdx with _ | ⟨spqr', kk⟩
  · exact CompTrace.Preserves.failure
  have hkey : PtAvoidFull compI0 r S g ms b kk := ptAvoidFull_spqrRecvKey_of hrecv (by rw [hx]; exact hinit) hpq
  dsimp only
  refine CompTrace.Preserves.bind (preserves_send_baseGood hkey) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ =>
      CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
  split <;> [refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ =>
    CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ => ?_; skip] <;>
  (refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
    CompTrace.Preserves.bind (preserves_logPQ_baseGood _) fun _ => ?_;
   split
   · exact CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
       CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ =>
         CompTrace.Preserves.bind (preserves_logC_baseGood _) fun _ =>
           CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
             CompTrace.Preserves.bind (preserves_logSkippedKeys_baseGood _ _ _ _ _ _ _) fun _ =>
               CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _
   · exact CompTrace.Preserves.bind (preserves_logC_baseGood _) fun _ =>
       CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ =>
         CompTrace.Preserves.bind (preserves_logSkippedKeys_baseGood _ _ _ _ _ _ _) fun _ =>
           CompTrace.Preserves.bind (preserves_logTR_baseGood _) fun _ => preserves_logMessageKeyAndStore_baseGood _ _ _ _ _ _ _ _ _)
theorem hbase_of_runFacts {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hmr : ModelRun r ms) (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b = ptAt 38 ∨ b = ptAt 78) (hst : ∀ ls ∈ storedStates r (runTraceMoves r ms), PtAvoidFull compI0 r S g ms b (Comparse.serialize ls)) (hsks : NoSKS (runTraceMoves r ms)) (hnb : ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH ∧ ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM) (hrs : RunRandSafe g b (runTraceMoves r ms)) : ∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u := by
  obtain ⟨_, hb8, hb32⟩ := ptAt38_or_ptAt78_len hb
  have htr : RunTRStatesGood compI0 r S g ms b (runTraceMoves r ms) :=
    runTRStatesGood_of_storedStates hst (fun _ _ _ hat => mem_storedStates_of_storedAt (setupTrace_le_runTrace' r ms) hat)
  have hsec : RunPQSecretsGood compI0 r S g ms b (runTraceMoves r ms) := runPQSecretsGood_of_no_setup hcompat hwf hb32 hmr; have hpki : RunPKIGood compI0 r S g ms b (runTraceMoves r ms) := runPKIGood_of_no_setup hcompat hwf hb32 hmr.2.1; have hsk : RunSkippedGood compI0 r S g ms b (runTraceMoves r ms) := runSkippedGood_of_noSKS hsks
  refine hbase_of_openSteps hmr (fun k hk0 hk2 hk9 hk19 hk20 => ?_)
  match k with
  | 0 => exact absurd rfl hk0 | 1 => exact stepOK_registerIdentity_of_run hb32 hrs | 2 => exact absurd rfl hk2
  | 3 => exact stepOK_genSignedPrekey_of_run hb32 hsec hrs | 4 => exact stepOK_genPQPrekey_of_run hsec hrs
  | 5 => exact stepOK_genOneTimePrekey_of_run hb32 hrs | 6 => exact stepOK_aliceStart_of_run hb32 hrs
  | 7 => exact stepOK_bobStart_of_run hb8 hsec hpki | 8 => exact stepOK_messageEncrypt_of_run hb8 htr hrs
  | 9 => exact absurd rfl hk9 | 10 => exact stepOK_messageDecrypt_of_run htr | 11 => exact stepOK_messageDecryptSkipped_of_run htr
  | 12 => exact stepOK_exposeKey_of_run htr | 13 => exact stepOK_exposeSpqr_of_run htr | 14 => exact stepOK_exposeSkipped_of_run hsk
  | 15 => exact stepOK_compromiseIK_of_run hsec | 16 => exact stepOK_compromiseSPK_of_run hsec
  | 17 => exact stepOK_compromisePQSPK_of_run hsec | 18 => exact stepOK_compromiseOPK_of_run hsec
  | 19 => exact absurd rfl hk19 | 20 => exact absurd rfl hk20 | 21 => exact stepOK_invertDH_of_run hnb.1 | 22 => exact stepOK_invertKEM_of_run hnb.2
  | k + 23 => intro trPre input hk; have hlt := input.1.2; rw [hk] at hlt; omega
theorem hbase_of_runFacts_no_leak {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hmr : ModelRun r ms) (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b = ptAt 38 ∨ b = ptAt 78) (hst : ∀ ls ∈ storedStates r (runTraceMoves r ms), PtAvoidFull compI0 r S g ms b (Comparse.serialize ls)) (hsks : NoSKS (runTraceMoves r ms)) (_hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hnb : Common443.CompSetupSecrecy.NoBrk r ms) (hrs : RunRandSafe g b (runTraceMoves r ms)) : ∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u :=
  hbase_of_runFacts hmr hcompat hwf hb hst hsks hnb hrs
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps
