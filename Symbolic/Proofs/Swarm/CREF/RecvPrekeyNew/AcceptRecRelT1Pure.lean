/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecRelT1PureA
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptProv
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Record-Relation Glue Instantiation for Pre-Key Session Start

Instantiates `RpkT1Glue` from an `XplBlock` explanation and a `preKeyRepresentations` witness for
an accepting `session_recv_prekey` call.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF.TR (EvE NetE RndE)

private theorem rpkT1_newRandoms_snoc_other {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    (hle : tr₀ ≤ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none := by rfl) :
    newRandoms tr₀ (tr.append e) = newRandoms tr₀ tr := by
  rw [rpkT1_newRandoms_trans hle (DY.Trace.append_le tr e), rpkT1_newRandoms_append_other tr e hnone,
    List.append_nil]

private theorem rpkT1_newRandoms_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      newRandoms tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val = []
  | 0, _, _, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    simp only [DY.Traceful.run_pure]
    unfold newRandoms; rw [newIndices_self]; rfl
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [DY.Traceful.run_bind, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      DY.Traceful.run_bind, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    dsimp only
    rw [Symbolic.DYBridge.DY.Traceful.run_eq_1 (pure ())]
    let tr₁ := tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    change newRandoms tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
      (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.val = []
    rw [rpkT1_newRandoms_trans (DY.Trace.append_le tr _)
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
        (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.property,
      rpkT1_newRandoms_append_other tr _, rpkT1_newRandoms_logSkippedKeys s pk rIdx srcIdx k _ _ tr₁]; rfl

private theorem rpkT1_append_le_of_le {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    (e : E) (hle : tr₀ ≤ tr) : tr₀ ≤ tr.append e :=
  DY.Trace.le_trans tr₀ tr (tr.append e) hle (DY.Trace.append_le tr e)

private theorem rpkT1_bobStartPreSkipTr_le (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) : tr ≤ bobStartPreSkipTr tr b a o msg key := by
  unfold bobStartPreSkipTr; dsimp only
  apply rpkT1_append_le_of_le; apply rpkT1_append_le_of_le
  apply rpkT1_append_le_of_le; apply rpkT1_append_le_of_le
  cases o.opk
  · exact rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (DY.Trace.le_refl tr))
  · exact rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (DY.Trace.le_refl tr)))

private abbrev rpkT1_bobSkipTr (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) : ExecTrace :=
  let tr_pre := bobStartPreSkipTr tr b a o msg key
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
  let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr_pre.length + skipped + 2
  ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx
    c.chainKey c.index skipped).run tr_pre).2.val

private theorem rpkT1_bobStartPreSkipTr_le_bobSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    bobStartPreSkipTr tr b a o msg key ≤ rpkT1_bobSkipTr tr b a o msg key :=
  ((DY.Libsignal.TripleRatchet.logSkippedKeys _ _ _ _ _ _ _).run _).2.property

private theorem rpkT1_newRandoms_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    newRandoms tr (bobStartPreSkipTr tr b a o msg key) = [(randTerm tr.length 32, 32)] := by
  unfold bobStartPreSkipTr
  have h1 : tr ≤ (tr.append (RndE 32)).append (NetE key) :=
    rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (DY.Trace.le_refl tr))
  cases o.opk with
  | none =>
    dsimp only
    rw [rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ h1))),
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ h1)),
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ h1),
      rpkT1_newRandoms_snoc_other h1,
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (DY.Trace.le_refl tr)),
      rpkT1_newRandoms_append_rnd_self]
  | some opkPk =>
    dsimp only
    have h2 : tr ≤ ((tr.append (RndE 32)).append (NetE key)).append (EvE (.OPKUsed b opkPk)) :=
      rpkT1_append_le_of_le _ h1
    rw [rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ h2))),
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ h2)),
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ h2),
      rpkT1_newRandoms_snoc_other h2,
      rpkT1_newRandoms_snoc_other h1,
      rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (DY.Trace.le_refl tr)),
      rpkT1_newRandoms_append_rnd_self]

theorem rpkT1_newRandoms_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    newRandoms tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) =
      [(randTerm tr.length 32, 32)] := by
  unfold bobStartTr; dsimp only
  have hpre := rpkT1_bobStartPreSkipTr_le tr b a o msg key
  have hskip := rpkT1_bobStartPreSkipTr_le_bobSkipTr tr b a o msg key
  have hle1 := DY.Trace.le_trans _ _ _ hpre hskip
  rw [rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ (rpkT1_append_le_of_le _ hle1)),
    rpkT1_newRandoms_snoc_other (rpkT1_append_le_of_le _ hle1), rpkT1_newRandoms_snoc_other hle1,
    rpkT1_newRandoms_trans hpre hskip, rpkT1_newRandoms_logSkippedKeys,
    rpkT1_newRandoms_bobStartPreSkipTr, List.append_nil]

theorem rpkT1_rng_eq {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {p a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    g.σ (runTraceMoves r (ms₀ ++ pre)).length 32 = d ∧
      gamma interpretation S g (randTerm (runTraceMoves r (ms₀ ++ pre)).length 32) = d := by
  obtain ⟨hF, ⟨w⟩⟩ := rpkT_bobStart_block hB hpre
  rw [xpl_vis_eq] at hF
  have hexp : exposures (runTraceMoves r (ms₀ ++ pre))
      ((Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown).next (runTraceMoves r (ms₀ ++ pre))) = [] :=
    exposures_nil_of_not_leakKind rfl (by rintro ⟨⟩)
  rw [hexp, List.append_nil] at hF
  simp only [xpl_ownVis, bobVis, w.next_eq, rpkT1_newRandoms_bobStartTr, List.map_cons, List.map_nil,
    rngEntry] at hF
  rcases shown with _ | _ | k
  · simp at hF
  · simp at hF
  · simp only [List.take_succ_cons, List.cons_append] at hF
    obtain ⟨_, hF2⟩ := List.forall₂_cons.1 hF
    obtain ⟨⟨_, hrng⟩, _⟩ := List.forall₂_cons.1 hF2
    dsimp only [eventBytes, List.map] at hrng
    injection hrng with hd
    refine ⟨?_, hd⟩
    unfold randTerm at hd
    rwa [TR.gamma_rand] at hd

theorem rpkT1_rkLen {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) :
    (gamma interpretation S g w.keys.rk).length = 32 := by
  have hag := w.hagree
  unfold PQXDH.bobAgreement at hag
  simp only [Pure.pure, Option.some.injEq] at hag
  rw [← hag, (TR.gamma_pqxdhKdf interpretation S g _).1]
  exact TR.length_hmacWith _ _ _

theorem rpkT1_dhsLen {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move}
    {acc : List MachineEvent} {b d pt : HwBytes} {a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob a kh regA mh pqIdx spqrMsgIdx) :
    (gamma interpretation S g w.spk).length = 32 := by
  have hms : ∀ m ∈ ms₀ ++ pre, m.isSetup = false := fun m hm => by
    apply hB.run.2.1 m
    rw [← List.append_assoc]
    exact List.mem_append_left _ hm
  have hspk : w.spk = setupSecret r 2 := rpkP_bob_spk hwf.1 (ms₀ ++ pre) hms w.hspk
  obtain ⟨_, _, hs2, _, _⟩ := TR.gamma_setupSecret interpretation r S g hB.pre.1 hwf.1
  rw [hspk, hs2, (TR.secretBytes_eq r hwf.1).2.2.1]
  exact hwf.2.1 (10, 32) (by rw [TR.setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> simp)

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

private theorem rpkT1_gamma_spqrRecvState (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (st msg : DY.Bytes) :
    gamma interpretation S g (({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack) =
      S.recvState (gamma interpretation S g st) (gamma interpretation S g msg) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll interpretation S g)]
  rfl

/-- Relates the post-receive symbolic SPQR state `w.spqr'` under `gamma` to `newPqr`. -/
theorem rpkT1_spqr_of_faithfulInner {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hRecvState : S.recvState = Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvStateOf interpretation)
    {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)
    {p : PreKeyFields}
    (hF : FaithfulInner interpretation S g w.raw p)
    (st0 : CryptoGames.LibsignalSession.SessionState HwBytes) (newPqr : HwBytes)
    (key : CryptoGames.HKDF.Salt)
    (hpq0 : st0.pqRatchetState =
      gamma interpretation S g (DY.Spqr.spqrInit w.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A))
    (hrecv :
      (pureSpqrEmptyAsNone
          (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation)).recv
        st0.pqRatchetState p.inner.pqRatchet = Except.ok (newPqr, key)) :
    gamma interpretation S g w.spqr' = newPqr := by
  obtain ⟨msg', hp', _, _, _, _, _, hpqr, _, _⟩ := hF
  rw [w.hparse] at hp'
  cases hp'
  have hst := DY.Spqr.spqrRecv_state _ _ _ _ w.hspqr
  dsimp only [bobRatchetedSt] at hst
  rw [hst, rpkT1_gamma_spqrRecvState, ← hpq0, hpqr, hRecvState]
  unfold pureSpqrEmptyAsNone at hrecv
  unfold Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvStateOf
    Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvStateB
    Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvB
  dsimp only at hrecv ⊢
  rcases h : (Symbolic.Swarm.SHARED.HookAuth.spqrV1RecvWithMac
      (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
      (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
      (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation)).recv
      st0.pqRatchetState p.inner.pqRatchet with _ | ⟨st', key?⟩
  · rw [h] at hrecv; cases hrecv
  · rw [h] at hrecv
    injection hrecv with hpair
    exact (Prod.mk.inj hpair).1

/-- From an explanation of the accepting block, `BobStartOk`'s received handles `[w.ek, w.ct, w.raw]`
satisfy `PreKeyRecvMatches` and `OpkNamed r b w.opk.isSome`. -/
theorem rpkT1_recvMatches {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {p a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) p a kh regA mh pqIdx spqrMsgIdx) :
    PreKeyRecvMatches interpretation r S g b [w.ek, w.ct, w.raw] ∧
      OpkNamed r b w.opk.isSome := by
  obtain ⟨hF, -⟩ := rpkT_bobStart_block hB hpre
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 :=
    ⟨shown - 1, by have := rpkT_bobStart_shown_pos hB; omega⟩
  rw [xpl_vis_eq] at hF
  simp only [xpl_ownVis, bobVis, List.take_succ_cons, List.cons_append] at hF
  obtain ⟨⟨_, hrecv⟩, -⟩ := List.forall₂_cons.1 hF
  have hrec : received (runTraceMoves r (ms₀ ++ pre)) [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
    simp only [received, List.filterMap_cons, List.filterMap_nil,
      rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
      rpkT_getMessageSentAt_of_at? w.hmsg]
  change PreKeyRecvOpkMatches interpretation r S g b
    (received (runTraceMoves r (ms₀ ++ pre)) [mh.ek, mh.ct, mh.msg] ++
      (bobOpkPk p kh (runTraceMoves r (ms₀ ++ pre))).toList) at hrecv
  rw [hrec, bobOpkPk_eq _ _ _ _ w.hopk] at hrecv
  rcases hopk : w.opk with _ | o <;> rw [hopk] at hrecv <;> exact hrecv

theorem rpkT1_bobKeys {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ pre post : List Move}
    {acc : List MachineEvent} {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {p : PreKeyFields} {used : Bool}
    (hparse : parsePreKeyWire b = some p)
    (hopk_ok : p.preKeyId = none ∨
      (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId))
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob r.alice kh regA mh pqIdx spqrMsgIdx) :
    TR.bobKeys r p ⟨w.ek, w.ct, w.raw⟩ = some w.keys := by
  have hms : ∀ m ∈ ms₀ ++ pre, m.isSetup = false := fun m hm => by
    apply hB.run.2.1 m
    rw [← List.append_assoc]
    exact List.mem_append_left _ hm
  have hikB : w.ikB = setupSecret r 1 := rpkP_bob_identity hwf.1 (ms₀ ++ pre) hms w.hik
  have hspk : w.spk = setupSecret r 2 := rpkP_bob_spk hwf.1 (ms₀ ++ pre) hms w.hspk
  have hpq : w.pqsk = setupSecret r 4 := rpkP_bob_pq hwf.1 (ms₀ ++ pre) hms w.hpq
  have hikA : w.ikAPk = setupPublic r 0 := rpkP_reg_alice hwf.1 (ms₀ ++ pre) hms w.hreg
  have hopk_prov := rpkP_bob_opk hwf.1 (ms₀ ++ pre) hms kh.opk w.opk w.hopk
  obtain ⟨p', hp1, hopk_if⟩ := (rpkT1_recvMatches hB hpre w).2
  rw [hparse] at hp1; cases hp1
  have hag := w.hagree
  unfold PQXDH.bobAgreement at hag
  rw [hikB, hspk, hpq, hikA] at hag
  simp only [Pure.pure, Option.some.injEq] at hag
  unfold TR.bobKeys
  dsimp only
  rcases hopk_ok with hnone | ⟨hw, -, hsome⟩
  · have his : w.opk.isSome = false := by
      cases h : w.opk.isSome
      · rfl
      · simp only [h, ↓reduceIte] at hopk_if
        rw [hnone] at hopk_if
        exact nomatch hopk_if.1
    have hwopk : w.opk = none := Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp his)
    rw [hwopk] at hag
    rw [hnone]
    exact congrArg some hag
  · have his : w.opk.isSome = true := by
      cases h : w.opk.isSome
      · simp only [h, Bool.false_eq_true, ↓reduceIte] at hopk_if
        rw [hsome] at hopk_if
        cases hopk_if
      · rfl
    have hwopk : w.opk = some (setupSecret r 6) := by
      rcases hopk_prov with h0 | ⟨_, h6⟩
      · rw [h0] at his; cases his
      · exact h6
    have hcond : (r.withOpk && r.opkId == r.opkId) = true := by simp [hw]
    rw [hwopk] at hag
    rw [hsome]
    simp only [Bind.bind, Option.bind, Pure.pure, hcond, ↓reduceIte, Option.some.injEq]
    exact hag

/-- Establishes the initial `TR.StateRel` between `bobInitSt` and the normalized pre-decrypt
session record from `preKeyRepresentations` membership. -/
theorem rpkT1_rel0_of_rep {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {p : PreKeyFields} {used : Bool}
    (hparse : parsePreKeyWire b = some p)
    (hopk_ok : p.preKeyId = none ∨
      (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId))
    (hkm : ¬ KyberMismatch interpretation r p)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob r.alice kh regA mh pqIdx spqrMsgIdx)
    (hrep : ⟨w.ek, w.ct, w.raw⟩ ∈ preKeyRepresentations interpretation r S g (ms₀ ++ pre) b)
    (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (hinv : AcceptSt0ModelInvs interpretation r p s.state) :
    TR.StateRel interpretation S g
      (bobInitSt r.alice w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey)
      (sessionToRecordRec (RpkDHa.rpkSessionNorm (rpkSpkPub interpretation r) s)) := by
  have hms : ∀ m ∈ ms₀ ++ pre, m.isSetup = false := fun m hm => by
    apply hB.run.2.1 m
    rw [← List.append_assoc]
    exact List.mem_append_left _ hm
  have hikB : w.ikB = setupSecret r 1 := rpkP_bob_identity hwf.1 (ms₀ ++ pre) hms w.hik
  have hspk : w.spk = setupSecret r 2 := rpkP_bob_spk hwf.1 (ms₀ ++ pre) hms w.hspk
  have hikA : w.ikAPk = setupPublic r 0 := rpkP_reg_alice hwf.1 (ms₀ ++ pre) hms w.hreg
  have hInit : S.init = Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interpretation := hSeq ▸ rfl
  have hkeys := rpkT1_bobKeys hwf hparse hopk_ok hB hpre w
  have hst : bobInitSt r.alice w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey =
      { peer := r.alice, myIk := PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 1)),
        peerIk := PQXDH.serializedIk (setupPublic r 0), rk := w.keys.rk, dhs := setupSecret r 2,
        cks := w.keys.ck, ns := 0, pn := 0,
        sid := DY.Concat.concat (DY.X25519.normalizeX25519Key w.msg.ratchetKey) w.keys.rk,
        initiator := false, rIdx := 0, recv := [],
        spqr := DY.Spqr.spqrInit w.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A } := by
    unfold BobStartOk.out bobOut bobInitSt
    dsimp only
    rw [hikB, hspk, hikA]
  rw [hst]
  exact rpkN_stateRel_norm hEq hwf hInit hB.pre.1 hparse hrep hkm hkeys hinv
    w.msg.ratchetKey

/-- Instantiates `RpkT1Glue` from representation membership and pre-start skipped-key freshness. -/
theorem rpkT1_glue_of_rep {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    {p : PreKeyFields} {used : Bool}
    (hparse : parsePreKeyWire b = some p)
    (hdLen : d.length = 32)
    (hopk_ok : p.preKeyId = none ∨
      (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId))
    (hkm : ¬ KyberMismatch interpretation r p)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob r.alice kh regA mh pqIdx spqrMsgIdx)
    (hrep : ⟨w.ek, w.ct, w.raw⟩ ∈ preKeyRepresentations interpretation r S g (ms₀ ++ pre) b)
    (hfresh : ∀ j < w.msg.counter.toNat,
      DY.Libsignal.TripleRatchet.receiverKeyUsedB (runTraceMoves r (ms₀ ++ pre))
        ((rpkR_finalSt w).sessionInfo r.bob)
        (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt
          (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).chainKey j)).2
        (UInt32.ofNat j) 2 = false) :
    RpkT1Glue interpretation r S g p d (ms₀ ++ pre) r.alice kh regA mh pqIdx spqrMsgIdx w := by
  have hrel0 := rpkT1_rel0_of_rep hEq hwf hSeq hparse hopk_ok hkm hB hpre w hrep
  obtain ⟨_, _, _, _, p', hp1, hF⟩ := hrep
  rw [hparse] at hp1; cases hp1
  obtain ⟨_, htheir, hpkLen, hctr⟩ := rpkT1_msgTie_of_faithfulInner w.hparse hF
  refine
    { reach := by
        have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
        rwa [← List.append_assoc, List.take_left] at h
      rel0 := hrel0
      rkLen := rpkT1_rkLen w
      dhsLen := rpkT1_dhsLen hwf hB w
      their := htheir
      pkLen := hpkLen
      rng := (rpkT1_rng_eq hB hpre).1
      dLen := hdLen
      ctr := hctr
      spqr := fun st0 newPqr key hinv hrecv => ?_
      fresh := hfresh }
  let s0 : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)) :=
    { state := st0, pendingPreKey := none, pendingKyberPreKey := none,
      aliceBaseKey := [], remoteRegistrationId := 0, localRegistrationId := 0 }
  have hpq0 : st0.pqRatchetState =
      gamma interpretation S g (DY.Spqr.spqrInit w.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) :=
    congrArg SessionRec.pqRatchetState (hrel0 s0 hinv).2
  have hRecvState : S.recvState = Symbolic.Swarm.SHARED.SpqrBytes.spqrRecvStateOf interpretation :=
    hSeq ▸ rfl
  exact rpkT1_spqr_of_faithfulInner hRecvState w hF st0 newPqr key hpq0 hrecv

end Symbolic.Swarm.CREF.CliPure
