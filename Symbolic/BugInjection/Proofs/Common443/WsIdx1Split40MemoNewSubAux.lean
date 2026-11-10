/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem eq_take_append_cons_drop :
    ∀ (ms : List Move) (k : Nat) {m : Move}, ms[k]? = some m → ms = ms.take k ++ m :: ms.drop (k + 1)
  | [], _, _, h => by simp at h
  | x :: xs, 0, _, h => by simp at h; subst h; rfl
  | x :: xs, k + 1, _, h => congrArg (x :: ·) (eq_take_append_cons_drop xs k h)
theorem runTrace_eq_of_getElem? {r : Records} {ms : List Move} {k : Nat} {m : Move} {tr_k : ExecTrace} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some m) : runTraceMoves r ms = (runMoves (ms.drop (k + 1)) (m.next tr_k)).1 := by
  conv => lhs; rw [eq_take_append_cons_drop ms k hget]
  rw [xpl_runTrace_eq, runMoves_append_fst, ← xpl_runTrace_eq, htr_k, runMoves_cons_fst]
theorem setupTrace_le_of_runTrace_take {r : Records} {ms : List Move} {k : Nat} {tr_k : ExecTrace} (htr_k : runTraceMoves r (ms.take k) = tr_k) : setupTrace r ≤ tr_k := by rw [← htr_k, xpl_runTrace_eq]; exact CompPrefixInvEnc.runMoves_le (ms.take k) (setupTrace r)
theorem next_le_runTrace_of_getElem? {r : Records} {ms : List Move} {k : Nat} {m : Move} {tr_k : ExecTrace} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some m) : m.next tr_k ≤ runTraceMoves r ms := by
  rw [runTrace_eq_of_getElem? htr_k hget]
  exact CompPrefixInvEnc.runMoves_le (ms.drop (k + 1)) (m.next tr_k)
theorem mem_runVis_of_getElem? {r : Records} {ms : List Move} {k : Nat} {m : Move} {tr_k : ExecTrace} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some m) {v : VisEntry} (hv : v ∈ m.vis tr_k) : v ∈ runVis r ms := by change v ∈ r.setupMove.vis Trace.nil ++ (runMoves ms (setupTrace r)).2; rw [eq_take_append_cons_drop ms k hget, runMoves_append_snd, ← xpl_runTrace_eq, htr_k]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hv))
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts ( encrypt_vis_eq trStateStoredAt_encNextTr mem_storedStates_iff)
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc ( mem_prefixTerms_of_send_vis mem_prefixTerms_of_storedStates length_le_of_trace_le lt_length_of_at?_some)
theorem encOut_mem_prefixTerms_of_getElem? {r : Records} {ms : List Move} {k : Nat} {tr_k : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} {stA : DY.Libsignal.TripleRatchet.TRState} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some (Move.encrypt me sIdx cl pq wrap)) (henc : (Move.encrypt me sIdx cl pq wrap).next tr_k = CompPrefixInvEnc.encNextTr tr_k me sIdx stA cl pq) : encOut tr_k stA cl pq ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms) := by
  rcases wrap with _ | ⟨e, c⟩
  · refine mem_prefixTerms_of_send_vis (v := ⟨.send, [encOut tr_k stA cl pq], .whisper, none⟩)
      (mem_runVis_of_getElem? htr_k hget ?_) rfl (List.mem_singleton_self _)
    rw [encrypt_vis_eq, henc]
    exact List.mem_append_right _ (by unfold encSend; rw [CompPrefixInvEnc.lastSent_encNextTr]; exact List.mem_singleton_self _)
  · refine mem_prefixTerms_of_send_vis
      (v := ⟨.send, received tr_k [e, c] ++ [encOut tr_k stA cl pq], .preKeySend, none⟩)
      (mem_runVis_of_getElem? htr_k hget ?_) rfl (List.mem_append_right _ (List.mem_singleton_self _))
    rw [encrypt_vis_eq, henc]
    exact List.mem_append_right _ (by unfold encSend; rw [CompPrefixInvEnc.lastSent_encNextTr]; exact List.mem_singleton_self _)
theorem serialize_encSt_mem_prefixTerms_of_getElem? {r : Records} {ms : List Move} {k : Nat} {tr_k : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} {stA : DY.Libsignal.TripleRatchet.TRState} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some (Move.encrypt me sIdx cl pq wrap)) (henc : (Move.encrypt me sIdx cl pq wrap).next tr_k = CompPrefixInvEnc.encNextTr tr_k me sIdx stA cl pq) : (Comparse.serialize (⟨me, encSt tr_k stA cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms) := by
  have hat : ((runTraceMoves r ms).at? (tr_k.length + 5) : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE me (encSt tr_k stA cl)) :=
    XplSteps.xat?_le_some (henc ▸ next_le_runTrace_of_getElem? htr_k hget) (trStateStoredAt_encNextTr tr_k me sIdx stA cl pq)
  have hlen_setup := length_le_of_trace_le (setupTrace_le_of_runTrace_take htr_k)
  exact mem_prefixTerms_of_storedStates
    (mem_storedStates_iff.mpr ⟨tr_k.length + 5, by omega, lt_length_of_at?_some hat, hat⟩)
theorem prefixTerms_mem_of_ws40Idx1RunInv
    {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat}
    (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    (Comparse.serialize (⟨r.alice, encSt tr₂ stA₁ cl₁⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    (Comparse.serialize (⟨r.alice, encSt tr₃ stA₁' cl₂⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈
      prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, htr₂, hget₂, htr₃, hget₃, _, rfl, rfl, henc₂, henc₃⟩ := hinv.links
  exact ⟨encOut_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂, encOut_mem_prefixTerms_of_getElem? htr₃ hget₃ henc₃, serialize_encSt_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂, serialize_encSt_mem_prefixTerms_of_getElem? htr₃ hget₃ henc₃⟩
theorem census_iniAliceStartTr_eq (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : iniAliceStartTr tr a b o = CompPrefixInvAlice.iniAliceStartTr tr a b o := rfl
theorem census_encNextTr_eq (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : encNextTr tr₂ me sIdx stA cl pq = CompPrefixInvEnc.encNextTr tr₂ me sIdx stA cl pq := rfl
theorem received_own_wrap_eq {tr₁ tr_k : ExecTrace} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hle : iniAliceStartTr tr₁ a b o ≤ tr_k) : received tr_k [tr₁.length + 3, tr₁.length + 4] = [o.ek, o.ct] := by
  rw [census_iniAliceStartTr_eq] at hle
  simp only [received, List.filterMap_cons, List.filterMap_nil, CompPrefixInvAlice.getMessageSentAt_of_netMsgAt (XplSteps.xat?_le_some hle (CompPrefixInvAlice.netMsgAt_ek_iniAliceStartTr tr₁ a b o)), CompPrefixInvAlice.getMessageSentAt_of_netMsgAt (XplSteps.xat?_le_some hle (CompPrefixInvAlice.netMsgAt_ct_iniAliceStartTr tr₁ a b o))]
theorem next_le_runTrace_take_of_lt {r : Records} {ms : List Move} {k₁ k₂ : Nat} {m : Move} {tr₁ tr₂ : ExecTrace} (hk : k₁ < k₂) (htr₁ : runTraceMoves r (ms.take k₁) = tr₁) (hget₁ : ms[k₁]? = some m) (htr₂ : runTraceMoves r (ms.take k₂) = tr₂) : m.next tr₁ ≤ tr₂ := by
  rw [← htr₂]
  refine next_le_runTrace_of_getElem? ?_ (by rw [List.getElem?_take_of_lt hk]; exact hget₁)
  rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk)]
theorem wrap_terms_mem_prefixTerms_of_getElem? {r : Records} {ms : List Move} {k : Nat} {tr_k : ExecTrace} {me : Participant} {sIdx cl pq e c : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} (htr_k : runTraceMoves r (ms.take k) = tr_k) (hget : ms[k]? = some (Move.encrypt me sIdx cl pq (some (e, c)))) (henc : (Move.encrypt me sIdx cl pq (some (e, c))).next tr_k = encNextTr tr_k me sIdx stA cl pq) {u : DY.Bytes} (hu : u ∈ received tr_k [e, c]) : u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms) := by
  refine mem_prefixTerms_of_send_vis
    (v := ⟨.send, received tr_k [e, c] ++ [encOut tr_k stA cl pq], .preKeySend, none⟩)
    (mem_runVis_of_getElem? htr_k hget ?_) rfl (List.mem_append_left _ hu)
  rw [encrypt_vis_eq, henc, census_encNextTr_eq]
  exact List.mem_append_right _ (by unfold encSend; rw [CompPrefixInvEnc.lastSent_encNextTr]; exact List.mem_singleton_self _)
theorem ek_ct_mem_prefixTerms_of_links40Own {r : Records} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hown : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    o₁.ek ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    o₁.ct ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  intro o₁
  obtain ⟨_, _, _, _, _, _, _, hk₁₂, _, htr₁, hget₁, htr₂, hget₂, _, _, hnext₁, henc₂, _⟩ := hown
  have hrecv := received_own_wrap_eq (hnext₁ ▸ next_le_runTrace_take_of_lt hk₁₂ htr₁ hget₁ htr₂)
  exact ⟨wrap_terms_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂ (by rw [hrecv]; exact List.mem_cons_self),
         wrap_terms_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂ (by rw [hrecv]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc ( mem_memo_lit_assumedInjective_false mem_memo_concat_cases mem_memo_hmac_cases mem_memo_concat_left mem_memo_concat_right mem_memo_concatPrefixes_mem mem_memo_concatPrefixes_tail mem_memo_hmac_left mem_memo_hmac_right mem_memo_trunc8 self_mem_slowBytes_serialize cks_mem_trStatePrefixes chainKey_mem_serialize_recvChain mem_memo_chainKey_of_serialize_recvList)
theorem mem_memo_encWire_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encWire tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_encWire_of_encOut hx
theorem mem_memo_encMac_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMac tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_encMac_of_encOut hx
theorem mem_memo_encCiphertext_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encCiphertext tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_encCiphertext_of_encOut hx
theorem mem_memo_encPqMsg_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encPqMsg tr₂ stA cl)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_encPqMsg_of_encOut hx
theorem mem_memo_akeys_cipherKey_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).cipherKey).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_akeys_cipherKey_of_encOut hx
theorem mem_memo_akeys_iv_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).iv).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_akeys_iv_of_encOut hx
theorem mem_memo_akeys_macKey_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).macKey).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_akeys_macKey_of_encOut hx
theorem mem_memo_pt_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (randTerm tr₂.length 32)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_pt_of_encOut hx
theorem mem_memo_macInput_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq)))).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_macInput_of_encOut hx
theorem mem_memo_seed_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_seed_of_encOut hx
theorem mem_memo_cks_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g stA.cks).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_cks_of_encOut hx
theorem mem_memo_rk_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.rk).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_rk_of_encOut hx
theorem mem_memo_pqr_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.pqr).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl pq)).memo := CompRX0NBSC38Hmc.mem_memo_pqr_of_encOut hx
theorem mem_memo_encSalt_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encSalt tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_akeys_cipherKey_of_encOut (mem_memo_hmac_left (mem_memo_hmac_left hx))
theorem mem_memo_ck_of_serialize_encSt {i : ExternInterpretation} {S : Sem} {g : Ghost} (me b : Participant) (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.ck).memo) : x ∈ (gamma' i S g (Comparse.serialize (⟨me, encSt tr₂ (iniAliceStartState tr₁ b o) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes)).memo := CompRX0NBSC38Hmc.mem_memo_ck_of_serialize_encSt me b tr₁ tr₂ o cl hx
theorem mem_memo_cks_of_serialize_localState {i : ExternInterpretation} {S : Sem} {g : Ghost} (ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g ls.state.cks).memo) : x ∈ (gamma' i S g (Comparse.serialize ls : DY.Bytes)).memo := CompRX0NBSC38Hmc.mem_memo_cks_of_serialize_local_tr ls hx
theorem mem_symDec_encCiphertext_eq {ck iv : DY.Bytes} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {m : DY.Bytes} (hm : m ∈ (DY.SymEnc.symDec ck iv (encCiphertext tr₂ stA cl pq)).toList) : m = randTerm tr₂.length 32 := by
  unfold encCiphertext at hm; simp only [DY.SymEnc.symDec, DY.SymEnc.CanSymEnc.symDec, DY.SymEnc.symEnc, DY.BytesView.view_pack] at hm
  split_ifs at hm <;> [exact List.mem_singleton.mp hm; simp at hm]
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
