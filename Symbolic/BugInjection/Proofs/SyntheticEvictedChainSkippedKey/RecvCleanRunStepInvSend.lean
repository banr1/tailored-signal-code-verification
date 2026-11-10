/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean-Run Prefix Step Agreement: `.send` Calls

Computes the visible-entry trace projection `stepView` for `messageEncrypt` (`encTrGen_stepView_ok`)
and proves `party_send_agree` for all 12 `.send` calls (`sIdx < 12`) along the clean-run prefix.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot u32Max)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma ecKey pubBytes secretBytes preKeyWire
   runSteps stepView encDraws encSendEntry pendingPreKey lastSent
   newIndices newRandoms exposures pqExposureAt trExposureAt rngEntry
   randTerm GhostWF OutputsMatch RunMatches runWrapped inputKind)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry at?_append_cases)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg encSig parse_encMsg RndE NetE EvT StT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (o1)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (preCond_messageEncrypt step_ok_encrypt step_next_encrypt step_ok_encryptAbort_false)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse (sendCallOf)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (encTrGen encTrGen_length encTrGen_le append_len
   at?_append_of_lt at?_append_self_proj at?_append_at le_append_of_le at?_mono)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (pqAddrBytes gClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
  (StateBytesAgree stateBytesAgree_encrypt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (PeeledCall stepCoinLen PkiUnchanged pkiUnchanged_runSteps_network
   pkiUnchanged_step_party OnlyAliceDone onlyAliceDone_runSteps_network
   onlyAliceDone_messageEncrypt pendingPreKey_eq_of_onlyAliceDone at?_of_le_lt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
  (NoNewPartyState noNewPartyState_trans noNewPartyState_runSteps_network
   noNewPartyState_step_other ActivePartySt noNewPartyState_preserves_active
   activePartySt_pin_state activePartySt_of_unique_new)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

private theorem encTrGen_newIndices (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    newIndices tr (encTrGen tr me stH cl st pq) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3,
       tr.length + 4, tr.length + 5, tr.length + 6] := by
  unfold newIndices
  rw [encTrGen_length, Nat.add_sub_cancel_left]
  simp [List.range', Nat.add_assoc]

private theorem at?_append_proj_at {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E2) =
      DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) := by
  subst hi; exact at?_append_self_proj tr e

private theorem encTrGen_newRandoms (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    newRandoms tr (encTrGen tr me stH cl st pq) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
  unfold newRandoms
  rw [encTrGen_newIndices]
  let tr' := encTrGen tr me stH cl st pq
  have h0 : (tr'.at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by
    dsimp only [tr', encTrGen]
    iterate 6 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    exact at?_append_at _ _ rfl
  have h1 : (tr'.at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE cl) := by
    dsimp only [tr', encTrGen]
    iterate 5 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    exact at?_append_at _ _ (by simp only [append_len])
  have h2 : (tr'.at? (tr.length + 2) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]
    iterate 4 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h3 : (tr'.at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]
    iterate 3 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h4 : (tr'.at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]
    iterate 2 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h5 : (tr'.at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]
    rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h6 : (tr'.at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  change List.filterMap (fun i => (tr'.at? i : Option DY.Random.ExecEntryT).map _) _ = _
  simp [h0, h1, h2, h3, h4, h5, h6, RndE]

private theorem encTrGen_lastSent (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    lastSent tr (encTrGen tr me stH cl st pq) =
      some (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32)) := by
  unfold lastSent
  rw [encTrGen_length]
  have hlt : tr.length < tr.length + 7 := by omega
  have hsub : tr.length + 7 - 1 = tr.length + 6 := by omega
  simp only [hlt, ↓reduceIte, hsub, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have hat : ((encTrGen tr me stH cl st pq).at? (tr.length + 6) : Option DY.Network.ExecEntryT) =
      some (NetE (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
    dsimp only [encTrGen]
    exact at?_append_at _ _ (by simp only [append_len])
  rw [hat]

private theorem pqExposureAt_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr.append e ≤ tr') (hj : j = tr.length)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    pqExposureAt tr' j = none := by
  subst hj
  unfold pqExposureAt
  have hlt : tr.length < (tr.append e).length := by simp [append_len]
  have hat : (tr'.at? tr.length : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    rw [at?_of_le_lt hle hlt, at?_append_self_proj, hnone]
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

private theorem trExposureAt_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr.append e ≤ tr') (hj : j = tr.length)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none) :
    trExposureAt tr' j = none := by
  subst hj
  unfold trExposureAt
  have hlt : tr.length < (tr.append e).length := by simp [append_len]
  have hat : (tr'.at? tr.length : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
    rw [at?_of_le_lt hle hlt, at?_append_self_proj, hnone]
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

theorem encTrGen_exposures (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    exposures tr (encTrGen tr me stH cl st pq) = [] := by
  unfold exposures
  rw [encTrGen_newIndices]
  let t0 := tr
  let t1 := t0.append (RndE 32)
  let t2 := t1.append (RndE cl)
  let t3 := t2.append (NetE (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)
  let t4' := t3.append (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32)))
  let t5' := t4'.append (EvT (.MessageKey (st.sessionInfo me) .sender
    (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pq st.ns st.rIdx stH))
  let t6 := t5'.append (StT me (encSt st (rnd (tr.length + 1) cl)))
  let t7 := encTrGen tr me stH cl st pq
  have h67 : t6 ≤ t7 := DY.Trace.append_le _ _
  have h57 : t5' ≤ t7 := le_append_of_le (DY.Trace.append_le _ _) _
  have h47' : t4' ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h57
  have h37 : t3 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h47'
  have h27 : t2 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h37
  have h17 : t1 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h27
  have hp0 := pqExposureAt_append_non tr.length h17 rfl rfl
  have hp1 := pqExposureAt_append_non (tr.length + 1) h27 (by simp only [t1, t0, append_len]) rfl
  have hp2 := pqExposureAt_append_non (tr.length + 2) h37 (by simp only [t2, t1, t0, append_len]) rfl
  have hp3 := pqExposureAt_append_non (tr.length + 3) h47' (by simp only [t3, t2, t1, t0, append_len]) rfl
  have hp4 := pqExposureAt_append_non (tr.length + 4) h57 (by simp only [t4', t3, t2, t1, t0, append_len]) rfl
  have hp5 := pqExposureAt_append_non (tr.length + 5) h67 (by simp only [t5', t4', t3, t2, t1, t0, append_len]) rfl
  have hp6 := pqExposureAt_append_non (tr.length + 6) (DY.Trace.le_refl t7)
    (by simp only [append_len]) rfl
  have ht0 := trExposureAt_append_non tr.length h17 rfl rfl
  have ht1 := trExposureAt_append_non (tr.length + 1) h27 (by simp only [t1, t0, append_len]) rfl
  have ht2 := trExposureAt_append_non (tr.length + 2) h37 (by simp only [t2, t1, t0, append_len]) rfl
  have ht5 := trExposureAt_append_non (tr.length + 5) h67 (by simp only [t5', t4', t3, t2, t1, t0, append_len]) rfl
  have ht6 := trExposureAt_append_non (tr.length + 6) (DY.Trace.le_refl t7)
    (by simp only [append_len]) rfl
  have ht3 : trExposureAt t7 (tr.length + 3) = none := by
    unfold trExposureAt
    have hat : (t7.at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32))) :=
      at?_mono h47' (at?_append_at t3 _ (by simp only [t3, t2, t1, t0, append_len]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat, EvT]
  have ht4 : trExposureAt t7 (tr.length + 4) = none := by
    unfold trExposureAt
    have hat : (t7.at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.MessageKey (st.sessionInfo me) .sender
          (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pq st.ns st.rIdx stH)) :=
      at?_mono h57 (at?_append_at t4' _ (by simp only [t4', t3, t2, t1, t0, append_len]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat, EvT]
  change List.filterMap (pqExposureAt t7) _ ++ List.filterMap (trExposureAt t7) _ = []
  simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, ht0, ht1, ht2, ht3, ht4, ht5, ht6]

/-- Expected `.send` visible entry for ciphertext `m`: `.preKeySend` when `wrapped` holds with a
pending prekey pair, and `.whisper` when unwrapped with none. -/
def encSendList (wrapped : Bool) (ppk : Option (Bytes × Bytes)) (m : Bytes) : List VisEntry :=
  match wrapped, ppk with
  | true, some (ek, ct) => [⟨.send, [ek, ct, m], .preKeySend, none⟩]
  | false, none => [⟨.send, [m], .whisper, none⟩]
  | _, _ => []

theorem encTrGen_stepView_ok {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} {pq : Bytes} {wrapped : Bool}
    (hok : (Step.messageEncrypt me stH cl pqH).ok tr = true)
    (hnext : (Step.messageEncrypt me stH cl pqH).next tr = encTrGen tr me stH cl st pq) :
    stepView (.messageEncrypt me stH cl pqH) tr wrapped =
      ⟨.pt, [randTerm tr.length 32], .single, none⟩ ::
      ((if cl != 0 then [rngEntry (randTerm (tr.length + 1) cl)] else []) ++
       encSendList wrapped (pendingPreKey tr stH)
         (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
  unfold stepView
  simp only [hok, ↓reduceIte]
  rw [hnext, encTrGen_newRandoms, encTrGen_exposures, List.append_nil]
  unfold encDraws encSendEntry encSendList
  rw [encTrGen_lastSent]
  by_cases hcl : cl = 0 <;> simp [hcl, List.cons_append] <;>
    (rcases wrapped with _ | _ <;> rcases pendingPreKey tr stH with _ | ⟨_, _⟩ <;> rfl)

private theorem append_singleton_inj {α : Type} {xs₁ xs₂ : List α} {y₁ y₂ : α}
    (h : xs₁ ++ [y₁] = xs₂ ++ [y₂]) : xs₁ = xs₂ ∧ y₁ = y₂ := by
  induction xs₁ generalizing xs₂ with
  | nil =>
    cases xs₂ with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons a as => simp at h
  | cons x xs₁ ih =>
    cases xs₂ with
    | nil => simp at h
    | cons a as =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxs, hy⟩ := ih h.2
      exact ⟨congrArg₂ List.cons h.1 hxs, hy⟩

/-- Steps `.send` call `sIdx` across a network prefix `c.pre`, updates `ActivePartySt` via
`stateBytesAgree_encrypt`, and equates `(ev (sendCallOf sIdx)).exit` with the concrete prekey or
whisper wire bytes under `gClean r cls`. -/
theorem party_send_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {party otherParty : Participant} {initRole : Bool}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {stClean : TRState}
    {ek0 ct0 : Bytes} {sIdx tsPt tsCoins : Nat}
    {tr : ExecTrace} {c : PeeledCall}
    (hne_other : otherParty ≠ party)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (honly : runWrapped (ev (sendCallOf sIdx)) = true → OnlyAliceDone ek0 ct0 tr)
    (hek0 : gamma evictedI0 S g ek0 = gamma evictedI0 S (gClean r cls) o1.ek)
    (hct0 : gamma evictedI0 S g ct0 = gamma evictedI0 S (gClean r cls) o1.ct)
    (hAct : ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx stClean tr)
    (he_party : (ev (sendCallOf sIdx)).party = party ∧
      ∃ peer, (ev (sendCallOf sIdx)).cmd = .send peer)
    (hcl_eq : cls sIdx = stepCoinLen c.s)
    (hpt_clean : (gClean r cls).σ tsPt 32 = (ev (sendCallOf sIdx)).input)
    (hcoins_clean : ∀ n, (gClean r cls).σ tsCoins n = (ev (sendCallOf sIdx)).coins.take n)
    (hwrap_addr :
      (runWrapped (ev (sendCallOf sIdx)) = true ∧
       (gClean r cls).addr (encSig stClean (rnd tsCoins (cls sIdx))
         (DY.Spqr.spqrSend stClean.spqr (rnd tsCoins (cls sIdx))).2.1 (rnd tsPt 32)).wire =
         pqAddrBytes) ∨
      (runWrapped (ev (sendCallOf sIdx)) = false ∧
       (gClean r cls).addr (encSig stClean (rnd tsCoins (cls sIdx))
         (DY.Spqr.spqrSend stClean.spqr (rnd tsCoins (cls sIdx))).2.1 (rnd tsPt 32)).wire = []))
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hpre : c.s.PreCond (runSteps c.pre tr))
    (hlok : c.s.LocalOk (runSteps c.pre tr))
    (hrm : RunMatches evictedI0 r S g (runSteps c.pre tr) c.s (ev (sendCallOf sIdx)) c.v
      (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c.v, w ∈ visAll) :
    let tr' := c.s.next (runSteps c.pre tr)
    let coins' := rnd tsCoins (cls sIdx)
    let pt' := rnd tsPt 32
    let mClean := encMsg stClean coins' (DY.Spqr.spqrSend stClean.spqr coins').2.1 pt'
    PkiUnchanged tr' ∧
    (runWrapped (ev (sendCallOf sIdx)) = true → OnlyAliceDone ek0 ct0 tr') ∧
    ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx (encSt stClean coins') tr' ∧
    NoNewPartyState otherParty tr tr' ∧
    (if runWrapped (ev (sendCallOf sIdx)) then
       (ev (sendCallOf sIdx)).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
         (ecKey (pubBytes evictedI0 (secretBytes r 0)))
         (gamma evictedI0 S (gClean r cls) o1.ek)
         (gamma evictedI0 S (gClean r cls) o1.ct)
         (gamma evictedI0 S (gClean r cls) mClean))
     else
       (ev (sendCallOf sIdx)).exit =
         some (0, wireWhisperTag :: gamma evictedI0 S (gClean r cls) mClean)) := by
  set e := ev (sendCallOf sIdx)
  set tr₁ := runSteps c.pre tr
  have hpki₁ : PkiUnchanged tr₁ := pkiUnchanged_runSteps_network c.pre hnet hpki
  have honly₁ : runWrapped e = true → OnlyAliceDone ek0 ct0 tr₁ :=
    fun hw => onlyAliceDone_runSteps_network c.pre hnet (honly hw)
  have hAct₁ : ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx stClean tr₁ :=
    noNewPartyState_preserves_active (noNewPartyState_runSteps_network c.pre tr hnet) hAct
  obtain ⟨hparty_e, peer, hcmd_e⟩ := he_party
  obtain ⟨hcls_s, hparty, hfits, _, hok, hexit_some, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_e] at hparty
  rw [hcmd_e] at hfits
  cases hs : c.s with
  | messageEncryptAbort me stateIdx =>
    exfalso
    rw [hs, step_ok_encryptAbort_false] at hok
    cases hok
  | messageEncrypt me stateIdx cl pq =>
    rw [hs] at hparty hpre hlok hok hvis_eq hcl_eq hcls_s
    dsimp only [stepCoinLen] at hcl_eq
    rcases Option.some.inj hparty.symm with rfl
    have hpq_eq : pq = tr₁.length + 2 := by
      rcases hlok.2 with hpq2 | hpq3
      · exact hpq2
      · exfalso
        dsimp only [DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx] at hpq3
        rw [hpq3, Symbolic.Proofs.Swarm.UA.XlateSteps.messageEncrypt_fail_not_ok] at hok
        cases hok
    subst hpq_eq
    have hcur : isCurrentSnapshot tr₁ stateIdx = true := preCond_messageEncrypt hpre
    have hok_run : ((DY.Libsignal.TripleRatchet.messageEncrypt party stateIdx cl (tr₁.length + 2)).run tr₁).1.isSome = true := by
      rwa [step_ok_encrypt] at hok
    unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok_run
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hok_run
    rcases hst : ((DY.PersistentLocalState.getLocalState party stateIdx : Traceful TRState).run tr₁).1 with _ | st
    · simp [hst] at hok_run
    · obtain ⟨hinit, hagree, hrecv, hdhs⟩ := activePartySt_pin_state hAct₁ hst hcur
      have hat_st : tr₁.at? stateIdx = some (StT party st) :=
        Symbolic.Swarm.CREF.bks_stored_of_getLocalState hst
      rw [hst, Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd] at hok_run
      dsimp only at hok_run
      have hns : st.ns ≠ u32Max := by
        intro hmax
        have hf : ((failure : Traceful Unit).run tr₁).1 = none := by rw [DY.Traceful.run_failure]
        simp [_root_.guard, hmax, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hf] at hok_run
      let pqSalt := (DY.Spqr.spqrSend st.spqr (rnd (tr₁.length + 1) cl)).2.1
      have hpq_at : (((tr₁.append (RndE 32)).append (RndE cl)).append (NetE pqSalt)).at?
          (tr₁.length + 2) = some (NetE pqSalt) :=
        at?_append_at _ _ (by simp only [append_len])
      have hruns :=
        Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase.Runs.messageEncryptGen
          hat_st hns hpq_at
      have hnext_eq : (Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁ =
          encTrGen tr₁ party stateIdx cl st pqSalt := by
        rw [step_next_encrypt]
        exact hruns.2
      have hview := encTrGen_stepView_ok (wrapped := runWrapped e) hok hnext_eq
      obtain ⟨out, hexit_e⟩ := hexit_some
      unfold OutputsMatch at hout
      rw [hexit_e, hcmd_e] at hout
      obtain ⟨v_out, rfl, hbm_out⟩ := hout
      have hv_comb := hv_split.symm.trans (hvis_eq.trans hview)
      injection hv_comb with hinp_eq hdrs_out_eq
      have hpt_gam : gamma evictedI0 S g (rnd tr₁.length 32) =
          gamma evictedI0 S (gClean r cls) (rnd tsPt 32) := by
        have hin_k : inputKind e = .pt := by unfold inputKind; rw [hcmd_e]
        rw [hin_k, hinp_eq] at hbm_in
        have h1 : gamma evictedI0 S g (randTerm tr₁.length 32) = e.input := by
          simpa using hbm_in.2
        have h2 : gamma evictedI0 S (gClean r cls) (rnd tsPt 32) = e.input := by
          unfold rnd; rw [gamma_rand]; simp [hpt_clean]
        exact h1.trans h2.symm
      let encOpt : List VisEntry := encSendList (runWrapped e) (pendingPreKey tr₁ stateIdx)
        (encMsg st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32))
      have hencOpt_nonempty : ∃ v_s, encOpt = [v_s] := by
        dsimp only [encOpt, encSendList]
        rcases hw : runWrapped e with _ | _ <;> rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · exact ⟨_, rfl⟩
        · exfalso
          rw [hw, hppk] at hdrs_out_eq
          dsimp only [encSendList] at hdrs_out_eq
          rw [List.append_nil] at hdrs_out_eq
          have hmem : v_out ∈ (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) := by
            rw [← hdrs_out_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
          by_cases hcl0 : cl = 0 <;> simp [hcl0, rngEntry] at hmem
          subst hmem; cases hbm_out.1
        · exfalso
          rw [hw, hppk] at hdrs_out_eq
          dsimp only [encSendList] at hdrs_out_eq
          rw [List.append_nil] at hdrs_out_eq
          have hmem : v_out ∈ (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) := by
            rw [← hdrs_out_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
          by_cases hcl0 : cl = 0 <;> simp [hcl0, rngEntry] at hmem
          subst hmem; cases hbm_out.1
        · exact ⟨_, rfl⟩
      obtain ⟨v_s, hv_s⟩ := hencOpt_nonempty
      change drs ++ [v_out] = (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) ++ encOpt at hdrs_out_eq
      rw [hv_s] at hdrs_out_eq
      obtain ⟨hdrs_eq, rfl⟩ := append_singleton_inj hdrs_out_eq
      have hc_gam : gamma evictedI0 S g (rnd (tr₁.length + 1) cl) =
          gamma evictedI0 S (gClean r cls) (rnd tsCoins (cls sIdx)) := by
        rw [hcl_eq]
        by_cases hcl0 : cl = 0
        · subst hcl0; unfold rnd; rw [gamma_rand, gamma_rand]; simp
        · have hdrs_1 : drs = [rngEntry (randTerm (tr₁.length + 1) cl)] := by
            simpa [hcl0] using hdrs_eq
          rw [hdrs_1] at hdr
          have hmem_rng : rngEntry (randTerm (tr₁.length + 1) cl) ∈ visAll := by
            apply hsub
            rw [hv_split, hdrs_1]; simp
          have hlen_c : (gamma evictedI0 S g (randTerm (tr₁.length + 1) cl)).length = cl := by
            have hsig := hgwf.1 _ hmem_rng rfl (tr₁.length + 1) cl hcl0 (by simp [rngEntry])
            unfold randTerm; rw [gamma_rand]; simpa [hcl0] using hsig
          obtain ⟨pieces, _, hpref, hrel⟩ := hdr
          cases pieces with
          | nil => cases hrel
          | cons p0 ps_tl =>
            cases hrel with
            | cons hp0 htl =>
              cases ps_tl with
              | cons _ _ => cases htl
              | nil =>
                have hp0_eq : gamma evictedI0 S g (randTerm (tr₁.length + 1) cl) = p0 := by
                  simpa [rngEntry] using hp0.2
                simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
                obtain ⟨rem_c, hcoins_eq⟩ := hpref
                have htake_c : e.coins.take cl = p0 := by
                  rw [← hcoins_eq]; exact List.take_left' (hp0_eq ▸ hlen_c)
                have hg_clean : gamma evictedI0 S (gClean r cls) (rnd tsCoins cl) = e.coins.take cl := by
                  unfold rnd; rw [gamma_rand]; simp [hcl0, hcoins_clean]
                exact hp0_eq.trans (htake_c.symm.trans hg_clean.symm)
      have hv_s_mem : v_out ∈ visAll := by
        apply hsub; rw [hv_split]; simp
      have hpki₂ : PkiUnchanged ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        pkiUnchanged_step_party rfl hpki₁
      have honly₂ : runWrapped e = true →
          OnlyAliceDone ek0 ct0 ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        fun hw => onlyAliceDone_messageEncrypt (honly₁ hw)
      have hnoOther₂ : NoNewPartyState otherParty tr ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        noNewPartyState_trans (noNewPartyState_runSteps_network c.pre tr hnet)
          (noNewPartyState_step_other tr₁ rfl (by simp [Step.party?, Ne.symm hne_other]))
      have hst_upd : StateBytesAgree S g (gClean r cls)
          (encSt st (rnd (tr₁.length + 1) cl)) (encSt stClean (rnd tsCoins (cls sIdx))) →
          ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx
            (encSt stClean (rnd tsCoins (cls sIdx)))
            ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) := by
        intro hst_ag'
        rw [hnext_eq]
        have hle_enc := encTrGen_le tr₁ party stateIdx cl st pqSalt
        have hge_idx : tr₁.length ≤ tr₁.length + 5 := by omega
        have hat_new : ((encTrGen tr₁ party stateIdx cl st pqSalt).at? (tr₁.length + 5) : Option TRStEntry) =
            some ⟨⟨party, encSt st (rnd (tr₁.length + 1) cl)⟩⟩ := by
          dsimp only [encTrGen]
          rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
          exact at?_append_at _ _ (by simp only [append_len])
        refine activePartySt_of_unique_new hAct₁ hle_enc hge_idx hat_new ?_ hinit hst_ag' hrecv hdhs
        intro j s0 hj hat_j
        dsimp only [encTrGen] at hat_j
        rcases at?_append_cases hat_j with ⟨hlt6, hat6⟩ | ⟨_, hp6⟩
        · rcases at?_append_cases hat6 with ⟨hlt5, hat5⟩ | ⟨heq5, hp5⟩
          · rcases at?_append_cases hat5 with ⟨_, hat4⟩ | ⟨_, hp4⟩
            · rcases at?_append_cases hat4 with ⟨_, hat3⟩ | ⟨_, hp3⟩
              · rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hp2⟩
                · rcases at?_append_cases hat2 with ⟨_, hat1⟩ | ⟨_, hp1⟩
                  · rcases at?_append_cases hat1 with ⟨hlt0, _⟩ | ⟨_, hp0⟩
                    · omega
                    · cases hp0
                  · cases hp1
                · cases hp2
              · cases hp3
            · cases hp4
          · have hj5 : j = tr₁.length + 5 := by simp only [append_len] at heq5; omega
            subst hj5
            simp only [StT, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq, Option.some.injEq] at hp5
            injection hp5 with h1; injection h1 with _ hs0
            exact ⟨rfl, hs0.symm⟩
        · cases hp6
      rcases hwrap_addr with ⟨hw_true, haddr_clean⟩ | ⟨hw_false, haddr_clean⟩
      · dsimp only [encOpt] at hv_s
        rw [hw_true] at hv_s ⊢
        simp only [↓reduceIte]
        rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · rw [hppk] at hv_s; cases hv_s
        · rw [hppk] at hv_s
          dsimp only [encSendList] at hv_s
          simp only [List.cons.injEq, and_true] at hv_s
          subst hv_s
          obtain ⟨rfl, rfl⟩ := pendingPreKey_eq_of_onlyAliceDone (honly₁ hw_true) hppk
          have haddr_ss : g.addr (encSig st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32)).wire =
              pqAddrBytes :=
            (hgwf.2.2 _ hv_s_mem rfl).1 rfl _ _ _ _ rfl (parse_encMsg _ _ _ _)
          obtain ⟨hst_ag', hm_eq⟩ := stateBytesAgree_encrypt hagree hc_gam hpt_gam
            (haddr_ss.trans haddr_clean.symm)
          have hsm := hbm_out.2
          dsimp only [DY.Libsignal.Composed.Refinement.SendMatches] at hsm
          obtain ⟨pkId, spkId, kpkId, hids_eq, hout_wire⟩ := hsm
          injection hids_eq with hprod
          obtain ⟨rfl, hprod2⟩ := Prod.mk.inj hprod
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hprod2
          rw [hek0, hct0, hm_eq] at hout_wire
          exact ⟨hpki₂, fun _ => honly₂ hw_true, hst_upd hst_ag', hnoOther₂,
            hexit_e.trans (congrArg (some ∘ (0, ·)) hout_wire)⟩
      · dsimp only [encOpt] at hv_s
        rw [hw_false] at hv_s ⊢
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · rw [hppk] at hv_s
          dsimp only [encSendList] at hv_s
          simp only [List.cons.injEq, and_true] at hv_s
          subst hv_s
          have haddr_ss : g.addr (encSig st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32)).wire = [] :=
            (hgwf.2.2 _ hv_s_mem rfl).2 rfl _ _ rfl (parse_encMsg _ _ _ _)
          obtain ⟨hst_ag', hm_eq⟩ := stateBytesAgree_encrypt hagree hc_gam hpt_gam
            (haddr_ss.trans haddr_clean.symm)
          obtain ⟨t_w, ht_eq, hout_wire⟩ := hbm_out.2
          simp only [List.cons.injEq, and_true] at ht_eq
          subst ht_eq
          rw [hm_eq] at hout_wire
          exact ⟨hpki₂, False.elim, hst_upd hst_ag', hnoOther₂,
            hexit_e.trans (congrArg (some ∘ (0, ·)) hout_wire)⟩
        · rw [hppk] at hv_s; cases hv_s
  | _ => rw [hs] at hfits; cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSend
