/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.ProtocolEvent
import DY.Actions.Network
import DY.Actions.PersistentGlobalState
import DY.Actions.PersistentLocalState
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.TR.Leaks
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.Cli.World.HeldRecPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.LeakModelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Leak-Phase Stepping for `Clean`, `PureCRel`, and `COpkRelC`

Steps `Clean`, `PureCRel`, and `COpkRelC` across blocks of `.leak` events drawn from
`LeakableSecret` or `KeyInDirsV1`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open DY.Libsignal.Composed.Refinement.Cli (CliTurn KeyInDirsV1)

/-! ## Stepping `Clean` across `LeakKind` moves -/

private theorem eventIdx_isAliceDone_of_leakKind (tr : ExecTrace) {m : Move} (hk : LeakKind m) :
    eventIdx isAliceDone tr (m.next tr) = none := by
  unfold eventIdx
  refine List.find?_eq_none.mpr fun i hi => ?_
  rcases leakKind_next_cases tr hk with ⟨hnext, _⟩ | ⟨ev, msg, _, hnext, _⟩ |
      ⟨ev, msg, pq, hpq, hnext, _⟩
  · rw [hnext] at hi
    simp [newIndices] at hi
  · rw [hnext] at hi ⊢
    rw [TR.newIndices_append_pair] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · have hlt : tr.length < (tr.append (⟨ev⟩ : LeakTREntry)).length := by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have h0 : (((tr.append (⟨ev⟩ : LeakTREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
          PQXDHEvent tr.length) = none := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [TR.at?_append_of_lt _ _ hlt, TR.at?_append_eq_of_proj _ _ rfl none rfl]
      simp [h0]
    · rcases List.mem_singleton.mp hi with rfl
      have h1 : (((tr.append (⟨ev⟩ : LeakTREntry)).append (⟨msg⟩ : Network.ExecEntryT)).getEventAt
          PQXDHEvent (tr.length + 1)) = none := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [TR.at?_append_eq_of_proj (tr.append _) _ (i := tr.length + 1)
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) none rfl]
      simp [h1]
  · rw [hnext] at hi ⊢
    rw [TR.newIndices_append_pair] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · have hlt : tr.length < (tr.append (TR.EvE ev)).length := by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have h0 : (((tr.append (TR.EvE ev)).append (TR.NetE msg)).getEventAt
          PQXDHEvent tr.length) = some ev := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [TR.at?_append_of_lt _ _ hlt, TR.at?_append_self]
      rw [h0]
      cases ev <;> simp_all [TR.pqLeakKind, isAliceDone]
    · rcases List.mem_singleton.mp hi with rfl
      have h1 : (((tr.append (TR.EvE ev)).append (TR.NetE msg)).getEventAt
          PQXDHEvent (tr.length + 1)) = none := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        rw [TR.at?_append_eq_of_proj (tr.append _) _ (i := tr.length + 1)
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]) none rfl]
      simp [h1]

theorem clean_snoc_leakKind {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move} {m : Move}
    {acc : List MachineEvent} {k : HwBytes}
    (hc : Clean interpretation r S who ok g ms acc)
    (hlk : LeakKind m)
    (hmp' : MatchedPrefix interpretation r S who g (ms ++ [m]) (acc ++ [.leak k])) :
    Clean interpretation r S who ok g (ms ++ [m]) (acc ++ [.leak k]) := by
  refine ⟨⟨hmp', outcomeFaithful_snoc_neutral hc.1.2
      (fun ds hrej => by subst hrej; exact hlk)
      (eventIdx_isAliceDone_of_leakKind (runTraceMoves r ms) hlk)⟩,
    not_readCollision_append_noAccept hc.2
      (fun e he pt hacc => by rw [List.mem_singleton.mp he] at hacc; cases hacc)
      (fun m' hm' _ _ hcol => by
        rw [List.mem_singleton.mp hm'] at hcol
        cases m <;> first | exact False.elim hlk | exact False.elim hcol)⟩

private theorem find?_eq_some_of_mem_of_map_nodup {α β : Type} (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) {x : α} (hx : x ∈ l) (p : α → Bool)
    (hpx : p x = true) (hpf : ∀ y, p y = true → f y = f x) :
    l.find? p = some x := by
  induction l with
  | nil => cases hx
  | cons a xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [List.find?, hpx]
    · have hpa : p a = false := by
        cases hp : p a
        · rfl
        · exact False.elim (hnd.1 ⟨x, hx', (hpf a hp).symm⟩)
      simp [List.find?, hpa, ih hnd.2 hx']

private theorem stateRel_fields {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec} (hsr : TR.StateRel interpretation S g st rec) :
    rec.current.rootKey = gamma interpretation S g st.rk ∧
    rec.current.senderChain = (TR.sessionOf interpretation (gamma interpretation S g) st).senderChain ∧
    rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) =
      (TR.sessionOf interpretation (gamma interpretation S g) st).receiverChains ∧
    rec.current.pqRatchetState = gamma interpretation S g st.spqr := by
  have h := hsr.2
  exact ⟨by simpa [TR.eraseSkipped, TR.eraseUnmodelled, TR.sessionOf] using congrArg SessionRec.rootKey h,
    by simpa [TR.eraseSkipped, TR.eraseUnmodelled] using congrArg SessionRec.senderChain h,
    by simpa [TR.eraseSkipped, TR.eraseUnmodelled] using congrArg SessionRec.receiverChains h,
    by simpa [TR.eraseSkipped, TR.eraseUnmodelled, TR.sessionOf] using congrArg SessionRec.pqRatchetState h⟩

private theorem someEventOnTraceB_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') {P : TREvent → Bool}
    (hP : ∀ ev, TR.IsAnyExposureEv ev → P ev = false) :
    (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) t' P = (TripleRatchet.anyEventOnTrace TripleRatchet.TREvent) t P := by
  apply Bool.eq_iff_iff.mpr
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi', hpi⟩
    by_cases hi : i < t.length
    · refine ⟨i, hi, ?_⟩
      have heq : (t'.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          (t.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) := by
        simp only [Trace.at?, hi, hi', ↓reduceDIte, Trace.at_le t t' i hi h.1]
      rwa [heq] at hpi
    · rcases hat : (t'.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with _ | ev
      · rw [hat] at hpi; cases hpi
      · rw [hat] at hpi; dsimp only at hpi
        have hproj : TraceEntryHas.proj (t'.at i hi') = some ev := by
          simp only [Trace.at?, hi', ↓reduceDIte] at hat; exact hat
        rw [hP ev.ev ((h.2 i hi' (Nat.le_of_not_lt hi)).2 ev hproj)] at hpi; cases hpi
  · rintro ⟨i, hi, hpi⟩
    have hi' : i < t'.length := Nat.lt_of_lt_of_le hi (Trace.length_le t t' h.1)
    refine ⟨i, hi', ?_⟩
    have heq : (t'.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        (t.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) := by
      simp only [Trace.at?, hi, hi', ↓reduceDIte, Trace.at_le t t' i hi h.1]
    rwa [heq]

private theorem skippedKeyUsedB_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') (skIdx : Nat) :
    TripleRatchet.skippedKeyUsedB t' skIdx = TripleRatchet.skippedKeyUsedB t skIdx :=
  someEventOnTraceB_of_appendsOnlyExposure h
    (fun ev hev => by cases ev <;> simp_all [TR.IsAnyExposureEv])

private theorem receiverKeyUsedB_of_appendsOnlyExposure {t t' : ExecTrace}
    (h : TR.AppendsOnlyExposure t t') (s : TripleRatchet.SessionInfo) (seed : DY.Bytes)
    (n : UInt32) (rIdx : Nat) :
    TripleRatchet.receiverKeyUsedB t' s seed n rIdx =
      TripleRatchet.receiverKeyUsedB t s seed n rIdx :=
  someEventOnTraceB_of_appendsOnlyExposure h
    (fun ev hev => by cases ev <;> simp_all [TR.IsAnyExposureEv])

private theorem pureRecordStateInv_of_appendsOnlyExposure
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost}
    {ms ms' : List Move} {records : Participant → Option HwBytes}
    (hexp : TR.AppendsOnlyExposure (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (hinv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r₀ S Z g ms' records := by
  intro p b hpb
  obtain ⟨hp, rec, st, stIdx, rfl, hget, hcurr, hsr, hkeys, hcanon, hks, hnd⟩ := hinv p b hpb
  refine ⟨hp, rec, st, stIdx, rfl, ?_, ?_, hsr, ?_, hcanon, hks, hnd⟩
  · rwa [TR.getLocalState_fst_of_appendsOnlyExposure hexp]
  · rwa [TR.isCurrentSnapshot_of_appendsOnlyExposure hexp]
  · intro c hc k' hk'
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam⟩ := hkeys c hc k' hk'
    refine ⟨pk, rIdx, srcIdx, skIdx, seed, Trace.EventLoggedAt_le _ _ _ _ hexp.1 hlog, ?_, ?_, hgam⟩
    · rwa [skippedKeyUsedB_of_appendsOnlyExposure hexp]
    · rwa [receiverKeyUsedB_of_appendsOnlyExposure hexp]

private theorem pureRecordStateInv_snoc_exposeSpqr
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost}
    {ms : List Move} {me : Participant} {stateIdx : Nat}
    {records : Participant → Option HwBytes}
    (hinv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [.exposeSpqr me stateIdx]) records := by
  apply pureRecordStateInv_of_appendsOnlyExposure _ hinv
  rw [TR.runTrace_snoc r₀ ms (.exposeSpqr me stateIdx), TR.exposeSpqr_next_eq]
  exact TR.exposeSpqr_appendsOnlyExposure me stateIdx (runTraceMoves r₀ ms)

private theorem pureRecordStateInv_snoc_exposeKey
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost}
    {ms : List Move} {me : Participant} {stateIdx : Nat} {k : TripleRatchet.KeyComponent}
    {records : Participant → Option HwBytes}
    (hinv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [.exposeKey me stateIdx k]) records := by
  apply pureRecordStateInv_of_appendsOnlyExposure _ hinv
  rw [TR.runTrace_snoc r₀ ms (.exposeKey me stateIdx k), TR.exposeKey_next_eq]
  exact TR.exposeKey_appendsOnlyExposure me stateIdx k (runTraceMoves r₀ ms)

private theorem pureRecordStateInv_snoc_exposeSkipped
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost}
    {ms : List Move} {skIdx : Nat}
    {records : Participant → Option HwBytes}
    (hinv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records) :
    TR.PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [.exposeSkipped skIdx]) records := by
  apply pureRecordStateInv_of_appendsOnlyExposure _ hinv
  rw [TR.runTrace_snoc r₀ ms (.exposeSkipped skIdx), TR.exposeSkipped_next_eq]
  exact TR.exposeSkipped_appendsOnlyExposure skIdx (runTraceMoves r₀ ms)

private theorem single_record_leak_step
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots}
    {who : List Participant} {g : Ghost}
    {ms : List Move} {acc : List MachineEvent}
    {records : Participant → Option HwBytes} {k : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hrecInv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records)
    (he : ∃ p rec, records p = some (recordBytes rec) ∧ KeyInRecord rec k) :
    ∃ m, LeakKind m ∧ MatchedPrefix interpretation r₀ S who g (ms ++ [m]) (acc ++ [.leak k]) ∧
      TR.PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m]) records ∧
      TR.AppendsOnlyExposure (runTraceMoves r₀ ms) (runTraceMoves r₀ (ms ++ [m])) := by
  obtain ⟨p, rec_env, hpb, hkey_env⟩ := he
  obtain ⟨_hp_ab, rec, st, stateIdx, heq_bytes, hget, hcurr, hsr, hkeys, _, _, hnd⟩ :=
    hrecInv p (recordBytes rec_env) hpb
  have hkey : KeyInRecord rec k := TR.keyInRecord_of_recordBytes_eq heq_bytes hkey_env
  clear hkey_env
  obtain ⟨hrk_eq, hsc_eq, hrc_eq, hpq_eq⟩ := stateRel_fields hsr
  have hnocs : ∀ ev ∈ ([MachineEvent.leak k] : List MachineEvent),
      eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
    intro ev hev; rw [List.mem_singleton.mp hev]; simp [eventKind]
  rcases hkey with rfl | ⟨sc, hsc, rfl | ⟨ck, hck, rfl⟩⟩ |
      ⟨rc, hrc, ⟨hne, _⟩ | ⟨ck, hck, rfl⟩ | ⟨mk, hmk, rfl⟩⟩ | rfl
  · refine ⟨.exposeKey p stateIdx .rk, trivial,
      TR.matchedPrefix_snoc_env hmp (TR.modelRun_snoc_exposeKey r₀ ms p stateIdx .rk hmp.2.1 hcurr)
        rfl rfl hnocs (by rw [TR.visOf_exposeKey_rk hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeKey_rk hget]; exact .cons ⟨rfl, _, rfl, .inl hrk_eq⟩ .nil),
      pureRecordStateInv_snoc_exposeKey hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeKey_next_eq]
    exact TR.exposeKey_appendsOnlyExposure p stateIdx .rk (runTraceMoves r₀ ms)
  · rw [hsc_eq] at hsc; dsimp only [TR.sessionOf] at hsc; injection hsc with hsc'; subst hsc'
    refine ⟨.exposeKey p stateIdx .dhs, trivial,
      TR.matchedPrefix_snoc_env hmp (TR.modelRun_snoc_exposeKey r₀ ms p stateIdx .dhs hmp.2.1 hcurr)
        rfl rfl hnocs (by rw [TR.visOf_exposeKey_dhs hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeKey_dhs hget]; exact .cons ⟨rfl, _, rfl, .inr rfl⟩ .nil),
      pureRecordStateInv_snoc_exposeKey hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeKey_next_eq]
    exact TR.exposeKey_appendsOnlyExposure p stateIdx .dhs (runTraceMoves r₀ ms)
  · rw [hsc_eq] at hsc; dsimp only [TR.sessionOf] at hsc; injection hsc with hsc'; subst hsc'
    dsimp only at hck; injection hck with hck'; subst hck'
    refine ⟨.exposeKey p stateIdx .cks, trivial,
      TR.matchedPrefix_snoc_env hmp (TR.modelRun_snoc_exposeKey r₀ ms p stateIdx .cks hmp.2.1 hcurr)
        rfl rfl hnocs (by rw [TR.visOf_exposeKey_cks hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeKey_cks hget]; exact .cons ⟨rfl, _, rfl, .inl rfl⟩ .nil),
      pureRecordStateInv_snoc_exposeKey hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeKey_next_eq]
    exact TR.exposeKey_appendsOnlyExposure p stateIdx .cks (runTraceMoves r₀ ms)
  · have hmem_map : { rc with messageKeys := [] } ∈
        rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
      List.mem_map.mpr ⟨rc, hrc, rfl⟩
    rw [hrc_eq] at hmem_map; dsimp only [TR.sessionOf] at hmem_map
    obtain ⟨_, _, hc₀_eq⟩ := List.mem_map.mp hmem_map
    exact absurd (congrArg ChainRec.senderRatchetKeyPrivate hc₀_eq).symm hne
  · have hmem_map : { rc with messageKeys := [] } ∈
        rec.current.receiverChains.map (fun c => { c with messageKeys := [] }) :=
      List.mem_map.mpr ⟨rc, hrc, rfl⟩
    rw [hrc_eq] at hmem_map; dsimp only [TR.sessionOf] at hmem_map
    obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := List.mem_map.mp hmem_map
    have hck_eq : rc.chainKey =
        some (c₀.index.toBitVec, gamma interpretation S g c₀.chainKey) :=
      (congrArg ChainRec.chainKey hc₀_eq).symm
    rw [hck_eq] at hck; injection hck with hck'; subst hck'
    have hmap_srk : st.recv.map (fun c => TR.serializedKey (gamma interpretation S g c.ratchetKey)) =
        rec.current.receiverChains.map ChainRec.senderRatchetKey := by
      have h1 := congrArg (List.map ChainRec.senderRatchetKey) hrc_eq.symm
      rw [List.map_map] at h1; dsimp only [TR.sessionOf] at h1; rw [List.map_map] at h1
      exact h1
    have hnd_recv :
        (st.recv.map (fun c => TR.serializedKey (gamma interpretation S g c.ratchetKey))).Nodup := by
      rw [hmap_srk]; exact hnd.1
    have hfind : DY.Libsignal.TripleRatchet.findRecvChain st.recv c₀.ratchetKey = some c₀ :=
      find?_eq_some_of_mem_of_map_nodup
        (fun c => TR.serializedKey (gamma interpretation S g c.ratchetKey))
        hnd_recv hc₀_mem (·.ratchetKey == c₀.ratchetKey) (beq_self_eq_true _)
        (fun _ hy => by rw [beq_iff_eq.mp hy])
    refine ⟨.exposeKey p stateIdx (.ckr c₀.ratchetKey), trivial,
      TR.matchedPrefix_snoc_env hmp
        (TR.modelRun_snoc_exposeKey r₀ ms p stateIdx (.ckr c₀.ratchetKey) hmp.2.1 hcurr)
        rfl rfl hnocs
        (by rw [TR.visOf_exposeKey_ckr hget hfind]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeKey_ckr hget hfind]; exact .cons ⟨rfl, _, rfl, .inl rfl⟩ .nil),
      pureRecordStateInv_snoc_exposeKey hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeKey_next_eq]
    exact TR.exposeKey_appendsOnlyExposure p stateIdx (.ckr c₀.ratchetKey) (runTraceMoves r₀ ms)
  · obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, _, hru, hgam, _, _⟩ := hkeys rc hrc mk hmk
    have hlog' := hlog
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
    refine ⟨.exposeSkipped skIdx, trivial,
      TR.matchedPrefix_snoc_env hmp (TR.modelRun_snoc_exposeSkipped r₀ ms skIdx hmp.2.1)
        rfl rfl hnocs
        (by rw [TR.visOf_exposeSkipped hlog' hru]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeSkipped hlog' hru]; exact .cons ⟨rfl, _, rfl, .inl hgam.symm⟩ .nil),
      pureRecordStateInv_snoc_exposeSkipped hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeSkipped_next_eq]
    exact TR.exposeSkipped_appendsOnlyExposure skIdx (runTraceMoves r₀ ms)
  · refine ⟨.exposeSpqr p stateIdx, trivial,
      TR.matchedPrefix_snoc_env hmp (TR.modelRun_snoc_exposeSpqr r₀ ms p stateIdx hmp.2.1 hcurr)
        rfl rfl hnocs
        (by rw [TR.visOf_exposeSpqr hget]; intro _ hv; rw [List.mem_singleton.mp hv]; rintro ⟨⟩)
        (by rw [TR.visOf_exposeSpqr hget]; exact .cons ⟨rfl, _, rfl, .inl hpq_eq⟩ .nil),
      pureRecordStateInv_snoc_exposeSpqr hrecInv, ?_⟩
    rw [TR.runTrace_snoc, TR.exposeSpqr_next_eq]
    exact TR.exposeSpqr_appendsOnlyExposure p stateIdx (runTraceMoves r₀ ms)

theorem leakable_leaks_step_clean
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms : List Move} {acc evs : List MachineEvent} {records : Participant → Option HwBytes}
    {used : Bool} (hne : r₀.alice ≠ r₀.bob)
    (hc : Clean interpretation r₀ S who ok g ms acc)
    (hrecInv : TR.PureTRRecordStateInv interpretation r₀ S Z g ms records)
    (hevs : ∀ e ∈ evs, ∃ k, LeakableSecret r₀ records used k ∧ e = .leak k)
    (hopk_unused : r₀.withOpk = true → used = false →
      DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r₀ ms) r₀.bob (setupPublic r₀ 8) = false) :
    ∃ ms₁, Clean interpretation r₀ S who ok g ms₁ (acc ++ evs) ∧
      TR.PureTRRecordStateInv interpretation r₀ S Z g ms₁ records ∧
      TR.AppendsOnlyExposure (runTraceMoves r₀ ms) (runTraceMoves r₀ ms₁) := by
  induction evs generalizing ms acc with
  | nil =>
    refine ⟨ms, ?_, hrecInv, TR.AppendsOnlyExposure.refl (runTraceMoves r₀ ms)⟩
    rw [List.append_nil]; exact hc
  | cons e evs ih =>
    obtain ⟨k, hk, rfl⟩ := hevs e (List.mem_cons_self ..)
    have hstep : ∃ m, LeakKind m ∧
        MatchedPrefix interpretation r₀ S who g (ms ++ [m]) (acc ++ [.leak k]) ∧
        TR.PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m]) records ∧
        TR.AppendsOnlyExposure (runTraceMoves r₀ ms) (runTraceMoves r₀ (ms ++ [m])) := by
      rcases TR.leakableSecret_cases hk with hs | ⟨p, rec, hp, hkr⟩
      · obtain ⟨m, hm, hmp', hexp'⟩ := TR.setupLeak_step hne hc.1.1 hs hopk_unused
        have hlk : LeakKind m := by cases m <;> cases hm <;> trivial
        exact ⟨m, hlk, hmp', pureRecordStateInv_of_appendsOnlyExposure hexp' hrecInv, hexp'⟩
      · exact single_record_leak_step hc.1.1 hrecInv ⟨p, rec, hp, hkr⟩
    obtain ⟨m, hlk, hmp', hrecInv', hexp'⟩ := hstep
    have hc' : Clean interpretation r₀ S who ok g (ms ++ [m]) (acc ++ [.leak k]) :=
      clean_snoc_leakKind hc hlk hmp'
    have hopk_unused' : r₀.withOpk = true → used = false →
        DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r₀ (ms ++ [m])) r₀.bob (setupPublic r₀ 8) = false := by
      intro hw hu
      rw [TR.runTrace_snoc, opkUsedB_next_of_not_bobStart _ _ _ m (by intros _ _ _ _ _ _ _ _ h; subst h; exact hlk)]
      exact hopk_unused hw hu
    obtain ⟨ms₁, hc₁, hrecInv₁, hexp₁⟩ :=
      ih hc' hrecInv' (fun e' he' => hevs e' (List.mem_cons_of_mem _ he')) hopk_unused'
    refine ⟨ms₁, ?_, hrecInv₁, TR.AppendsOnlyExposure.trans hexp' hexp₁⟩
    simpa using hc₁

theorem bks_leak {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant}
    {records : Participant → Option HwBytes} {acc evs : List MachineEvent} {g : Ghost}
    {ms δ : List Move} (hB : XplBlock interpretation r S who g ms δ acc evs)
    (hleak : ∀ ev ∈ evs, eventKind ev = .leak)
    (h : BobRecordBaseKeyInSession interpretation r S g ms records) :
    BobRecordBaseKeyInSession interpretation r S g (ms ++ δ) records := by
  have hexp := appendsOnlyExposure_of_leakBlock hB hleak
  refine bks_of_ext (newBobSinfo_of_noNewSt fun j hj => ?_) (bks_rec_of_eq rfl) h
  rw [at?_stEntry_of_appendsOnlyExposure hexp j]
  exact (XplSteps.xnone_of_ge hj).1

/-! ## Transporting `PureCRel` and `COpkRelC` across leak blocks -/

theorem pureAliceInitPending_of_appendsOnlyExposure {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {b : HwBytes}
    (hexp : TR.AppendsOnlyExposure (runTraceMoves r ms) (runTraceMoves r ms'))
    (hp : PureAliceInitPending interp r S g ms b) :
    PureAliceInitPending interp r S g ms' b := by
  obtain ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, hget, hcur, h6, h7, hek, hct, rest⟩ := hp
  exact ⟨sess, sc, remote, items, kpk, st, stateIdx, ekIdx, ctIdx, ek, ct,
    h1, h2, h3, by rw [TR.getLocalState_fst_of_appendsOnlyExposure hexp]; exact hget,
    by rw [TR.isCurrentSnapshot_of_appendsOnlyExposure hexp]; exact hcur, h6, h7,
    getMessageSentAt_of_le hexp.1 hek, getMessageSentAt_of_le hexp.1 hct, rest⟩

theorem pureCRecRel_of_appendsOnlyExposure {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move}
    {p : Participant} {b : HwBytes}
    (hexp : TR.AppendsOnlyExposure (runTraceMoves r ms) (runTraceMoves r ms'))
    (hc : PureCRecRel interp r S g ms p b) :
    PureCRecRel interp r S g ms' p b := by
  rcases hc with hc | ⟨hpa, hc⟩
  · exact Or.inl (pureRecordStateInv_of_appendsOnlyExposure hexp hc)
  · exact Or.inr ⟨hpa, pureAliceInitPending_of_appendsOnlyExposure hexp hc⟩

theorem cHist_of_appendsOnlyExposure {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move}
    (hexp : TR.AppendsOnlyExposure (runTraceMoves r ms) (runTraceMoves r ms'))
    (hc : CHist interp r S g ms) :
    CHist interp r S g ms' := by
  obtain ⟨hlen, hlow, hfresh, hnd⟩ := hc
  refine ⟨fun st hst => hlen st (availableStates_of_appendsOnlyExposure hexp hst),
    fun st hst => hlow st (availableStates_of_appendsOnlyExposure hexp hst), ?_,
    fun st hst => hnd st (availableStates_of_appendsOnlyExposure hexp hst)⟩
  intro s pk n seed rIdx src i p₀ st₀ c₀ hlog hstored hfor
  exact hfresh s pk n seed rIdx src i p₀ st₀ c₀
    (skippedKeyStored_of_appendsOnlyExposure hexp hlog)
    ((at?_stEntry_of_appendsOnlyExposure hexp src).symm.trans hstored) hfor

theorem pureCRelAt_leak {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {acc evs : List MachineEvent} {g : Ghost} {ms δ : List Move}
    (hB : XplBlock interp r S who g ms δ acc evs)
    (hleak : ∀ ev ∈ evs, eventKind ev = .leak)
    (hsent : TR.sentBodies (acc ++ evs) = TR.sentBodies acc)
    (hb : PureCRelAt interp r S g ms records sent accepted acc) :
    PureCRelAt interp r S g (ms ++ δ) records sent accepted (acc ++ evs) := by
  have hs := hB.run.2.1
  have hanc := hB.run.2.2.1.2.1
  have hanc' := xpl_movesAnchored_append_right ms δ (setupTrace r) hanc
  rw [← xpl_runTrace_eq] at hanc'
  obtain ⟨hexp, hbd⟩ := leak_moves_effect δ (runTraceMoves r ms) evs
    (xpl_movesFrom_of δ _ (fun m hm => hs m (List.mem_append_right _ hm)) hanc')
    hB.matched hleak
  rw [← TR.runTrace_append] at hexp hbd
  obtain ⟨hrec, ⟨hs_eq, hns, hacc1, hacc2⟩, hhist, hrole⟩ := hb
  refine ⟨fun p b hpb => ?_, ⟨hs_eq.trans hsent.symm,
    TR.trNsBound_of_appendsOnlyExposure hexp hns, ?_, ?_⟩,
    cHist_of_appendsOnlyExposure hexp hhist, roleSnapshots_of_appendsOnlyExposure hexp hrole⟩
  · obtain ⟨hmem, hne, hc⟩ := hrec p b hpb
    exact ⟨hmem, hne, pureCRecRelH_mono (fun _ => pureCRecRel_of_appendsOnlyExposure hexp) hc⟩
  · rw [hbd]; exact hacc1
  · rw [hbd]; exact hacc2

private def Z_any_pure : TR.PureTRSlots :=
  { canon := fun _ _ => True, recvSim := fun _ _ => True, tok := fun _ => True }

/-- Steps `Clean`, `PureCRel`, and `COpkRelC` across a `LeakableSecret` leak block. -/
theorem pureCRel_leak {interp : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {used : Bool}
    {acc evs : List MachineEvent}
    (hevs : ∀ e ∈ evs, ∃ k, LeakableSecret r records used k ∧ e = .leak k)
    (hclean : ∃ g₀ ms₀, Clean interp r S who ok g₀ ms₀ acc)
    (hrel : PureCRel interp r S who ok records sent accepted acc)
    (hopk : COpkRelC interp r S who ok used acc) :
    (∃ g₁ ms₁, Clean interp r S who ok g₁ ms₁ (acc ++ evs)) ∧
    PureCRel interp r S who ok records sent accepted (acc ++ evs) ∧
    COpkRelC interp r S who ok used (acc ++ evs) := by
  obtain ⟨g₀, ms₀, hc₀⟩ := hclean
  have hleak_kind : ∀ ev ∈ evs, eventKind ev = .leak := by
    intro ev hev; obtain ⟨_, _, rfl⟩ := hevs ev hev; rfl
  have hhead_leak : ∀ ev ∈ evs.head?, eventKind ev = .leak := by
    intro ev hev
    cases evs with
    | nil => cases hev
    | cons a l =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hev
      subst hev
      exact hleak_kind _ (List.mem_cons_self ..)
  have hsent_evs : TR.sentBodies evs = [] := by
    unfold TR.sentBodies
    refine List.filterMap_eq_nil_iff.mpr fun ev hev => ?_
    obtain ⟨_, _, rfl⟩ := hevs ev hev; rfl
  have hsent_append : TR.sentBodies (acc ++ evs) = TR.sentBodies acc := by
    rw [TR.sentBodies_append, hsent_evs, List.append_nil]
  have hnoacc_evs : ∀ ev ∈ evs, eventKind ev ≠ .accept := by
    intro ev hev; rw [hleak_kind ev hev]; decide
  have hfit_evs : TR.SendsFit evs := by
    intro b hb; obtain ⟨_, _, hsend⟩ := hevs _ hb; cases hsend
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ms₁, hc₁, _, _⟩ := leakable_leaks_step_clean hwf.1 hc₀
      (trRecordStateInv_pureStripPrev (Z := Z_any_pure) (fun _ _ => trivial) (hrel.recs hc₀))
      (leakEvs_pureStripPrev hevs)
      (fun hw hu => hopk.apply hw hu hc₀)
    exact ⟨g₀, ms₁, hc₁⟩
  · refine { oooAll := hrel.oooAll
             sendsFit := TR.sendsFit_append hrel.sendsFit hfit_evs
             bka := hrel.bka
             bkn := hrel.bkn
             clean := fun g ms hc => ?_ }
    obtain ⟨ms_pre, δ, rfl, hpre, hmatch⟩ :=
      matchedPrefix_split_all_leak hwf.1 hc.matched hhead_leak
    have hc_pre : Clean interp r S who ok g ms_pre acc :=
      clean_prefix (matchedPrefix_length_eq hpre) hc
    have hB : XplBlock interp r S who g ms_pre δ acc evs := ⟨hpre, hc.matched.2.1, hmatch⟩
    exact ⟨pureCRelAt_leak hB hleak_kind hsent_append (hrel.clean g ms_pre hc_pre).1,
      bks_leak hB hleak_kind (hrel.bks hc_pre)⟩
  · intro hw hu g ms hclo
    have hmp := hclo.matched
    obtain ⟨ms_pre, δ, rfl, hpre, hmatch⟩ :=
      matchedPrefix_split_all_leak hwf.1 hmp hhead_leak
    have hB : XplBlock interp r S who g ms_pre δ acc evs := ⟨hpre, hmp.2.1, hmatch⟩
    rw [opkUsedB_xplBlock_eq r.bob (setupPublic r 8) hB (Or.inl hnoacc_evs)]
    exact hopk hw hu g ms_pre (clean_prefix (matchedPrefix_length_eq hpre) hclo)

theorem cliLeak_step {interp : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {accepted : List HwBytes} {acc leaks : List MachineEvent}
    (hleaks : ∀ e ∈ leaks, ∃ k, KeyInDirsV1 r t k ∧ e = .leak k)
    (hclean : ∃ g₀ ms₀, Clean interp r S who ok g₀ ms₀ acc)
    (hrel : PureCRel interp r S who ok (t.leakRecords r) t.sent accepted acc)
    (hopk : COpkRelC interp r S who ok (t.opkUsed r) acc) :
    (∃ g₁ ms₁, Clean interp r S who ok g₁ ms₁ (acc ++ leaks)) ∧
    PureCRel interp r S who ok (t.leakRecords r) t.sent accepted (acc ++ leaks) ∧
    COpkRelC interp r S who ok (t.opkUsed r) (acc ++ leaks) :=
  pureCRel_leak hwf hleaks hclean hrel hopk

end Symbolic.Swarm.CREF.CliPure
