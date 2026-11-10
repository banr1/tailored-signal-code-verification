/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Tests.Nonvacuity
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Schedule Trace Primitives and Initial Handshake Steps

Defines trace-append and snapshot-currency helpers, the `AllRecvChainsHonest` invariant, generic
`messageEncrypt` trace execution (`encTrGen`), and symbolic execution of Calls `0..3` (`aliceStart`,
Alice's two initial sends, and `bobStart`) on `cleanCallSteps cls cleanSpqrIdxs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase

open DY (Bytes ExecTrace Participant Trace Traceful ExecTraceTypes TraceEntryHas)
open DY.Bytes (view?)
open DY.BytesView (pack)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Spqr (spqrInit spqrSend spqrRecv)
open DY.X25519 (normalizeX25519Key)
open DY.Libsignal.PQXDH (PreKeyMsgHandles)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain SessionInfo kdfCk createChain setRecvChain
   isCurrentSnapshot maxReceiverChains spqrA2B spqrB2A u32Max)
open DY.Libsignal.Composed (reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step stepIn setupTrace setupRandoms)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs bobSt0 bobAgreement_honest encSt encMsg encSig parse_encMsg
   ratchetState recvSt recvKey mac_ok dec_ok rnd createChain_comm
   registerIdentityTr genSignedPrekeyTr genPQPrekeyTr
   aliceTr aliceTrOpt skipTr StP StT RndE NetE EvP EvT EvC)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA o1 keys1 stA0 bh1 kh1
   t1 t2 t3 t4 t5 t1_length t2_length t3_length t4_length t5_length t5_runs t5_stA0_at)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
  (r0 r_alice_eq r_bob_eq)

/-- Canonical SPQR message header indices for `cleanCallSteps` (`2` at `bobStart`, `1` on whispers). -/
def cleanSpqrIdxs (k : Nat) : UInt32 :=
  if k = 3 then 2 else 1

/-- All timestamps `ts` whose `dhPk (rnd ts 32)` can appear as a `RecvChain.ratchetKey` in `ssClean`. -/
def ratchetKeyTimestamps : List Nat :=
  [10, 24, 45, 62, 76, 90, 104, 118, 132, 146, 160, 174, 188]

theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le t2 e)

theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace} {i : Nat} {x : E}
    (hle : t1 ≤ t2) (h : t1.at? i = some x) : t2.at? i = some x := by
  have := Trace.at?_le (EntryT := E) t1 t2 i hle
  rwa [h] at this

theorem at?_append_at {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

theorem at?_append_self_proj {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self]
  simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hi' : i < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hne : i ≠ tr.length := by omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]

theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

theorem stepIn_next (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

theorem stepIn_isSome (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (inst.pf_step x).symm

theorem setupTrace_r0_eq : setupTrace r0 = t4 :=
  Symbolic.Proofs.Tests.Nonvacuity.keySetupTrace_eq

theorem setupTrace_eq_t4 {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    setupTrace r = t4 := by
  have ha : r.alice = r0.alice := r_alice_eq hfit
  have hb : r.bob = r0.bob := r_bob_eq hfit
  have ho : r.withOpk = r0.withOpk := hfit.1.1.2.1
  unfold setupTrace
  rw [ha, hb, ho]
  exact setupTrace_r0_eq

theorem setupRandoms_len_eq {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    (setupRandoms r).length = (if r.withOpk then 7 else 6) := by
  have ho : r.withOpk = false := hfit.1.1.2.1
  unfold setupRandoms
  rw [setupTrace_eq_t4 hfit, ← setupTrace_r0_eq, ho]
  exact Symbolic.Swarm.CREF.TR.setupRandoms_length r0 (by decide)

/-- Trace produced by `TripleRatchet.messageEncrypt me stH cl pqH` from state `st` and PQ salt `pq`. -/
def encTrGen (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState) (pq : Bytes) :
    ExecTrace :=
  let m := rnd tr.length 32
  let coins := rnd (tr.length + 1) cl
  ((((((tr.append (RndE 32)).append (RndE cl)).append
    (NetE (spqrSend st.spqr coins).2.1)).append
    (EvT (.Sent me st.peer (dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

theorem encTrGen_length (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : (encTrGen tr me stH cl st pq).length = tr.length + 7 := by
  dsimp only [encTrGen]; simp only [append_len]

theorem encTrGen_le (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTrGen tr me stH cl st pq := by
  dsimp only [encTrGen]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

theorem Runs.messageEncryptGen {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} {pq : Bytes}
    (hst : tr.at? stH = some (StT me st))
    (hns : st.ns ≠ u32Max)
    (hpq : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)).at? pqH = some (NetE pq)) :
    Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pqH) tr (tr.length + 6)
      (encTrGen tr me stH cl st pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.guard _ hns) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  have hpq' :
      (((tr.append (RndE 32)).append (RndE cl)).append
        (NetE (spqrSend st.spqr
          (rnd (tr.append (RndE 32)).length cl)).2.1)).at? pqH = some (NetE pq) := by
    rw [append_len]; exact hpq
  refine Runs.bind (Runs.receiveMessage hpq') ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
  refine runs_cast (Runs.sendMessage _ _) ?_ ?_
  · simp only [NetE, EvT, StT, append_len, Nat.add_assoc]
  · simp only [encTrGen, encSt, encMsg, RndE, NetE, EvT, StT, append_len]
    dsimp only [kdfCk, spqrSend]

theorem x25519LowOrder_dhPk (sk : Bytes) :
    DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _
  have hl0 : (dhPk sk).view? DY.Literal.Literal.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
  have hl : DY.Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold DY.Libsignal.TripleRatchet.x25519LowOrder normalizeX25519Key
  rw [hv, hl]

theorem isCanonicalKey_dhPk (sk : Bytes) :
    DY.Libsignal.PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _
  have hl : DY.Libsignal.PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold DY.Libsignal.PQXDH.isCanonicalKey
  rw [hv, hl]; rfl

theorem bytesToLiteral_spqrSendMsg (st coins : Bytes) :
    DY.Literal.bytesToLiteral (spqrSend st coins).2.2 = none := by
  have hl0 : ((spqrSend st coins).2.2).view? DY.Literal.Literal.SubF = none := by
    dsimp only [spqrSend]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]

theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo)
    (pk : Bytes) (c : RecvChain) (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]

theorem skipTr_one (tr : ExecTrace) (s : SessionInfo)
    (pk : Bytes) (c : RecvChain) (src : Nat) (n : UInt32) (h1 : n.toNat - c.index.toNat = 1) :
    skipTr tr s pk c src n =
      tr.append (EvT (.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)) := by
  dsimp only [skipTr]; rw [h1]
  unfold DY.Libsignal.TripleRatchet.logSkippedKeys
  have hlog := Runs.logEvent tr
    (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)
  have hp : DY.Libsignal.TripleRatchet.logSkippedKeys s pk c.rIdx src (kdfCk c.chainKey).1
      (c.index + 1) 0 = pure () := rfl
  simp only [hp]
  exact (Runs.bind hlog (Runs.pure () _)).2

theorem isCurrentSnapshot_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]; rfl

theorem isCurrentSnapshot_non {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {k : Nat}
    (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none)
    (hcur : isCurrentSnapshot tr k = true) :
    isCurrentSnapshot (tr.append e) k = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  cases hst : (tr.at? k :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) with
  | none => rw [hst] at hcur; cases hcur
  | some es =>
    have hk : k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le
        (EntryT := DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState)) tr k
      rwa [hst] at this
    rw [hst] at hcur
    rw [at?_mono (Trace.append_le tr e) hst]
    dsimp only at hcur ⊢
    have hsub : (tr.append e).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
      rw [append_len]; omega
    rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hcur ⊢
      intro j hj
      rw [at?_append_of_lt tr e (by rw [List.mem_range'_1] at hj; omega)]
      exact hcur j hj
    · rw [at?_append_self_proj, hnone]

theorem isCurrentSnapshot_ne {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {k : Nat}
    (hst : tr.at? k = some (StT me st)) (hne : (me' != me) = true)
    (hcur : isCurrentSnapshot tr k = true) :
    isCurrentSnapshot (tr.append (StT me' st')) k = true := by
  have hk : k < tr.length := by
    have := Trace.at?_eq_some_implies_length_le
      (EntryT := DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState)) tr k
    rwa [hst] at this
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [hst] at hcur
  rw [at?_mono (Trace.append_le tr (StT me' st')) hst]
  dsimp only at hcur ⊢
  have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
    rw [append_len]; omega
  rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
    List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hcur ⊢
    intro j hj
    rw [at?_append_of_lt tr (StT me' st') (by rw [List.mem_range'_1] at hj; omega)]
    exact hcur j hj
  · rw [Trace.at?_append]; simp [hne]

/-- Every stored `TRState` on `tr` only holds receiver chains with `ratchetKey = dhPk (rnd ts 32)`
for `ts ∈ ratchetKeyTimestamps`. -/
def AllRecvChainsHonest (tr : ExecTrace) : Prop :=
  ∀ (idx : Nat) (me : Participant) (st : TRState),
    tr.at? idx = some (StT me st) →
    ∀ c ∈ st.recv, ∃ ts ∈ ratchetKeyTimestamps, c.ratchetKey = dhPk (rnd ts 32)

theorem allRecvChainsHonest_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none)
    (h : AllRecvChainsHonest tr) :
    AllRecvChainsHonest (tr.append e) := by
  intro idx me st hat
  by_cases hlt : idx < tr.length
  · rw [at?_append_of_lt tr e hlt] at hat
    exact h idx me st hat
  · by_cases heq : idx = tr.length
    · subst heq; rw [at?_append_self_proj, hnone] at hat; cases hat
    · have hge : (tr.append e).length ≤ idx := by rw [append_len]; omega
      have hlt' := Trace.at?_eq_some_implies_length_le
        (EntryT := DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState)) (tr.append e) idx
      rw [hat] at hlt'; simp at hlt'; omega

theorem allRecvChainsHonest_append_st {tr : ExecTrace} {me : Participant} {st : TRState}
    (h : AllRecvChainsHonest tr)
    (hst : ∀ c ∈ st.recv, ∃ ts ∈ ratchetKeyTimestamps, c.ratchetKey = dhPk (rnd ts 32)) :
    AllRecvChainsHonest (tr.append (StT me st)) := by
  intro idx me' st' hat
  by_cases hlt : idx < tr.length
  · rw [at?_append_of_lt tr (StT me st) hlt] at hat
    exact h idx me' st' hat
  · by_cases heq : idx = tr.length
    · subst heq
      rw [Trace.at?_append] at hat
      have h1 : StT me st = StT me' st' := Option.some.inj hat
      cases h1
      exact hst
    · have hge : (tr.append (StT me st)).length ≤ idx := by rw [append_len]; omega
      have hlt' := Trace.at?_eq_some_implies_length_le
        (EntryT := DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState)) (tr.append (StT me st)) idx
      rw [hat] at hlt'; simp at hlt'; omega

theorem allRecvChainsHonest_of_le {t1 t2 : ExecTrace} (hle : t1 ≤ t2)
    (h : AllRecvChainsHonest t2) : AllRecvChainsHonest t1 :=
  fun idx me st hat => h idx me st (at?_mono hle hat)

def pt1Clean : Bytes := rnd 31 32
def coins1Clean (cls : Nat → Nat) : Bytes := rnd 32 (cls 0)
def key1Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0.spqr (coins1Clean cls)).2.1
def pqm1Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0.spqr (coins1Clean cls)).2.2
def stA1Clean (cls : Nat → Nat) : TRState := encSt stA0 (coins1Clean cls)
def m1Clean (cls : Nat → Nat) : Bytes := encMsg stA0 (coins1Clean cls) (key1Clean cls) pt1Clean
def trClean2 (cls : Nat → Nat) : ExecTrace :=
  encTrGen t5 "alice" 30 (cls 0) stA0 (key1Clean cls)

theorem trClean2_length (cls : Nat → Nat) : (trClean2 cls).length = 38 := by
  rw [trClean2, encTrGen_length, t5_length]

def pt2Clean : Bytes := rnd 38 32
def coins2Clean (cls : Nat → Nat) : Bytes := rnd 39 (cls 1)
def key2Clean (cls : Nat → Nat) : Bytes :=
  (spqrSend (stA1Clean cls).spqr (coins2Clean cls)).2.1
def pqm2Clean (cls : Nat → Nat) : Bytes :=
  (spqrSend (stA1Clean cls).spqr (coins2Clean cls)).2.2
def stA2Clean (cls : Nat → Nat) : TRState := encSt (stA1Clean cls) (coins2Clean cls)
def m2Clean (cls : Nat → Nat) : Bytes :=
  encMsg (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean
def trClean3 (cls : Nat → Nat) : ExecTrace :=
  encTrGen (trClean2 cls) "alice" 36 (cls 1) (stA1Clean cls) (key2Clean cls)

theorem trClean3_length (cls : Nat → Nat) : (trClean3 cls).length = 45 := by
  rw [trClean3, encTrGen_length, trClean2_length]

def mhClean3 : PreKeyMsgHandles := { ek := 25, ct := 26, msg := 44 }
def dhsB0Clean : Bytes := rnd 45 32
def stB00Clean (cls : Nat → Nat) : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) keys1
    (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean)
def stB0'Clean (cls : Nat → Nat) : TRState :=
  (ratchetState (stB00Clean cls) (dhPk dhsA) dhsB0Clean).1
def cB0Clean (cls : Nat → Nat) : RecvChain :=
  (ratchetState (stB00Clean cls) (dhPk dhsA) dhsB0Clean).2
def cB0'Clean (cls : Nat → Nat) : RecvChain :=
  { cB0Clean cls with chainKey := (kdfCk (kdfCk (cB0Clean cls).chainKey).1).1, index := 2 }
def seedB0Clean (cls : Nat → Nat) : Bytes :=
  (kdfCk (kdfCk (cB0Clean cls).chainKey).1).2
def stB3Clean (cls : Nat → Nat) : TRState :=
  { stB0'Clean cls with
    recv := [cB0'Clean cls]
    spqr := recvSt (stB0'Clean cls).spqr (pqm2Clean cls) }

def bobStartSpqrKey0 : Bytes :=
  DY.Spqr.spqrChainKey keys1.pqr spqrA2B (DY.Spqr.encodeSpqrIndexTerm 2)

/-- Symbolic trace after Call 3 (`bobStart`), which logs the skipped chain key at index 0 and stores
Bob's initial `TRState`. -/
def trClean4 (cls : Nat → Nat) : ExecTrace :=
  let tr1 := ((trClean3 cls).append (RndE 32)).append (NetE bobStartSpqrKey0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0Clean)))).append
      (EvT (.HonestDH ((stB0'Clean cls).sessionInfo "bob") dhsB0Clean 0))).append
      (EvC (.HandshakeSession ((stB0'Clean cls).sessionInfo "bob") 47))
  let trS := tr5.append
    (EvT (.SkippedKeyStored ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA) 0
      (kdfCk (cB0Clean cls).chainKey).2 2 54))
  ((trS.append (EvT (.Received "bob" "alice" (dhPk dhsA) 1 pt2Clean))).append
    (EvT (.MessageKey ((stB0'Clean cls).sessionInfo "bob") .receiver
      (seedB0Clean cls) (key2Clean cls) 1 2 54))).append
    (StT "bob" (stB3Clean cls))

theorem trClean4_length (cls : Nat → Nat) : (trClean4 cls).length = 55 := by
  dsimp only [trClean4]; simp only [append_len, trClean3_length]

theorem aliceTrOpt_le (tr : ExecTrace) (a b : Participant)
    (ikA' ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    tr ≤ aliceTrOpt tr a b ikA' ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _

theorem t4_entry_facts :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) ∧
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) ∧
    AllRecvChainsHonest t4 := by
  have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have someEventB_nil : ∀ p : DY.Libsignal.PQXDH.PQXDHEvent → Bool,
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) Trace.nil p = false := fun p => by
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]; rw [nil_len]; rfl
  have someEventB_non : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
      (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool),
      (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append x) p = false := by
    intro E _ tr x p hnone h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
      exact h i hi
    · rw [at?_append_self_proj, hnone]
  have someEventB_ev : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent)
      (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool), p ev = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false →
      (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append (EvP ev)) p = false := by
    intro tr ev p hp h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
      exact h i hi
    · rw [Trace.at?_append]; exact hp
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2
  have ht2 : t2 = registerIdentityTr t1 "bob" := by
    refine (Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]; dsimp only [registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_nil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB := (Runs.genSignedPrekey hb2).2
  have h23 : t2 ≤ t3 := by
    rw [ht3]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB := (Runs.genPQPrekey (at?_mono h23 hb2)).2
  have h12 : t1 ≤ t2 := by
    rw [ht2]
    exact le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t1 _) _) _) _) _
  have h34 : t3 ≤ t4 := by
    rw [ht4]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t3 _) _) _) _) _) _
  have h24 : t2 ≤ t4 := Trace.le_trans _ _ _ h23 h34
  have h14 : t1 ≤ t4 := Trace.le_trans _ _ _ h12 h24
  have hhon_nil : AllRecvChainsHonest Trace.nil := by
    intro i _ _ h
    have hlt := Trace.at?_eq_some_implies_length_le
      (EntryT := DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState)) (Trace.nil : ExecTrace) i
    rw [h, nil_len] at hlt; simp at hlt
  have hhon1 : AllRecvChainsHonest t1 := by
    rw [ht1]; dsimp only [registerIdentityTr]
    iterate 5 refine allRecvChainsHonest_append_non _ rfl ?_
    exact hhon_nil
  have hhon2 : AllRecvChainsHonest t2 := by
    rw [ht2]; dsimp only [registerIdentityTr]
    iterate 5 refine allRecvChainsHonest_append_non _ rfl ?_
    exact hhon1
  have hhon3 : AllRecvChainsHonest t3 := by
    rw [ht3]; dsimp only [genSignedPrekeyTr]
    iterate 6 refine allRecvChainsHonest_append_non _ rfl ?_
    exact hhon2
  have hhon4 : AllRecvChainsHonest t4 := by
    rw [ht4]; dsimp only [genPQPrekeyTr]
    iterate 6 refine allRecvChainsHonest_append_non _ rfl ?_
    exact hhon3
  refine ⟨?_, at?_mono h24 hb2, ?_, ?_, hhon4⟩
  · refine at?_mono h14 ?_; rw [ht1]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))

theorem s0_next_ok :
    (Step.aliceStart "alice" "bob" 4 6 bh1).next t4 = t5 ∧
    (Step.aliceStart "alice" "bob" 4 6 bh1).ok t4 = true :=
  ⟨(stepIn_next DY.Libsignal.Composed.aliceStart.reachability _ t4).trans t5_runs.2,
   (stepIn_isSome DY.Libsignal.Composed.aliceStart.reachability _ t4).trans
     (congrArg Option.isSome t5_runs.1)⟩

theorem s1_next_ok (cls : Nat → Nat) :
    (Step.messageEncrypt "alice" 30 (cls 0) 33).next t5 = trClean2 cls ∧
    (Step.messageEncrypt "alice" 30 (cls 0) 33).ok t5 = true := by
  have hpq : (((t5.append (RndE 32)).append (RndE (cls 0))).append
      (NetE (spqrSend stA0.spqr (rnd (t5.length + 1) (cls 0))).2.1)).at? 33 =
      some (NetE (key1Clean cls)) := by
    have hc : rnd (t5.length + 1) (cls 0) = coins1Clean cls := by rw [t5_length]; rfl
    rw [hc]
    exact at?_append_at _ (NetE (key1Clean cls)) (by simp only [append_len, t5_length])
  have hr := runs_cast (Runs.messageEncryptGen (tr := t5) (stH := 30) (cl := cls 0) (pqH := 33)
    (st := stA0) (pq := key1Clean cls) t5_stA0_at (by decide) hpq) (by rw [t5_length]) rfl
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans
      (congrArg Option.isSome hr.1)⟩

theorem s2_next_ok (cls : Nat → Nat) :
    (Step.messageEncrypt "alice" 36 (cls 1) 40).next (trClean2 cls) = trClean3 cls ∧
    (Step.messageEncrypt "alice" 36 (cls 1) 40).ok (trClean2 cls) = true := by
  have hst : (trClean2 cls).at? 36 = some (StT "alice" (stA1Clean cls)) := by
    dsimp only [trClean2, encTrGen, stA1Clean]
    have hc : rnd (t5.length + 1) (cls 0) = coins1Clean cls := by rw [t5_length]; rfl
    rw [hc]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hpq : ((((trClean2 cls).append (RndE 32)).append (RndE (cls 1))).append
      (NetE (spqrSend (stA1Clean cls).spqr (rnd ((trClean2 cls).length + 1) (cls 1))).2.1)).at?
      40 = some (NetE (key2Clean cls)) := by
    have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
      rw [trClean2_length]; rfl
    rw [hc]
    exact at?_append_at _ (NetE (key2Clean cls)) (by simp only [append_len, trClean2_length])
  have hns : (stA1Clean cls).ns ≠ u32Max := by
    dsimp only [stA1Clean, encSt, stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
    decide
  have hr := runs_cast (Runs.messageEncryptGen (tr := trClean2 cls) (stH := 36) (cl := cls 1)
    (pqH := 40) (st := stA1Clean cls) (pq := key2Clean cls) hst hns hpq)
    (by rw [trClean2_length]) rfl
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem s3_next_ok (cls : Nat → Nat) :
    (Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)).next (trClean3 cls) =
      trClean4 cls ∧
    (Step.bobStart "bob" "alice" kh1 1 mhClean3 40 (cleanSpqrIdxs 3)).ok (trClean3 cls) = true := by
  change (Step.bobStart "bob" "alice" kh1 1 mhClean3 40 2).next (trClean3 cls) = trClean4 cls ∧
    (Step.bobStart "bob" "alice" kh1 1 mhClean3 40 2).ok (trClean3 cls) = true
  obtain ⟨ha1, hb9, hs13, hp19, _⟩ := t4_entry_facts
  have h53 : t5 ≤ trClean3 cls :=
    Trace.le_trans _ _ _ (encTrGen_le _ _ _ _ _ _) (encTrGen_le _ _ _ _ _ _)
  have h43 : t4 ≤ trClean3 cls := Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) h53
  have hek : (trClean3 cls).at? 25 = some (NetE o1.ek) := by
    refine at?_mono h53 ?_; dsimp only [t5, aliceTr, aliceTrOpt, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
    rw [t4_length]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hct : (trClean3 cls).at? 26 = some (NetE o1.ct) := by
    refine at?_mono h53 ?_; dsimp only [t5, aliceTr, aliceTrOpt, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt]
    rw [t4_length]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hmsg : (trClean3 cls).at? 44 = some (NetE (m2Clean cls)) := by
    dsimp only [trClean3, encTrGen, m2Clean]
    have hm : rnd (trClean2 cls).length 32 = pt2Clean := by rw [trClean2_length]; rfl
    have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
      rw [trClean2_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
  have hpq : (((trClean3 cls).append (RndE 32)).append
      (NetE bobStartSpqrKey0)).at? 40 =
      some (NetE (key2Clean cls)) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [trClean3, encTrGen]
    have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
      rw [trClean2_length]; rfl
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE (key2Clean cls)) (by simp only [append_len, trClean2_length]))
  have hrecv : spqrRecv (stB0'Clean cls).spqr (pqm2Clean cls) 2 =
      some ((stB3Clean cls).spqr, bobStartSpqrKey0) := by
    unfold spqrRecv DY.Spqr.spqrEmptyMsg pqm2Clean
    rw [bytesToLiteral_spqrSendMsg]
    have hinit : (stB0'Clean cls).spqr.view? DY.Spqr.InitState.SubF =
        some { authKey := keys1.pqr, params := spqrB2A } := by
      dsimp only [stB0'Clean, ratchetState, stB00Clean, bobSt0, spqrInit]
      exact DY.BytesView.view_pack _
    have hdir : DY.Spqr.spqrParamsDir? spqrB2A = some .b2a :=
      DY.Spqr.spqrParamsDir?_spqrParams .b2a
    rw [hinit]; dsimp only; rw [hdir]; rfl
  have hseed : (kdfCk (stA1Clean cls).cks).2 = seedB0Clean cls := by
    show (kdfCk (kdfCk (createChain keys1.rk (dhPk spkB) dhsA).2).1).2 =
      (kdfCk (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).1).2
    rw [createChain_comm keys1.rk dhsA spkB]
  have hset : setRecvChain (stB0'Clean cls).recv (cB0'Clean cls) = [cB0'Clean cls] := by
    simp [setRecvChain, stB0'Clean, ratchetState, cB0'Clean, cB0Clean, stB00Clean, bobSt0,
      maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1
      (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean))
      (encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean).ratchetKey
      (rnd (trClean3 cls).length 32) = (stB0'Clean cls, cB0Clean cls) := by
    rw [trClean3_length]; rfl
  have hr0 := Runs.bobStart (kh := kh1) (mh := mhClean3) (keys := keys1)
    (msg := encSig (stA1Clean cls) (coins2Clean cls) (key2Clean cls) pt2Clean) (t := m2Clean cls)
    (st' := stB0'Clean cls) (c := cB0Clean cls) (c' := cB0'Clean cls) (seed := seedB0Clean cls)
    (pq := key2Clean cls) (m := pt2Clean)
    (at?_mono h43 hb9) (at?_mono h43 hs13) (at?_mono h43 hp19) rfl (at?_mono h43 ha1) hek hct
    (isCanonicalKey_dhPk _)
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs rfl hrecv hpq
    (mac_ok hseed rfl rfl) (dec_ok hseed) (stOut := stB3Clean cls) (by rw [hset]; rfl)
  obtain ⟨hr1, hr2⟩ := hr0
  have h01 : (0 : UInt32) + 1 = 1 := rfl
  have hskip : ∀ tr5 src,
      skipTr tr5 ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA) (cB0Clean cls) src 1 =
        tr5.append (EvT (.SkippedKeyStored ((stB0'Clean cls).sessionInfo "bob") (dhPk dhsA) 0
          (kdfCk (cB0Clean cls).chainKey).2 2 src)) :=
    fun tr5 src => skipTr_one tr5 _ _ (cB0Clean cls) src 1 rfl
  have hr : Runs (DY.Libsignal.Composed.bobStart "bob" "alice" kh1 1 mhClean3 40 2)
      (trClean3 cls) 54 (trClean4 cls) := by
    refine ⟨?_, ?_⟩
    · dsimp only [encSig, stA1Clean, encSt, stA0,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt] at hr1
      rw [h01, hskip] at hr1
      convert hr1 using 2
      simp only [append_len, trClean3_length]
    · dsimp only [encSig, stA1Clean, encSt, stA0,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt] at hr2
      rw [h01, hskip] at hr2
      convert hr2 using 1
      dsimp only [trClean4]
      simp only [append_len, trClean3_length]
      rfl
  exact ⟨(stepIn_next DY.Libsignal.Composed.bobStart.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.Composed.bobStart.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
