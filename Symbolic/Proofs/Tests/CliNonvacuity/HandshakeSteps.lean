/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
public import Symbolic.Proofs.Tests.Nonvacuity
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Init.Data.Repr
import Init.Data.String.Defs
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Symbolic Steps, `GhostWF`, and `ModelRunWF` for Handshake

Constructs the 2-step prefix (`msPrefix2`) and 3-step full run (`msOf`), the pre-evaluated visible
entry lists (`visPrefix2Comp`, `visOfComp`), `mySemComp`, `GhostWF`, and `ModelRunWF`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps

set_option maxRecDepth 200000
unseal DY.Bytes

open DY
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet
  (TREvent RecvChain TRState kdfCk setRecvChain spqrB2A maxReceiverChains)
open DY.Libsignal.Composed (reachability bobStart)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost
   GhostAndSemMatchSetup Step stepIn VisEntry
   pubBytes kyberDecapsBytes clamp
   aliceVis bobVis bobOpkPk encDraws encSendEntry sessionHasDecrypted pendingPreKey lastSent stepView
   newRandoms exposures setupTrace runSteps runTrace randTerm
   GhostWF StepsWF ModelRunWF)
open DY.Libsignal.Composed.Refinement.Cli (aliceUuid bobUuid serializeAddresses)
open CryptoVerification.E2E (pqxdhSessionParams)
open Symbolic.Swarm.CREF (compSemOf b1_setupTrace_eq b1_setupRandomsAt_eq)
open Symbolic.Swarm.SHARED.SpqrBytes
  (spqrInitOf spqrChainKeyOf spqrSendStateOf spqrSendKeyOf
   spqrSendMsgOf spqrRecvStateOf spqrRecvKeyOf)
open Symbolic.Tests.Nonvacuity (honestHandshakeWithoutOpkTrace honestHandshakeWithOpkTrace)
open Symbolic.Proofs.Tests.Nonvacuity
  (keySetupTrace_eq tHandshakeNoOpk honestHandshakeWithoutOpkTrace_eq
   honestHandshakeWithOpkTrace_eq)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA o1 keys1 stA0 coins0 key0 m0 pqm0 bh1 kh1 mh1
   stB00 seedB0 seedB0_eq recv8
   oOpk stA0Opk coins0Opk key0Opk m0Opk bhOpk khOpk mhOpk
   t1 t2 t3 t4 t5 t6 t4Opk t5Opk t6Opk t7Opk wTrOpk
   t1_length t2_length t3_length t4_length t5_length t6_length
   t4Opk_length t5Opk_length t6Opk_length
   t4_reach t4Opk_reach
   t4Opk_runs t5_runs t5Opk_runs t6_runs t6Opk_runs t7Opk_runs
   t5_aliceDone_at t5_handshakeSessionA_at t5_stA0_at
   t5Opk_aliceDone_at t5Opk_handshakeSessionA_at t5Opk_stA0Opk_at)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs bobSt0 bobAgreement_honest encSig encMsg
   parse_encMsg ratchetState recvSt mac_ok dec_ok rnd
   registerIdentityTr genSignedPrekeyTr genPQPrekeyTr aliceTr aliceTrOpt encTr skipTr
   StP EvP EvT EvC RndE NetE StT)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (modelRunWF_of_append ghostWF_of_append)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp freshBytes pt0 myKyberPubBytes mkRecords mkRecords_wf
   mkRecords_opaqueBytes_6 padSendCoins padCompSemOf mySem mySem_compat)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel
  (tsM0 tsC0 cSend0 mkRecords_opaque5 mkRecords_opaque7)

/-! ## Constant-Fuel Non-Equality on `ComposedBare` -/

abbrev ComposedBare :=
  DY.ALaCarte.BareContainer (DY.ALaCarte.Representable.ctors (f := DY.BytesF))

local instance : DecidableEq (DY.ALaCarte.Representable.CtorId DY.BytesF) :=
  DY.ALaCarte.RepresentableDecidableEq.ctorid_deq (f := DY.BytesF)

local instance (id : DY.ALaCarte.Representable.CtorId DY.BytesF) :
    DecidableEq (DY.ALaCarte.Representable.ctors (f := DY.BytesF) id).Data :=
  DY.ALaCarte.RepresentableDecidableEq.ctor_data_deq (f := DY.BytesF) id

private def beqListOpt {α : Type} (eq : α → α → Option Bool) : List α → List α → Option Bool
  | [], [] => some true
  | a :: as, b :: bs =>
    match eq a b with
    | some true => beqListOpt eq as bs
    | some false => some false
    | none => none
  | _, _ => some false

private def beqBareOpt : Nat → ComposedBare → ComposedBare → Option Bool
  | 0, _, _ => none
  | fuel + 1, ⟨id1, d1, as1⟩, ⟨id2, d2, as2⟩ =>
    if hid : id1 = id2 then
      if hid ▸ d1 = d2 then beqListOpt (beqBareOpt fuel) as1.toList as2.toList
      else some false
    else some false

private theorem beqListOpt_false {α : Type} {eq : α → α → Option Bool} :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, ∀ b, eq a b = some false → a ≠ b) →
      beqListOpt eq l1 l2 = some false → l1 ≠ l2
  | [], [], _, h => nomatch h
  | [], _ :: _, _, _ => fun h => nomatch h
  | _ :: _, [], _, _ => fun h => nomatch h
  | a :: as, b :: bs, ih, h => by
    dsimp only [beqListOpt] at h
    cases heq : eq a b with
    | none => rw [heq] at h; nomatch h
    | some v =>
      cases v with
      | false =>
        intro hl; injection hl with hab _
        exact ih a List.mem_cons_self b heq hab
      | true =>
        rw [heq] at h
        intro hl; injection hl with _ htail
        exact beqListOpt_false (fun x hx y => ih x (List.mem_cons_of_mem a hx) y) h htail

private theorem beqBareOpt_false :
    ∀ (fuel : Nat) (x y : ComposedBare), beqBareOpt fuel x y = some false → x ≠ y
  | 0, _, _, h => nomatch h
  | fuel + 1, ⟨id1, d1, ⟨l1⟩⟩, ⟨id2, d2, ⟨l2⟩⟩, h => by
    dsimp only [beqBareOpt] at h
    split at h
    · next hid =>
      subst hid
      split at h
      · next hd =>
        subst hd
        intro heq; injection heq with _ _ hl; injection hl with hl'
        exact beqListOpt_false (fun a _ b => beqBareOpt_false fuel a b) h hl'
      · next hd => intro heq; cases heq; exact hd rfl
    · next hid => intro heq; cases heq; exact hid rfl

/-! ## Concrete `Step` Sequences, `Ghost`, and `GhostAndSemMatchSetup` -/

def m0Of (withOpk : Bool) : Step :=
  .aliceStart "alice" "bob" 4 6 (if withOpk then bhOpk else bh1)

def m1Of (withOpk : Bool) : Step :=
  if withOpk then .messageEncrypt "alice" 34 32 37
  else .messageEncrypt "alice" 30 32 33

def m2Of (withOpk : Bool) : Step :=
  if withOpk then .bobStart "bob" "alice" khOpk 1 mhOpk 37 1
  else .bobStart "bob" "alice" kh1 1 mh1 33 1

def msPrefix2 (withOpk : Bool) : List Step := [m0Of withOpk, m1Of withOpk]
def msOf (withOpk : Bool) : List Step := [m0Of withOpk, m1Of withOpk, m2Of withOpk]

def ghostOf (withOpk : Bool) : Ghost where
  σ := fun ts len =>
    if len == 32 then
      if ts == tsM0 withOpk then pt0
      else if ts == tsC0 withOpk then cSend0.take 32
      else freshBytes ts len
    else freshBytes ts len
  addr := fun _ => ((pqxdhSessionParams myParams).sendAddrs .A).getD []

theorem ghostOf_compat (withOpk : Bool) :
    GhostAndSemMatchSetup myInterp (mkRecords withOpk) (mySem withOpk) (ghostOf withOpk) := by
  apply mySem_compat
  rw [b1_setupRandomsAt_eq (mkRecords withOpk) (mkRecords_wf withOpk).1]
  cases withOpk <;> decide

def mySemComp (withOpk : Bool) : OpaqueSymbolSemantics where
  init := spqrInitOf myInterp
  chainKey := spqrChainKeyOf myInterp
  sendState := fun st c => spqrSendStateOf myInterp st (padSendCoins c)
  sendKey := fun st c => spqrSendKeyOf myInterp st (padSendCoins c)
  sendMsg := fun st c => spqrSendMsgOf myInterp st (padSendCoins c)
  recvState := spqrRecvStateOf myInterp
  recvKey := spqrRecvKeyOf myInterp
  kemPk := fun sk =>
    if sk = freshBytes 16 64 then myKyberPubBytes else 0xFF#8 :: sk
  kemDecap := fun _ ct => (kyberDecapsBytes myInterp (mkRecords withOpk) ct).getD []
  vk := fun sk => pubBytes myInterp (clamp sk)
  sign := fun _ _ _ => List.replicate 64 0#8

theorem mySem_eq_comp (withOpk : Bool) : mySem withOpk = mySemComp withOpk := by
  have h5 := mkRecords_opaque5 withOpk
  have h6 := mkRecords_opaqueBytes_6 withOpk
  have h7 := mkRecords_opaque7 withOpk
  cases withOpk <;>
    (unfold mySem padCompSemOf compSemOf mySemComp
     dsimp only
     congr 1
     · funext sk; rw [h6]; rfl
     · funext sk nonce msg
       rw [h5, h7]
       split <;> try rfl
       split <;> rfl)

/-! ## `runTrace` Equations, `stepView`, `ModelRunWF`, and `GhostWF` -/

private theorem stepIn_next_eq (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

private theorem stepIn_isSome_eq (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (i.pf_step x).symm

private theorem stepIn_preCond_iff (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    reachability.PreCond (stepIn c x) tr ↔ c.PreCond x tr :=
  (i.pf_pre x tr).symm.to_iff

theorem setupTrace_false_eq : setupTrace (mkRecords false) = t4 :=
  keySetupTrace_eq

theorem setupTrace_true_eq : setupTrace (mkRecords true) = t4Opk := by
  have ht4 : Symbolic.Swarm.CREF.b1_setupTr4 "alice" "bob" = t4 := by
    have h := (b1_setupTrace_eq (mkRecords false) (mkRecords_wf false).1).symm.trans setupTrace_false_eq
    simpa [mkRecords] using h
  have hlen4 : (Symbolic.Swarm.CREF.b1_setupTr4 "alice" "bob").length = 22 := by
    rw [ht4, t4_length]
  rw [b1_setupTrace_eq (mkRecords true) (mkRecords_wf true).1]
  dsimp only [mkRecords, ↓reduceIte]
  rw [← t4Opk_runs.2, ← ht4]
  unfold DY.Libsignal.PQXDH.genOneTimePrekey Symbolic.Swarm.CREF.b1_setupTr5
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure, hlen4]
  rfl

private abbrev dhsB0 : Bytes := rnd 38 32
private def stB0NoOpk' : TRState := (ratchetState stB00 (dhPk dhsA) dhsB0).1
private def cBNoOpk : RecvChain := (ratchetState stB00 (dhPk dhsA) dhsB0).2
private def cBNoOpk' : RecvChain :=
  { cBNoOpk with chainKey := (kdfCk cBNoOpk.chainKey).1, index := 1 }
private def stB1NoOpk : TRState :=
  { stB0NoOpk' with
      recv := [cBNoOpk']
      spqr := recvSt (DY.Spqr.spqrInit keys1.pqr spqrB2A) pqm0 }

private theorem tHandshakeNoOpk_bobStart_runs :
    Runs (bobStart "bob" "alice" kh1 1 mh1 33 1) t6 46 tHandshakeNoOpk := by
  have hset : setRecvChain stB0NoOpk'.recv cBNoOpk' = [cBNoOpk'] := by
    simp [setRecvChain, stB0NoOpk', ratchetState, cBNoOpk', cBNoOpk, stB00, bobSt0,
      maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA0 coins0 key0 m0))
      (encSig stA0 coins0 key0 m0).ratchetKey (rnd t6.length 32) =
      (stB0NoOpk', cBNoOpk) := by rw [t6_length]; rfl
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
      (hi : i = tr.length), ((tr.append e).at? i : Option E) = some e := by
    intro E _ tr e i hi; subst hi; exact DY.Trace.at?_append tr e
  have hle_of_runs : ∀ {α : Type} {x : Traceful α} {tr tr' : ExecTrace} {a : α},
      Runs x tr a tr' → tr ≤ tr' :=
    fun {_} {x} {tr} {_} {_} h => h.2 ▸ (x.run tr).2.property
  have hle45 : t4 ≤ t5 := hle_of_runs t5_runs
  have hle56 : t5 ≤ t6 := hle_of_runs t6_runs
  have hle46 : t4 ≤ t6 := DY.Trace.le_trans _ _ _ hle45 hle56
  have ht4 : t4 = Symbolic.Swarm.CREF.b1_setupTr4 "alice" "bob" := by
    have h := setupTrace_false_eq.symm.trans (b1_setupTrace_eq (mkRecords false) (mkRecords_wf false).1)
    simpa [mkRecords] using h
  have hik : t6.at? kh1.ik = some (StP "bob" { kind := .identity, sk := ikB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change t4.at? 9 = _; rw [ht4]
    unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
      Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1
    iterate 12 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hspk : t6.at? kh1.spk = some (StP "bob" { kind := .signedPrekey, sk := spkB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change t4.at? 13 = _; rw [ht4]
    unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
      Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1
    iterate 8 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hpqk : t6.at? kh1.pqspk = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change t4.at? 19 = _; rw [ht4]
    unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
      Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hreg : t6.at? 1 =
      some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    rw [ht4]
    unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
      Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1
    iterate 20 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hek : t6.at? mh1.ek = some (NetE o1.ek) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle56 ?_
    change t5.at? 25 = _; unfold t5 aliceTr aliceTrOpt; dsimp only
    iterate 5 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t4_length])
  have hct : t6.at? mh1.ct = some (NetE o1.ct) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle56 ?_
    change t5.at? 26 = _; unfold t5 aliceTr aliceTrOpt; dsimp only
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t4_length])
  have hv_var : ∀ sk : Bytes, ((dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk => by
    simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hlow_dhPk : ∀ sk : Bytes, DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false :=
    fun sk => by
      have hv_lit : ((dhPk sk).view? DY.Literal.Literal.SubF) = none := by
        simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
        exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
          ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
      simp only [DY.Libsignal.TripleRatchet.x25519LowOrder, DY.X25519.normalizeX25519Key,
        hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hcan : DY.Libsignal.PQXDH.isCanonicalKey o1.ek = true := by
    simp only [DY.Libsignal.PQXDH.isCanonicalKey, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt, hv_var]
    change (Option.isNone none && !DY.Libsignal.TripleRatchet.x25519LowOrder
      (dhPk (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd t4.length 32))) = true
    rw [hlow_dhPk]
    rfl
  have hmsg : t6.at? mh1.msg = some (NetE (encMsg stA0 coins0 key0 m0)) := by
    change t6.at? 37 = _; unfold t6 encTr; dsimp only; rw [t5_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5_length])
  have hpq : ((t6.append (RndE 32)).append (NetE key0)).at? 33 = some (NetE key0) := by
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    unfold t6 encTr; dsimp only; rw [t5_length]
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5_length])
  have hbs := Runs.bobStart (keys := keys1)
    (msg := encSig stA0 coins0 key0 m0)
    (t := encMsg stA0 coins0 key0 m0)
    (st' := stB0NoOpk') (c := cBNoOpk) (c' := cBNoOpk') (seed := seedB0)
    (pq := key0) (m := m0)
    hik hspk hpqk rfl hreg hek hct hcan
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (hlow_dhPk dhsA) hrs rfl recv8 hpq (mac_ok seedB0_eq rfl rfl)
    (dec_ok seedB0_eq) (stOut := stB1NoOpk) (by rw [hset]; rfl)
  dsimp -failIfUnchanged only [Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOutOpt] at hbs
  have htr1_len : ((t6.append (RndE 32)).append (NetE key0)).length = 40 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      t6_length]
  rw [htr1_len] at hbs
  have hskip : ∀ (tr : ExecTrace) (n : Nat),
      skipTr tr (stB0NoOpk'.sessionInfo "bob")
        (encSig stA0 coins0 key0 m0).ratchetKey
        cBNoOpk n
        (encSig stA0 coins0 key0 m0).counter = tr :=
    fun tr _ => by
      change ((Pure.pure () : Traceful Unit).run tr).2.val = tr
      rw [DY.Traceful.run_pure]
  rw [hskip] at hbs
  let tr5 := (((((t6.append (RndE 32)).append (NetE key0)).append
    (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0)))).append
      (EvT (.HonestDH (stB0NoOpk'.sessionInfo "bob") dhsB0 0))).append
      (EvC (.HandshakeSession (stB0NoOpk'.sessionInfo "bob") 40))
  have htr5_len : tr5.length = 44 := by
    simp [tr5, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      t6_length]
  change Runs (bobStart "bob" "alice" kh1 1 mh1 33 1) t6 (tr5.length + 2)
    (((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
      (EvT (.MessageKey (stB0NoOpk'.sessionInfo "bob") .receiver seedB0 key0 0 2
        (tr5.length + 0 + 2)))).append
      (StT "bob" stB1NoOpk)) at hbs
  rw [htr5_len] at hbs
  exact hbs

theorem m0_next_false : (m0Of false).next t4 = t5 := by
  change ((reachability.step (stepIn DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, bh1))).2.run t4).2.val = t5
  exact (stepIn_next_eq _ _ _).trans t5_runs.2

theorem m0_next_true : (m0Of true).next t4Opk = t5Opk := by
  change ((reachability.step (stepIn DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, bhOpk))).2.run t4Opk).2.val = t5Opk
  exact (stepIn_next_eq _ _ _).trans t5Opk_runs.2

theorem m1_next_false : (m1Of false).next t5 = t6 := by
  unfold Step.next; dsimp only [m1Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
  exact (stepIn_next_eq _ _ _).trans t6_runs.2

theorem m1_next_true : (m1Of true).next t5Opk = t6Opk := by
  unfold Step.next; dsimp only [m1Of, ↓reduceIte, Step.toInput]
  exact (stepIn_next_eq _ _ _).trans t6Opk_runs.2

theorem m2_next_false : (m2Of false).next t6 = tHandshakeNoOpk := by
  unfold Step.next; dsimp only [m2Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
  exact (stepIn_next_eq _ _ _).trans tHandshakeNoOpk_bobStart_runs.2

theorem m2_next_true : (m2Of true).next t6Opk = t7Opk := by
  unfold Step.next; dsimp only [m2Of, ↓reduceIte, Step.toInput]
  exact (stepIn_next_eq _ _ _).trans t7Opk_runs.2

theorem m0_ok_false : (m0Of false).ok t4 = true := by
  change ((reachability.step (stepIn DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, bh1))).2.run t4).1.isSome = true
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome t5_runs.1)

theorem m0_ok_true : (m0Of true).ok t4Opk = true := by
  change ((reachability.step (stepIn DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, bhOpk))).2.run t4Opk).1.isSome = true
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome t5Opk_runs.1)

theorem m1_ok_false : (m1Of false).ok t5 = true := by
  unfold Step.ok; dsimp only [m1Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome t6_runs.1)

theorem m1_ok_true : (m1Of true).ok t5Opk = true := by
  unfold Step.ok; dsimp only [m1Of, ↓reduceIte, Step.toInput]
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome t6Opk_runs.1)

theorem m2_ok_false : (m2Of false).ok t6 = true := by
  unfold Step.ok; dsimp only [m2Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome tHandshakeNoOpk_bobStart_runs.1)

theorem m2_ok_true : (m2Of true).ok t6Opk = true := by
  unfold Step.ok; dsimp only [m2Of, ↓reduceIte, Step.toInput]
  exact (stepIn_isSome_eq _ _ _).trans (congrArg Option.isSome t7Opk_runs.1)

private theorem runTrace_eq (r : ProtocolSetup) (ss : List Step) :
    runTrace r ss = runSteps ss (setupTrace r) := rfl

theorem runTrace_ms1_false : runTrace (mkRecords false) [m0Of false] = t5 := by
  rw [runTrace_eq, setupTrace_false_eq]
  dsimp only [runSteps]
  exact m0_next_false

theorem runTrace_ms1_true : runTrace (mkRecords true) [m0Of true] = t5Opk := by
  rw [runTrace_eq, setupTrace_true_eq]
  dsimp only [runSteps]
  exact m0_next_true

theorem runTrace_msPrefix2_false : runTrace (mkRecords false) (msPrefix2 false) = t6 := by
  rw [runTrace_eq, setupTrace_false_eq]
  dsimp only [msPrefix2, runSteps]
  rw [m0_next_false, m1_next_false]

theorem runTrace_msPrefix2_true : runTrace (mkRecords true) (msPrefix2 true) = t6Opk := by
  rw [runTrace_eq, setupTrace_true_eq]
  dsimp only [msPrefix2, runSteps]
  rw [m0_next_true, m1_next_true]

theorem runTrace_msOf_false :
    runTrace (mkRecords false) (msOf false) = honestHandshakeWithoutOpkTrace := by
  rw [honestHandshakeWithoutOpkTrace_eq, runTrace_eq, setupTrace_false_eq]
  dsimp only [msOf, runSteps]
  rw [m0_next_false, m1_next_false, m2_next_false]

theorem runTrace_msOf_true :
    runTrace (mkRecords true) (msOf true) = honestHandshakeWithOpkTrace := by
  rw [honestHandshakeWithOpkTrace_eq, wTrOpk, runTrace_eq, setupTrace_true_eq]
  dsimp only [msOf, runSteps]
  rw [m0_next_true, m1_next_true, m2_next_true]

def visStep (s : Step) (tr tr' : ExecTrace) (wrapped : Bool) : List VisEntry :=
  (match s with
    | .aliceStart _ _ _ _ h => aliceVis tr tr' h
    | .bobStart b _ kh _ mh _ _ => bobVis tr tr' mh (bobOpkPk b kh tr)
    | .messageEncrypt _ stateIdx .. =>
      encDraws (newRandoms tr tr') ++ encSendEntry tr tr' stateIdx wrapped
    | _ => []) ++
  exposures tr tr'

def visEncStep (tr tr' : ExecTrace) (ek ct : DY.Bytes) : List VisEntry :=
  (encDraws (newRandoms tr tr') ++
    match lastSent tr tr' with
    | some w => [⟨.send, [ek, ct, w], .preKeySend, none⟩]
    | none => []) ++
  exposures tr tr'

private theorem findSome?_append_cons {α β : Type} (f : α → Option β) :
    ∀ (l1 : List α) (x : α) (l2 : List α) (v : β),
      (∀ a ∈ l1, f a = none) → f x = some v → (l1 ++ x :: l2).findSome? f = some v
  | [], _, _, _, _, hx => by simp [hx]
  | a :: l1, x, l2, v, h1, hx => by
    have ha : f a = none := h1 a (.head _)
    simp [ha, findSome?_append_cons f l1 x l2 v (fun b hb => h1 b (.tail _ hb)) hx]

private theorem sessionHasDecrypted_eq_false_of_noReceiverKey
    {tr : ExecTrace} {s : DY.Libsignal.TripleRatchet.SessionInfo} {stateIdx : Nat}
    (hno : ∀ s' mk pq n rIdx cIdx,
      ¬ tr.EventLogged (TREvent.MessageKey s' .receiver mk pq n rIdx cIdx)) :
    sessionHasDecrypted tr s stateIdx = false := by
  unfold sessionHasDecrypted
  rw [List.any_eq_false]
  intro j _
  split
  · next s' mk pq n rIdx cIdx hget =>
    exfalso
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    rcases hat : (tr.at? j : Option (ProtocolEvent.ExecEntryT TREvent)) with _ | e
    · simp [hat] at hget
    · rcases e with ⟨tev'⟩
      simp only [hat, Option.some.injEq] at hget
      subst hget
      exact hno s' mk pq n rIdx cIdx
        ⟨j, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ j tr).mpr hat⟩
  · simp

private theorem pendingPreKey_of_at {tr : ExecTrace} {stateIdx hsIdx pqIdx : Nat}
    {rest : List Nat} {p : Participant} {st : TRState}
    {a b : Participant} {ikA' ikB' spkB' pqkB' ek ct : DY.Bytes}
    {opk' : Option DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    (hat : (tr.at? stateIdx : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState TRState))) = some ⟨{ participant := p, state := st }⟩)
    (hnodec : sessionHasDecrypted tr (st.sessionInfo p) stateIdx = false)
    (hrange : List.range tr.length = List.range hsIdx ++ hsIdx :: rest)
    (hnone : ((List.range hsIdx).all fun i =>
      (tr.getEventAt DY.Libsignal.Composed.ComposedEvent i).isNone) = true)
    (hhs : tr.getEventAt DY.Libsignal.Composed.ComposedEvent hsIdx =
      some (.HandshakeSession (st.sessionInfo p) pqIdx))
    (had : tr.getEventAt PQXDHEvent pqIdx =
      some (.AliceDone a b ikA' ikB' spkB' pqkB' opk' ek ct keys)) :
    pendingPreKey tr stateIdx = some (ek, ct) := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents
  rw [hat, Option.map_some]
  dsimp only
  simp only [hnodec, Bool.false_eq_true, ↓reduceIte, hrange, List.filterMap_append,
    List.filterMap_cons]
  rw [List.filterMap_eq_nil_iff.mpr fun i hi => by
    have his := (List.all_eq_true.mp hnone) i hi
    cases hget : tr.getEventAt DY.Libsignal.Composed.ComposedEvent i with
    | none => rfl
    | some _ => rw [hget] at his; cases his]
  rw [List.nil_append, hhs]
  simp only [↓reduceIte, had, List.findSome?_cons]

private theorem noReceiverKey_aliceTrOpt {tr : ExecTrace}
    {a b : Participant} {ikA' ikBPk spkPk pqPk : DY.Bytes} {opkPk : Option DY.Bytes}
    (hno : ∀ s' mk pq n rIdx cIdx,
      ¬ tr.EventLogged (TREvent.MessageKey s' .receiver mk pq n rIdx cIdx)) :
    ∀ s' mk pq n rIdx cIdx,
      ¬ (aliceTrOpt tr a b ikA' ikBPk spkPk pqPk opkPk).EventLogged
        (TREvent.MessageKey s' .receiver mk pq n rIdx cIdx) := by
  intro s' mk pq n rIdx cIdx hev
  have hpeelT : ∀ {E : Type} [ExecTraceTypes.Has E] {tr' : ExecTrace} {e : E} {tev : TREvent},
      (tr'.append e).EventLogged tev →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT TREvent)) = none →
      tr'.EventLogged tev :=
    fun h hnone => (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_other_iff hnone).mp h
  unfold aliceTrOpt at hev
  dsimp only at hev
  replace hev := hpeelT hev rfl
  replace hev := hpeelT hev rfl
  rcases (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_same_iff.mp hev) with hev | hbad
  · iterate 6 replace hev := hpeelT hev rfl
    exact hno s' mk pq n rIdx cIdx hev
  · cases hbad

private theorem pendingPreKey_t5 : pendingPreKey t5 30 = some (o1.ek, o1.ct) := by
  have hnil : ∀ cev : DY.Libsignal.Composed.ComposedEvent, ¬ (Trace.nil : ExecTrace).EventLogged cev := by
    rintro _ ⟨_, h⟩
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
      {cev : DY.Libsignal.Composed.ComposedEvent},
      (tr.append e).EventLogged cev →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)) = none →
      tr.EventLogged cev :=
    fun h hnone => (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_other_iff hnone).mp h
  have ht4 : t4 = Symbolic.Swarm.CREF.b1_setupTr4 "alice" "bob" := by
    have h := setupTrace_false_eq.symm.trans (b1_setupTrace_eq (mkRecords false) (mkRecords_wf false).1)
    simpa [mkRecords] using h
  have hhs_get : t5.getEventAt DY.Libsignal.Composed.ComposedEvent 29 =
      some (.HandshakeSession (stA0.sessionInfo "alice") 27) := by
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp t5_handshakeSessionA_at]
  have had_get : t5.getEventAt PQXDHEvent 27 =
      some (.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) := by
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp t5_aliceDone_at]
  have hnodec : sessionHasDecrypted t5 (stA0.sessionInfo "alice") 30 = false := by
    apply sessionHasDecrypted_eq_false_of_noReceiverKey
    apply noReceiverKey_aliceTrOpt
    intro s' mk pq n rIdx cIdx hev
    have hpeelT : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E} {tev : TREvent},
        (tr.append e).EventLogged tev →
        (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (ProtocolEvent.ExecEntryT TREvent)) = none →
        tr.EventLogged tev :=
      fun h hnone => (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_other_iff hnone).mp h
    rw [ht4] at hev
    unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
      Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1 at hev
    repeat replace hev := hpeelT hev rfl
    rcases hev with ⟨_, h⟩
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  refine pendingPreKey_of_at (hsIdx := 29) (pqIdx := 27) (rest := [30])
    t5_stA0_at hnodec (by rw [t5_length]; rfl) ?_ hhs_get had_get
  rw [List.all_eq_true]
  intro i hi
  have hi29 : i < 29 := List.mem_range.mp hi
  cases hget : t5.getEventAt DY.Libsignal.Composed.ComposedEvent i with
  | none => rfl
  | some cev =>
    exfalso
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    rcases hat : (t5.at? i :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)) with _ | e
    · simp [hat] at hget
    · rcases e with ⟨cev'⟩
      simp only [hat, Option.some.injEq] at hget
      subst hget
      unfold t5 aliceTr aliceTrOpt at hat
      dsimp only at hat
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]; omega),
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]; omega)] at hat
      have hev : DY.Trace.EventLogged cev' _ :=
        ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 cev' i _).mpr hat⟩
      rw [ht4] at hev
      unfold Symbolic.Swarm.CREF.b1_setupTr4 Symbolic.Swarm.CREF.b1_setupTr3
        Symbolic.Swarm.CREF.b1_setupTr2 Symbolic.Swarm.CREF.b1_setupTr1 at hev
      iterate 29 replace hev := hpeel hev rfl
      exact hnil cev' hev

private theorem pendingPreKey_t5Opk : pendingPreKey t5Opk 34 = some (oOpk.ek, oOpk.ct) := by
  have hnil : ∀ cev : DY.Libsignal.Composed.ComposedEvent, ¬ (Trace.nil : ExecTrace).EventLogged cev := by
    rintro _ ⟨_, h⟩
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
      {cev : DY.Libsignal.Composed.ComposedEvent},
      (tr.append e).EventLogged cev →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)) = none →
      tr.EventLogged cev :=
    fun h hnone => (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_other_iff hnone).mp h
  have ht4Opk : t4Opk = Symbolic.Swarm.CREF.b1_setupTr5 "alice" "bob" := by
    have h := setupTrace_true_eq.symm.trans (b1_setupTrace_eq (mkRecords true) (mkRecords_wf true).1)
    simpa [mkRecords] using h
  have hhs_get : t5Opk.getEventAt DY.Libsignal.Composed.ComposedEvent 33 =
      some (.HandshakeSession (stA0Opk.sessionInfo "alice") 31) := by
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp t5Opk_handshakeSessionA_at]
  have had_get : t5Opk.getEventAt PQXDHEvent 31 =
      some (.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk Symbolic.Proofs.Tests.Shared.Composed.HonestSession.opkB))
        oOpk.ek oOpk.ct Symbolic.Proofs.Tests.Shared.Composed.HonestSession.keysOpk) := by
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp t5Opk_aliceDone_at]
  have hnodec : sessionHasDecrypted t5Opk (stA0Opk.sessionInfo "alice") 34 = false := by
    apply sessionHasDecrypted_eq_false_of_noReceiverKey
    apply noReceiverKey_aliceTrOpt
    intro s' mk pq n rIdx cIdx hev
    have hpeelT : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E} {tev : TREvent},
        (tr.append e).EventLogged tev →
        (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (ProtocolEvent.ExecEntryT TREvent)) = none →
        tr.EventLogged tev :=
      fun h hnone => (Symbolic.Swarm.COMPOSED.CompTrace.eventLogged_append_other_iff hnone).mp h
    rw [ht4Opk] at hev
    unfold Symbolic.Swarm.CREF.b1_setupTr5 Symbolic.Swarm.CREF.b1_setupTr4
      Symbolic.Swarm.CREF.b1_setupTr3 Symbolic.Swarm.CREF.b1_setupTr2
      Symbolic.Swarm.CREF.b1_setupTr1 at hev
    repeat replace hev := hpeelT hev rfl
    rcases hev with ⟨_, h⟩
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  refine pendingPreKey_of_at (hsIdx := 33) (pqIdx := 31) (rest := [34])
    t5Opk_stA0Opk_at hnodec (by rw [t5Opk_length]; rfl) ?_ hhs_get had_get
  rw [List.all_eq_true]
  intro i hi
  have hi33 : i < 33 := List.mem_range.mp hi
  cases hget : t5Opk.getEventAt DY.Libsignal.Composed.ComposedEvent i with
  | none => rfl
  | some cev =>
    exfalso
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    rcases hat : (t5Opk.at? i :
        Option (ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)) with _ | e
    · simp [hat] at hget
    · rcases e with ⟨cev'⟩
      simp only [hat, Option.some.injEq] at hget
      subst hget
      unfold t5Opk Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpk aliceTrOpt at hat
      dsimp only at hat
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]; omega),
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]; omega)] at hat
      have hev : DY.Trace.EventLogged cev' _ :=
        ⟨i, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 cev' i _).mpr hat⟩
      rw [ht4Opk] at hev
      unfold Symbolic.Swarm.CREF.b1_setupTr5 Symbolic.Swarm.CREF.b1_setupTr4
        Symbolic.Swarm.CREF.b1_setupTr3 Symbolic.Swarm.CREF.b1_setupTr2
        Symbolic.Swarm.CREF.b1_setupTr1 at hev
      iterate 33 replace hev := hpeel hev rfl
      exact hnil cev' hev

private theorem stepView_eq_visStep {s : Step} {tr tr' : ExecTrace} {wrapped : Bool}
    (hok : s.ok tr = true) (hnext : s.next tr = tr')
    (hs : match s with | .aliceStart .. | .bobStart .. | .messageEncrypt .. => True | _ => False) :
    stepView s tr wrapped = visStep s tr tr' wrapped := by
  unfold stepView visStep
  simp only [hok, ↓reduceIte]
  rw [hnext]
  cases s <;> try cases hs <;> rfl

theorem vis_m0_false (w : Bool) :
    stepView (m0Of false) t4 w = visStep (m0Of false) t4 t5 false :=
  stepView_eq_visStep m0_ok_false m0_next_false trivial

theorem vis_m0_true (w : Bool) :
    stepView (m0Of true) t4Opk w = visStep (m0Of true) t4Opk t5Opk false :=
  stepView_eq_visStep m0_ok_true m0_next_true trivial

theorem vis_m1_false :
    stepView (m1Of false) t5 true = visEncStep t5 t6 o1.ek o1.ct := by
  rw [stepView_eq_visStep m1_ok_false m1_next_false trivial]
  simp only [visStep, m1Of, Bool.false_eq_true, ↓reduceIte, encSendEntry, visEncStep,
    pendingPreKey_t5]
  rfl

theorem vis_m1_true :
    stepView (m1Of true) t5Opk true = visEncStep t5Opk t6Opk oOpk.ek oOpk.ct := by
  rw [stepView_eq_visStep m1_ok_true m1_next_true trivial]
  simp only [visStep, m1Of, ↓reduceIte, encSendEntry, visEncStep, pendingPreKey_t5Opk]
  rfl

theorem vis_m2_false (w : Bool) :
    stepView (m2Of false) t6 w = visStep (m2Of false) t6 tHandshakeNoOpk true :=
  stepView_eq_visStep m2_ok_false m2_next_false trivial

theorem vis_m2_true (w : Bool) :
    stepView (m2Of true) t6Opk w = visStep (m2Of true) t6Opk t7Opk true :=
  stepView_eq_visStep m2_ok_true m2_next_true trivial

def vis1Comp (withOpk : Bool) : List VisEntry :=
  if withOpk then visStep (m0Of true) t4Opk t5Opk false
  else visStep (m0Of false) t4 t5 false

def vis2Comp (withOpk : Bool) : List VisEntry :=
  if withOpk then visEncStep t5Opk t6Opk oOpk.ek oOpk.ct
  else visEncStep t5 t6 o1.ek o1.ct

def vis3Comp (withOpk : Bool) : List VisEntry :=
  if withOpk then visStep (m2Of true) t6Opk t7Opk true
  else visStep (m2Of false) t6 tHandshakeNoOpk true

def visPrefix2Comp (withOpk : Bool) : List VisEntry :=
  vis1Comp withOpk ++ vis2Comp withOpk

def visOfComp (withOpk : Bool) : List VisEntry :=
  visPrefix2Comp withOpk ++ vis3Comp withOpk

theorem modelRunWF_msOf (withOpk : Bool) : ModelRunWF (mkRecords withOpk) (msOf withOpk) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_hat_lt : ∀ {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
        (t : ExecTrace) (e : E1) {i : Nat} (hi : i < t.length),
        ((t.append e).at? i : Option E2) = (t.at? i : Option E2) := by
      intro E1 E2 _ _ t e i hi
      have hi' : i < (t.append e).length := by
        rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
      rw [← DY.Trace.at_le t (t.append e) i hi (DY.Trace.append_le t e)]
    have h_nr_nil : (newRandoms Trace.nil Trace.nil).length = 0 := by
      simp [newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
        Symbolic.DYBridge.DY.Trace.length_eq_1]
    have h_nr_rnd : ∀ (t : ExecTrace) (len : Nat),
        (newRandoms Trace.nil (t.append (RndE len))).length = (newRandoms Trace.nil t).length + 1 := by
      intro t len
      simp only [newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero]
      rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        ← Symbolic.DYBridge.DY.Trace.append_eq_1, List.range'_concat, Nat.zero_add, Nat.one_mul,
        List.filterMap_append, List.length_append]
      congr 1
      · congr 1
        refine List.filterMap_congr fun i hi => ?_
        rw [h_hat_lt t (RndE len) (by have := List.mem_range'_1.mp hi; omega)]
      · simp only [List.filterMap_cons, List.filterMap_nil, DY.Trace.at?_append, Option.map_some,
          List.length_singleton]
    have h_nr_other : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (e : E),
        (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option DY.Random.ExecEntryT) = none →
        (newRandoms Trace.nil (t.append e)).length = (newRandoms Trace.nil t).length := by
      intro E _ t e hnone
      simp only [newRandoms, DY.Libsignal.Composed.Refinement.newIndices,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero]
      rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        ← Symbolic.DYBridge.DY.Trace.append_eq_1, List.range'_concat, Nat.zero_add, Nat.one_mul,
        List.filterMap_append, List.length_append]
      have hlast : ((t.append e).at? t.length : Option DY.Random.ExecEntryT) = none := by
        have hi' : t.length < (t.append e).length := by
          rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
        simp only [DY.Trace.at?, hi', ↓reduceDIte]
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]
        exact hnone
      simp only [List.filterMap_cons, List.filterMap_nil, hlast, Option.map_none, List.length_nil,
        Nat.add_zero]
      congr 1
      refine List.filterMap_congr fun i hi => ?_
      rw [h_hat_lt t e (by have := List.mem_range'_1.mp hi; omega)]
    have h_nr_ev : ∀ t ev,
        (newRandoms Trace.nil (t.append (Symbolic.Swarm.CREF.b1_EvE ev))).length =
          (newRandoms Trace.nil t).length := fun t ev => h_nr_other t _ rfl
    have h_nr_net : ∀ t m,
        (newRandoms Trace.nil (t.append (Symbolic.Swarm.CREF.b1_NetE m))).length =
          (newRandoms Trace.nil t).length := fun t m => h_nr_other t _ rfl
    have h_nr_st : ∀ t a s,
        (newRandoms Trace.nil (t.append (Symbolic.Swarm.CREF.b1_StE a s))).length =
          (newRandoms Trace.nil t).length := fun t a s => h_nr_other t _ rfl
    unfold DY.Libsignal.Composed.Refinement.setupRandoms
    rw [List.length_map, b1_setupTrace_eq (mkRecords withOpk) (mkRecords_wf withOpk).1]
    cases withOpk <;>
      simp only [mkRecords, Bool.false_eq_true, ↓reduceIte,
        Symbolic.Swarm.CREF.b1_setupTr5, Symbolic.Swarm.CREF.b1_setupTr4,
        Symbolic.Swarm.CREF.b1_setupTr3, Symbolic.Swarm.CREF.b1_setupTr2,
        Symbolic.Swarm.CREF.b1_setupTr1, Symbolic.Swarm.CREF.b1_RndE,
        h_nr_rnd, h_nr_ev, h_nr_net, h_nr_st, h_nr_nil]
  · cases withOpk
    · rw [setupTrace_false_eq]; exact t4_reach
    · rw [setupTrace_true_eq]; exact t4Opk_reach
  · cases withOpk
    · rw [setupTrace_false_eq]
      dsimp only [msOf, StepsWF]
      refine ⟨?_, trivial, ?_⟩
      · change reachability.PreCond (stepIn DY.Libsignal.Composed.aliceStart.reachability
          ("alice", "bob", 4, 6, bh1)) t4
        exact (stepIn_preCond_iff _ _ _).mpr trivial
      · rw [m0_next_false]
        refine ⟨?_, ?_, ?_⟩
        · unfold Step.PreCond; dsimp only [m1Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
          refine (stepIn_preCond_iff _ _ _).mpr ?_
          show DY.Libsignal.TripleRatchet.isCurrentSnapshot t5 30 = true
          simp only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?, t5_stA0_at, t5_length]
          rfl
        · dsimp only [m1Of, ↓reduceIte, Bool.false_eq_true, Step.LocalOk,
            DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx]
          exact ⟨Or.inr (Or.inl rfl), Or.inl (by rw [t5_length])⟩
        · rw [m1_next_false]
          refine ⟨?_, trivial, trivial⟩
          unfold Step.PreCond; dsimp only [m2Of, ↓reduceIte, Bool.false_eq_true, Step.toInput]
          exact (stepIn_preCond_iff _ _ _).mpr trivial
    · rw [setupTrace_true_eq]
      dsimp only [msOf, StepsWF]
      refine ⟨?_, trivial, ?_⟩
      · change reachability.PreCond (stepIn DY.Libsignal.Composed.aliceStart.reachability
          ("alice", "bob", 4, 6, bhOpk)) t4Opk
        exact (stepIn_preCond_iff _ _ _).mpr trivial
      · rw [m0_next_true]
        refine ⟨?_, ?_, ?_⟩
        · unfold Step.PreCond; dsimp only [m1Of, ↓reduceIte, Step.toInput]
          refine (stepIn_preCond_iff _ _ _).mpr ?_
          show DY.Libsignal.TripleRatchet.isCurrentSnapshot t5Opk 34 = true
          simp only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?, t5Opk_stA0Opk_at, t5Opk_length]
          rfl
        · dsimp only [m1Of, ↓reduceIte, Step.LocalOk,
            DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx]
          exact ⟨Or.inr (Or.inl rfl), Or.inl (by rw [t5Opk_length])⟩
        · rw [m1_next_true]
          refine ⟨?_, trivial, trivial⟩
          unfold Step.PreCond; dsimp only [m2Of, ↓reduceIte, Step.toInput]
          exact (stepIn_preCond_iff _ _ _).mpr trivial
  · intro i j si sj p k b hij hmi hmj hli _ hlj
    rcases i with _ | _ | _ | i <;>
      simp only [msOf, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Option.some.injEq] at hmi
    · subst hmi; cases withOpk <;> cases hli
    · rcases j with _ | _ | _ | j <;> try omega
      · simp only [msOf, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmj
        subst hmj; cases withOpk <;> cases hlj
      · simp only [msOf, List.getElem?_cons_succ, List.getElem?_nil] at hmj
        cases hmj
    · subst hmi; cases withOpk <;> cases hli
    · cases hmi

theorem modelRunWF_msPrefix2 (withOpk : Bool) :
    ModelRunWF (mkRecords withOpk) (msPrefix2 withOpk) :=
  modelRunWF_of_append (b := [m2Of withOpk]) (modelRunWF_msOf withOpk)

private def noPtRandInRngBool (withOpk : Bool) : Bool :=
  (visOfComp withOpk).all fun v =>
    !(v.kind == .rng) ||
      v.terms.all fun t =>
        beqBareOpt 4 t.val (randTerm (tsM0 withOpk) 32).val == some false

private theorem ghostWF_msOf_rng (withOpk : Bool) :
    ∀ v ∈ visOfComp withOpk, v.kind = .rng →
      ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → ((ghostOf withOpk).σ ts n).length = n := by
  intro v hv hvk ts n _ hmem
  have hexp_not_rng : ∀ (tr tr' : ExecTrace) {w : VisEntry}, w ∈ exposures tr tr' → w.kind ≠ .rng := by
    intro tr tr' w hw hwk
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
      unfold DY.Libsignal.Composed.Refinement.pqExposureAt at hj
      split at hj <;> simp at hj <;> subst hj <;> cases hwk
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
      unfold DY.Libsignal.Composed.Refinement.trExposureAt at hj
      split at hj <;> simp at hj <;> subst hj <;> cases hwk
  have hmem_nr : ∀ {tr tr' : ExecTrace} {t : DY.Bytes},
      t ∈ (newRandoms tr tr').map (·.1) →
      ∃ i, tr.length ≤ i ∧ i < tr.length + (tr'.length - tr.length) ∧ ∃ l, t = randTerm i l := by
    intro tr tr' t ht
    obtain ⟨⟨t', l⟩, hr, rfl⟩ := List.mem_map.mp ht
    obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hr
    obtain ⟨e, _, heq⟩ := Option.map_eq_some_iff.mp hmap
    injection heq with ht' hl'
    have ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
    exact ⟨i, hlo, hhi, e.length, ht'.symm⟩
  have halice_mem : ∀ (done : Option Nat) (xs : List DY.Bytes) {w : VisEntry} {t : DY.Bytes},
      w ∈ DY.Libsignal.Composed.Refinement.aliceDraws done xs → t ∈ w.terms → t ∈ xs := by
    intro done xs w t hw ht
    rcases xs with _ | ⟨ek, _ | ⟨entropy, rest⟩⟩
    · cases hw
    · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_singleton] at hw
      subst hw
      simpa [DY.Libsignal.Composed.Refinement.rngEntry] using ht
    · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_cons, List.mem_append,
        List.mem_map] at hw
      rcases hw with (rfl | hcoin) | ⟨dhs, hdhs, rfl⟩
      · have ht' : t = ek := by simpa [DY.Libsignal.Composed.Refinement.rngEntry] using ht
        subst ht'
        exact List.mem_cons_self
      · unfold DY.Libsignal.Composed.Refinement.kyberCoinEntries at hcoin
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hcoin
        have ht' : t = entropy := by simpa using ht
        subst ht'
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · have ht' : t = dhs := by simpa [DY.Libsignal.Composed.Refinement.rngEntry] using ht
        subst ht'
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hdhs))
  have ht_ne : randTerm ts n ≠ randTerm (tsM0 withOpk) 32 := by
    intro heq
    obtain ⟨hts, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj heq
    unfold visOfComp visPrefix2Comp at hv
    rcases List.mem_append.mp hv with hv12 | hv3
    · rcases List.mem_append.mp hv12 with hv1 | hv2
      · cases withOpk
        · simp only [vis1Comp, Bool.false_eq_true, ↓reduceIte, visStep, m0Of,
            List.mem_append] at hv1
          rcases hv1 with hv_a | hv_e
          · simp only [aliceVis, List.mem_cons] at hv_a
            rcases hv_a with rfl | hv_d
            · cases hvk
            · obtain ⟨i, _, hhi, l, hi_eq⟩ := hmem_nr (halice_mem _ _ hv_d hmem)
              obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hi_eq
              rw [t4_length, t5_length] at hhi
              simp only [tsM0, Bool.false_eq_true, ↓reduceIte] at hts
              omega
          · exact hexp_not_rng _ _ hv_e hvk
        · simp only [vis1Comp, ↓reduceIte, visStep, m0Of, List.mem_append] at hv1
          rcases hv1 with hv_a | hv_e
          · simp only [aliceVis, List.mem_cons] at hv_a
            rcases hv_a with rfl | hv_d
            · cases hvk
            · obtain ⟨i, _, hhi, l, hi_eq⟩ := hmem_nr (halice_mem _ _ hv_d hmem)
              obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hi_eq
              rw [t4Opk_length, t5Opk_length] at hhi
              simp only [tsM0, ↓reduceIte] at hts
              omega
          · exact hexp_not_rng _ _ hv_e hvk
      · cases withOpk
        · simp only [vis2Comp, Bool.false_eq_true, ↓reduceIte, visEncStep,
            List.mem_append] at hv2
          rcases hv2 with (hv_enc | hv_ls) | hv_e
          · have hat31 : (t6.at? 31 : Option DY.Random.ExecEntryT) = some (RndE 32) := by
              unfold t6 encTr; dsimp only
              iterate 6 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
              rw [← t5_length]; exact DY.Trace.at?_append t5 (RndE 32)
            have hnr : newRandoms t5 t6 = (randTerm 31 32, 32) ::
                (List.range' 32 6).filterMap (fun i =>
                  (t6.at? i : Option DY.Random.ExecEntryT).map fun e => (randTerm i e.length, e.length)) := by
              unfold newRandoms DY.Libsignal.Composed.Refinement.newIndices
              rw [t5_length, t6_length]
              show ((31 :: List.range' 32 6).filterMap _) = _
              simp only [List.filterMap_cons, hat31, Option.map_some]
            rw [hnr] at hv_enc
            simp only [encDraws, List.mem_cons, List.mem_map, List.mem_filter,
              List.mem_filterMap] at hv_enc
            rcases hv_enc with rfl | ⟨⟨t', l'⟩, ⟨⟨i, hi, hmap⟩, _⟩, rfl⟩
            · cases hvk
            · obtain ⟨e, _, heq'⟩ := Option.map_eq_some_iff.mp hmap
              injection heq' with ht' _
              have ht_eq : randTerm ts n = t' := by
                simpa [DY.Libsignal.Composed.Refinement.rngEntry] using hmem
              obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (ht_eq.trans ht'.symm)
              have ⟨hlo, _⟩ := List.mem_range'_1.mp hi
              simp only [tsM0, Bool.false_eq_true, ↓reduceIte] at hts
              omega
          · (split at hv_ls <;> simp at hv_ls); subst hv_ls; cases hvk
          · exact hexp_not_rng _ _ hv_e hvk
        · simp only [vis2Comp, ↓reduceIte, visEncStep, List.mem_append] at hv2
          rcases hv2 with (hv_enc | hv_ls) | hv_e
          · have hat35 : (t6Opk.at? 35 : Option DY.Random.ExecEntryT) = some (RndE 32) := by
              unfold t6Opk encTr; dsimp only
              iterate 6 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
              rw [← t5Opk_length]; exact DY.Trace.at?_append t5Opk (RndE 32)
            have hnr : newRandoms t5Opk t6Opk = (randTerm 35 32, 32) ::
                (List.range' 36 6).filterMap (fun i =>
                  (t6Opk.at? i : Option DY.Random.ExecEntryT).map fun e => (randTerm i e.length, e.length)) := by
              unfold newRandoms DY.Libsignal.Composed.Refinement.newIndices
              rw [t5Opk_length, t6Opk_length]
              show ((35 :: List.range' 36 6).filterMap _) = _
              simp only [List.filterMap_cons, hat35, Option.map_some]
            rw [hnr] at hv_enc
            simp only [encDraws, List.mem_cons, List.mem_map, List.mem_filter,
              List.mem_filterMap] at hv_enc
            rcases hv_enc with rfl | ⟨⟨t', l'⟩, ⟨⟨i, hi, hmap⟩, _⟩, rfl⟩
            · cases hvk
            · obtain ⟨e, _, heq'⟩ := Option.map_eq_some_iff.mp hmap
              injection heq' with ht' _
              have ht_eq : randTerm ts n = t' := by
                simpa [DY.Libsignal.Composed.Refinement.rngEntry] using hmem
              obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (ht_eq.trans ht'.symm)
              have ⟨hlo, _⟩ := List.mem_range'_1.mp hi
              simp only [tsM0, ↓reduceIte] at hts
              omega
          · (split at hv_ls <;> simp at hv_ls); subst hv_ls; cases hvk
          · exact hexp_not_rng _ _ hv_e hvk
    · cases withOpk
      · simp only [vis3Comp, Bool.false_eq_true, ↓reduceIte, visStep, m2Of,
          List.mem_append] at hv3
        rcases hv3 with hv_b | hv_e
        · simp only [bobVis, List.mem_cons, List.mem_append, List.mem_map] at hv_b
          rcases hv_b with (rfl | ⟨⟨t', l'⟩, hr, rfl⟩) | hv_acc
          · cases hvk
          · have ht_eq : randTerm ts n = t' := by
              simpa [DY.Libsignal.Composed.Refinement.rngEntry] using hmem
            obtain ⟨i, hlo, _, _, hi_eq⟩ := hmem_nr (List.mem_map_of_mem (f := (·.1)) hr)
            obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (ht_eq.trans hi_eq)
            rw [t6_length] at hlo
            simp only [tsM0, Bool.false_eq_true, ↓reduceIte] at hts
            omega
          · rw [Option.mem_toList] at hv_acc
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hv_acc
            cases hvk
        · exact hexp_not_rng _ _ hv_e hvk
      · simp only [vis3Comp, ↓reduceIte, visStep, m2Of, List.mem_append] at hv3
        rcases hv3 with hv_b | hv_e
        · simp only [bobVis, List.mem_cons, List.mem_append, List.mem_map] at hv_b
          rcases hv_b with (rfl | ⟨⟨t', l'⟩, hr, rfl⟩) | hv_acc
          · cases hvk
          · have ht_eq : randTerm ts n = t' := by
              simpa [DY.Libsignal.Composed.Refinement.rngEntry] using hmem
            obtain ⟨i, hlo, _, _, hi_eq⟩ := hmem_nr (List.mem_map_of_mem (f := (·.1)) hr)
            obtain ⟨rfl, _⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (ht_eq.trans hi_eq)
            rw [t6Opk_length] at hlo
            simp only [tsM0, ↓reduceIte] at hts
            omega
          · rw [Option.mem_toList] at hv_acc
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hv_acc
            cases hvk
        · exact hexp_not_rng _ _ hv_e hvk
  unfold ghostOf
  dsimp only
  by_cases hn32 : (n == 32) = true
  · simp only [hn32, ↓reduceIte]
    have hn : n = 32 := beq_iff_eq.mp hn32
    subst hn
    by_cases htsM : (ts == tsM0 withOpk) = true
    · exact absurd (congrArg (randTerm · 32) (beq_iff_eq.mp htsM)) ht_ne
    · simp only [htsM, Bool.false_eq_true, ↓reduceIte]
      by_cases htsC : (ts == tsC0 withOpk) = true
      · simp only [htsC, ↓reduceIte]; decide
      · simp only [htsC, Bool.false_eq_true, ↓reduceIte, freshBytes, List.length_replicate]
  · simp only [hn32, Bool.false_eq_true, ↓reduceIte, freshBytes, List.length_replicate]

theorem ghostWF_msOf (withOpk : Bool) : GhostWF (ghostOf withOpk) (visOfComp withOpk) := by
  have haddr_eq : ((pqxdhSessionParams myParams).sendAddrs .A).getD [] =
      serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.sendAddrs_A_getD_eq_serializeAddresses myParams
  refine ⟨ghostWF_msOf_rng withOpk, fun _ => Or.inr haddr_eq, ?_⟩
  intro v hv hvk
  have hexp : ∀ (tr tr' : ExecTrace), v ∈ exposures tr tr' → False := by
    intro tr tr' hw
    rcases List.mem_append.mp hw with hw | hw <;>
      obtain ⟨_, _, hj⟩ := List.mem_filterMap.mp hw
    · unfold DY.Libsignal.Composed.Refinement.pqExposureAt at hj
      split at hj <;> simp at hj <;> subst hj <;> cases hvk
    · unfold DY.Libsignal.Composed.Refinement.trExposureAt at hj
      split at hj <;> simp at hj <;> subst hj <;> cases hvk
  have had : ∀ (tr tr' : ExecTrace) (h : DY.Libsignal.PQXDH.BundleHandles),
      v ∈ aliceVis tr tr' h ++ exposures tr tr' → False := by
    intro tr tr' h hw
    simp only [aliceVis, List.mem_append, List.mem_cons] at hw
    rcases hw with (rfl | hw) | hw
    · cases hvk
    · rcases xs_eq : (newRandoms tr tr').map (·.1) with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rw [xs_eq] at hw
      · cases hw
      · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_singleton] at hw
        subst hw; cases hvk
      · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_cons, List.mem_append,
          DY.Libsignal.Composed.Refinement.kyberCoinEntries, List.mem_map] at hw
        rcases hw with (rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> cases hvk
    · exact hexp _ _ hw
  have hed : ∀ (tr tr' : ExecTrace) (ek ct : DY.Bytes),
      v ∈ visEncStep tr tr' ek ct → v.layout = .preKeySend := by
    intro tr tr' ek ct hw
    simp only [visEncStep, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · rcases xs_eq : newRandoms tr tr' with _ | ⟨_, _⟩ <;> rw [xs_eq] at hw
      · cases hw
      · simp only [encDraws, List.mem_cons, List.mem_map] at hw
        rcases hw with rfl | ⟨_, _, rfl⟩ <;> cases hvk
    · (split at hw <;> simp at hw); subst hw; rfl
    · exact (hexp _ _ hw).elim
  have hbv : ∀ (tr tr' : ExecTrace) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (opk : Option DY.Bytes),
      v ∈ bobVis tr tr' mh opk ++ exposures tr tr' → False := by
    intro tr tr' mh opk hw
    simp only [bobVis, List.mem_append, List.mem_cons, List.mem_map, Option.mem_toList,
      Option.map_eq_some_iff] at hw
    rcases hw with ((rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | hw
    · cases hvk
    · cases hvk
    · cases hvk
    · exact hexp _ _ hw
  have hlay : v.layout = .preKeySend := by
    unfold visOfComp visPrefix2Comp at hv
    rcases List.mem_append.mp hv with hv12 | hv3
    · rcases List.mem_append.mp hv12 with hv1 | hv2
      · cases withOpk <;>
          simp only [vis1Comp, Bool.false_eq_true, ↓reduceIte, visStep, m0Of] at hv1
        · exact (had _ _ _ hv1).elim
        · exact (had _ _ _ hv1).elim
      · cases withOpk <;> simp only [vis2Comp, Bool.false_eq_true, ↓reduceIte] at hv2
        · exact hed _ _ _ _ hv2
        · exact hed _ _ _ _ hv2
    · cases withOpk <;>
        simp only [vis3Comp, Bool.false_eq_true, ↓reduceIte, visStep, m2Of] at hv3
      · exact (hbv _ _ _ _ hv3).elim
      · exact (hbv _ _ _ _ hv3).elim
  exact ⟨fun _ _ _ _ _ _ _ => haddr_eq, fun hwh => by rw [hlay] at hwh; cases hwh⟩

theorem ghostWF_msPrefix2 (withOpk : Bool) : GhostWF (ghostOf withOpk) (visPrefix2Comp withOpk) :=
  ghostWF_of_append (ghostWF_msOf withOpk)

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
