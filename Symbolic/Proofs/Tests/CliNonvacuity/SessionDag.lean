/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Actions.PersistentLocalState
import all DY.Actions.Random
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.Sign
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB

/-!
# `TRState` Proxy Roots and Computable Session Witnesses

Defines session and handshake memo extractors (`stateAnchorPair`, `trStateProxyRoots`,
`serialize_localTR_memo`, `firstTwoBytesKey`, `macTerms`), kernel-reducible setup witnesses
(`r0Comp`, `S0Comp`, `myGhostComp`), and `attackerKnows_of_getMessageSentAt`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionDag

open scoped DY.Libsignal.Composed

attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (ExecTrace Trace)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (pqxdhSessionParams)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState RecvChain TRSignalMsg trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost TrialCtx
   node clamp pubBytes kyberDecapsBytes setupPublic randTerm
   concretizeConcat concretizeAll gamma' gamma assumedInjective)
open Symbolic.Swarm.SHARED.SpqrBytes
  (spqrInitOf spqrChainKeyOf spqrSendStateOf spqrSendKeyOf spqrSendMsgOf
   spqrRecvStateOf spqrRecvKeyOf)
open Symbolic.Swarm.CREF (compSemOf b1_setupPublic_5 b1_setupPublic_6 b1_setupPublic_7)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp freshBytes myKyberPubBytes myKyberSecField
   mkRecords mkRecords_opaqueBytes_6 padSendCoins padCompSemOf mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhostSigma msg0WireTerm msg1WireTerm myGhostAddr myGhost)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (decEqBytesFast)

unseal DY.Bytes

/-! ## `TRState` Proxy Roots and Memo Extraction -/

def recvTailTerm (c : RecvChain) : DY.Bytes :=
  Comparse.concatPrefixes
    (Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
     Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx)
    Comparse.BytesLike.empty

def stateAnchorPair (ls : DY.PersistentLocalState.LocalState TRState) : DY.Bytes × DY.Bytes :=
  match ls.state.recv.getLast? with
  | none => (ls.state.spqr, Comparse.BytesLike.empty)
  | some cLast => (cLast.chainKey, recvTailTerm cLast)

def trStateProxyRoots (ls : DY.PersistentLocalState.LocalState TRState) : List DY.Bytes :=
  let st := ls.state
  let (a, s) := stateAnchorPair ls
  Comparse.NonExtensibleMessageFormat.bool.serialize true ++
  Comparse.NonExtensibleMessageFormat.bool.serialize false ++
  Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++
  Comparse.NonExtensibleMessageFormat.slowString.serialize st.peer ++
  [st.myIk, st.peerIk, st.rk, st.dhs, st.cks] ++
  Comparse.NonExtensibleMessageFormat.uint32.serialize st.ns ++
  Comparse.NonExtensibleMessageFormat.uint32.serialize st.pn ++
  [st.sid] ++
  Comparse.NonExtensibleMessageFormat.slowNat.serialize st.rIdx ++
  [st.spqr, Comparse.BytesLike.empty, a, s] ++
  st.recv.flatMap fun c =>
    [c.ratchetKey, c.chainKey] ++
    Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
    Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx

private theorem mem_slowNat_serialize :
    ∀ (n : Nat) {p : DY.Bytes},
      p ∈ (Comparse.NonExtensibleMessageFormat.slowNat.serialize n : List DY.Bytes) →
      p ∈ (Comparse.NonExtensibleMessageFormat.bool.serialize true : List DY.Bytes) ++
        Comparse.NonExtensibleMessageFormat.bool.serialize false
  | 0, _, hp => List.mem_append_right _ hp
  | n + 1, _, hp => by
    rcases List.mem_append.mp hp with h1 | h2
    · exact List.mem_append_left _ h1
    · exact mem_slowNat_serialize n h2

private theorem concat_gamma' (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) :
    gamma' i S g (DY.Concat.concat a b) =
      concretizeConcat ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes)
        (fun y _ => gamma' i S g y) :=
  DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)
    ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes)

private theorem concatPrefixes_append :
    ∀ (xs ys : List DY.Bytes) (s : DY.Bytes),
      Comparse.concatPrefixes (xs ++ ys) s = Comparse.concatPrefixes xs (Comparse.concatPrefixes ys s)
  | [], _, _ => rfl
  | x :: xs, ys, s => congrArg (DY.Concat.concat x) (concatPrefixes_append xs ys s)

private theorem memo_concatPrefixes_anchor (i : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (a s : DY.Bytes) :
    ∀ (ps : List DY.Bytes),
      let t := Comparse.concatPrefixes (ps ++ [a]) s
      (gamma i S g a ++ gamma i S g s) <:+ (gamma' i S g t).bytes ∧
      ∀ x ∈ (gamma' i S g t).memo,
        (∃ r ∈ ps ++ [a, s], x ∈ (gamma' i S g r).memo) ∨
        (assumedInjective x.1 = false ∧ (gamma i S g a ++ gamma i S g s) <:+ x.2.2)
  | [] => by
    change (gamma i S g a ++ gamma i S g s) <:+ (gamma' i S g (DY.Concat.concat a s)).bytes ∧
      ∀ x ∈ (gamma' i S g (DY.Concat.concat a s)).memo, _
    rw [concat_gamma']
    have hinj : assumedInjective (DY.Concat.concat a s) = false := rfl
    simp only [concretizeConcat, node]
    refine ⟨List.suffix_rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Or.inr ⟨hinj, List.suffix_rfl⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx'
      rcases hx' with h1 | h2
      · exact Or.inl ⟨a, by simp, h1⟩
      · exact Or.inl ⟨s, by simp, h2⟩
  | p :: ps => by
    obtain ⟨ihSuf, ihMem⟩ := memo_concatPrefixes_anchor i S g a s ps
    change (gamma i S g a ++ gamma i S g s) <:+
        (gamma' i S g (DY.Concat.concat p (Comparse.concatPrefixes (ps ++ [a]) s))).bytes ∧
      ∀ x ∈ (gamma' i S g (DY.Concat.concat p (Comparse.concatPrefixes (ps ++ [a]) s))).memo, _
    rw [concat_gamma']
    have hinj : assumedInjective (DY.Concat.concat p (Comparse.concatPrefixes (ps ++ [a]) s)) = false := rfl
    simp only [concretizeConcat, node]
    have hsuf' : (gamma i S g a ++ gamma i S g s) <:+
        (gamma' i S g p).bytes ++ (gamma' i S g (Comparse.concatPrefixes (ps ++ [a]) s)).bytes :=
      ihSuf.trans (List.suffix_append _ _)
    refine ⟨hsuf', fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Or.inr ⟨hinj, hsuf'⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx'
      rcases hx' with h1 | h2
      · exact Or.inl ⟨p, by simp, h1⟩
      · rcases ihMem x h2 with ⟨r, hr, hxr⟩ | hcat
        · exact Or.inl ⟨r, List.mem_cons_of_mem p hr, hxr⟩
        · exact Or.inr hcat

private theorem serialize_recvList_append_singleton :
    ∀ (csInit : List RecvChain) (cLast : RecvChain),
      (Comparse.ExtensibleMessageFormat.list
        (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain))).serialize (csInit ++ [cLast]) =
      Comparse.concatPrefixes
        (csInit.flatMap (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize)
        (Comparse.concatPrefixes
          ((DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize cLast)
          Comparse.BytesLike.empty)
  | [], _ => rfl
  | d :: csInit, cLast => by
    show Comparse.concatPrefixes
        ((DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize d)
        ((Comparse.ExtensibleMessageFormat.list _).serialize (csInit ++ [cLast])) = _
    rw [serialize_recvList_append_singleton csInit cLast, List.flatMap_cons, concatPrefixes_append]

private theorem slowBytes_serialize_eq (b : DY.Bytes) :
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize b =
      Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length b) ++ [b] :=
  rfl

private theorem serialize_recvChain_eq (c : RecvChain) :
    (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize c =
      (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length c.ratchetKey) ++
       [c.ratchetKey] ++
       Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length c.chainKey)) ++
      [c.chainKey] ++
      (Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
       Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx) := by
  have h0 : (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize c =
      Comparse.NonExtensibleMessageFormat.slowBytes.serialize c.ratchetKey ++
      (Comparse.NonExtensibleMessageFormat.slowBytes.serialize c.chainKey ++
      (Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
       Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx)) := rfl
  rw [h0, slowBytes_serialize_eq, slowBytes_serialize_eq]
  simp only [List.append_assoc]

theorem serialize_localTR_memo (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ls : DY.PersistentLocalState.LocalState TRState)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Comparse.serialize ls)).memo) :
    (∃ r ∈ trStateProxyRoots ls, x ∈ (gamma' i S g r).memo) ∨
      (assumedInjective x.1 = false ∧
        (gamma i S g (stateAnchorPair ls).1 ++ gamma i S g (stateAnchorPair ls).2) <:+ x.2.2) := by
  let st := ls.state
  let psBase : List DY.Bytes :=
    Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++
    Comparse.NonExtensibleMessageFormat.slowString.serialize st.peer ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.myIk ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.peerIk ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.rk ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.dhs ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.cks ++
    Comparse.NonExtensibleMessageFormat.uint32.serialize st.ns ++
    Comparse.NonExtensibleMessageFormat.uint32.serialize st.pn ++
    Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.sid ++
    Comparse.NonExtensibleMessageFormat.bool.serialize st.initiator ++
    Comparse.NonExtensibleMessageFormat.slowNat.serialize st.rIdx ++
    Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length st.spqr)
  have hsn : ∀ {r : DY.Bytes} (n : Nat),
      r ∈ (Comparse.NonExtensibleMessageFormat.slowNat.serialize n : List DY.Bytes) →
      r ∈ trStateProxyRoots ls := by
    intro r n h
    have := List.mem_append.mp (mem_slowNat_serialize n h)
    dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
  have hsb : ∀ {r b : DY.Bytes},
      r ∈ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize b : List DY.Bytes) →
      b ∈ trStateProxyRoots ls → r ∈ trStateProxyRoots ls := by
    intro r b h hb
    rw [slowBytes_serialize_eq] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact hsn _ h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hb
  have hbase_mem : ∀ {r : DY.Bytes}, r ∈ psBase → r ∈ trStateProxyRoots ls := by
    intro r hr
    dsimp only [psBase] at hr
    simp only [List.mem_append] at hr
    rcases hr with ((((((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) | h13)
    · dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
    · dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
    · exact hsb h3 (by dsimp only [trStateProxyRoots]; simp [st])
    · exact hsb h4 (by dsimp only [trStateProxyRoots]; simp [st])
    · exact hsb h5 (by dsimp only [trStateProxyRoots]; simp [st])
    · exact hsb h6 (by dsimp only [trStateProxyRoots]; simp [st])
    · exact hsb h7 (by dsimp only [trStateProxyRoots]; simp [st])
    · dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
    · dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
    · exact hsb h10 (by dsimp only [trStateProxyRoots]; simp [st])
    · cases hinit : st.initiator <;> rw [hinit] at h11 <;>
        (dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto)
    · dsimp only [trStateProxyRoots]; simp only [List.mem_append]; tauto
    · exact hsn _ h13
  have hls0 : (DY.Comparse.serialize ls : DY.Bytes) =
      Comparse.concatPrefixes
        (Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant)
        (DY.Comparse.serialize st) := rfl
  have hst0 : (DY.Comparse.serialize st : DY.Bytes) =
      Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowString.serialize st.peer)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.myIk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.peerIk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.rk)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.dhs)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.cks)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize st.ns)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize st.pn)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.sid)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize st.initiator)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize st.rIdx)
      (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize st.spqr)
      ((Comparse.ExtensibleMessageFormat.list
        (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain))).serialize st.recv)))))))))))) := rfl
  have h0 : (DY.Comparse.serialize ls : DY.Bytes) =
      Comparse.concatPrefixes (psBase ++ [st.spqr])
        ((Comparse.ExtensibleMessageFormat.list
          (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain))).serialize st.recv) := by
    rw [hls0, hst0, slowBytes_serialize_eq st.spqr]
    simp only [psBase, List.append_assoc, concatPrefixes_append]
  rcases List.eq_nil_or_concat st.recv with hnil | ⟨csInit, cLast, hcat⟩
  · have hcat' : ls.state.recv = [] := hnil
    have hanc : stateAnchorPair ls = (st.spqr, Comparse.BytesLike.empty) := by
      simp [stateAnchorPair, hcat', st]
    rw [h0, hnil] at hx
    change x ∈ (gamma' i S g (Comparse.concatPrefixes (psBase ++ [st.spqr]) Comparse.BytesLike.empty)).memo at hx
    rw [hanc]
    rcases (memo_concatPrefixes_anchor i S g st.spqr Comparse.BytesLike.empty psBase).2 x hx with
      ⟨r, hr, hxr⟩ | hspine
    · refine Or.inl ⟨r, ?_, hxr⟩
      rcases List.mem_append.mp hr with hpb | htail
      · exact hbase_mem hpb
      · dsimp only [trStateProxyRoots]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
        rcases htail with rfl | rfl <;> simp [st]
    · exact Or.inr hspine
  · have hcat' : ls.state.recv = csInit ++ [cLast] := by simpa [st] using hcat
    have hanc : stateAnchorPair ls = (cLast.chainKey, recvTailTerm cLast) := by
      simp [stateAnchorPair, hcat']
    let serC := (DY.Comparse.ParseableSerializeableNE.mf (a := RecvChain)).serialize
    let psRecv :=
      (psBase ++ [st.spqr]) ++
      csInit.flatMap serC ++
      (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length cLast.ratchetKey) ++
       [cLast.ratchetKey] ++
       Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length cLast.chainKey))
    have hser : (DY.Comparse.serialize ls : DY.Bytes) =
        Comparse.concatPrefixes (psRecv ++ [cLast.chainKey]) (recvTailTerm cLast) := by
      rw [h0, hcat', serialize_recvList_append_singleton, serialize_recvChain_eq cLast]
      simp only [psRecv, serC, recvTailTerm, List.append_assoc, concatPrefixes_append]
    rw [hser] at hx
    rw [hanc]
    rcases (memo_concatPrefixes_anchor i S g cLast.chainKey (recvTailTerm cLast) psRecv).2 x hx with
      ⟨r, hr, hxr⟩ | hspine
    · refine Or.inl ⟨r, ?_, hxr⟩
      have hcMem : ∀ {c : RecvChain}, c ∈ ls.state.recv →
          ∀ {u : DY.Bytes}, u ∈ serC c → u ∈ trStateProxyRoots ls := by
        intro c hc u hu
        dsimp only [serC] at hu
        rw [serialize_recvChain_eq] at hu
        simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with (((h1 | rfl) | h2) | rfl) | h3 | h4
        · exact hsn _ h1
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, by simp⟩)
        · exact hsn _ h2
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, by simp⟩)
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, by simp [h3]⟩)
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, by simp [h4]⟩)
      have hcLast : cLast ∈ ls.state.recv := by simp [hcat']
      rcases List.mem_append.mp hr with hr1 | hrTail
      · rcases List.mem_append.mp hr1 with hr2 | hrLast
        · rcases List.mem_append.mp hr2 with hr3 | hrInit
          · rcases List.mem_append.mp hr3 with hpb | hspqr
            · exact hbase_mem hpb
            · simp only [List.mem_singleton] at hspqr; subst hspqr
              dsimp only [trStateProxyRoots]; simp [st]
          · obtain ⟨c, hcInit, hrc⟩ := List.mem_flatMap.mp hrInit
            exact hcMem (by simp [hcat', hcInit]) hrc
        · rcases List.mem_append.mp hrLast with hrk | hsn2
          · rcases List.mem_append.mp hrk with hsn1 | hrkEq
            · exact hsn _ hsn1
            · simp only [List.mem_singleton] at hrkEq; subst hrkEq
              exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cLast, hcLast, by simp⟩)
          · exact hsn _ hsn2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTail
        rcases hrTail with rfl | rfl
        · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cLast, hcLast, by simp⟩)
        · dsimp only [trStateProxyRoots]; rw [hanc]; simp
    · exact Or.inr hspine

def firstTwoBytesKey (bs : HwBytes) : Nat :=
  match bs with
  | [] => 0
  | [b0] => b0.toNat + 1
  | b0 :: b1 :: _ => b0.toNat + b1.toNat * 17 + bs.length * 31 + 2

theorem suffix_drop_eq {α : Type} {sfx bs : List α} (h : sfx <:+ bs) :
    sfx.length ≤ bs.length ∧ bs.drop (bs.length - sfx.length) = sfx := by
  obtain ⟨l, rfl⟩ := h
  have hlen : (l ++ sfx).length - sfx.length = l.length := by simp
  exact ⟨by simp, by rw [hlen, List.drop_left]⟩

/-! ## MAC Term Helper -/

def macTerms (honest : List DY.Bytes) (msg : TRSignalMsg) (ctxs : List TrialCtx) : List DY.Bytes :=
  msg.mac :: ctxs.flatMap fun ctx =>
    match ctx.seed? with
    | none => []
    | some seed =>
      seed :: (ctx.ownSalts ++ honest).flatMap fun salt =>
        let mk := trMsgKeys salt seed
        [mk.cipherKey, mk.macKey, mk.iv, computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire]

/-! ## Kernel-Reducible Witnesses and Direct `AttackerKnows` -/

noncomputable def r0Comp : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false
    regIdA := 10#32, regIdB := 20#32, spkId := 1#32, kpkId := 2#32, opkId := 3#32
    kyberSecB := myKyberSecField, fresh := freshBytes
    opaqueBytes := fun t =>
      match decEqBytesFast t (DY.PQKem.kemPk (randTerm 16 64)) with
      | isTrue _ => myKyberPubBytes
      | isFalse _ => List.replicate 64 0#8 }

theorem r0_eq_comp : r0 = r0Comp := by
  change mkRecords false = r0Comp
  unfold mkRecords r0Comp
  dsimp only
  congr 1
  funext t
  rw [b1_setupPublic_6 _ (by show "alice" ≠ "bob"; decide)]
  cases decEqBytesFast t (DY.PQKem.kemPk (randTerm 16 64)) with
  | isTrue h => simp [h]
  | isFalse h => simp [h]

def S0Comp : OpaqueSymbolSemantics where
  init := spqrInitOf myInterp
  chainKey := spqrChainKeyOf myInterp
  sendState := fun st c => spqrSendStateOf myInterp st (padSendCoins c)
  sendKey := fun st c => spqrSendKeyOf myInterp st (padSendCoins c)
  sendMsg := fun st c => spqrSendMsgOf myInterp st (padSendCoins c)
  recvState := spqrRecvStateOf myInterp
  recvKey := spqrRecvKeyOf myInterp
  kemPk := fun sk =>
    if sk = freshBytes 16 64 then myKyberPubBytes else 0xFF#8 :: sk
  kemDecap := fun _ ct => (kyberDecapsBytes myInterp (mkRecords false) ct).getD []
  vk := fun sk => pubBytes myInterp (clamp sk)
  sign := fun _ _ _ => List.replicate 64 0#8

theorem S0_eq_comp : S0 = S0Comp := by
  have ho5 : r0Comp.opaqueBytes (setupPublic r0Comp 5) = List.replicate 64 0#8 := by
    rw [b1_setupPublic_5 r0Comp (by show "alice" ≠ "bob"; decide)]
    rfl
  have ho7 : r0Comp.opaqueBytes (setupPublic r0Comp 7) = List.replicate 64 0#8 := by
    rw [b1_setupPublic_7 r0Comp (by show "alice" ≠ "bob"; decide)]
    rfl
  have ho6 : (mkRecords false).opaqueBytes (setupPublic (mkRecords false) 6) = myKyberPubBytes :=
    mkRecords_opaqueBytes_6 false
  change mySem false = S0Comp
  unfold mySem padCompSemOf compSemOf S0Comp
  dsimp only
  congr 1
  · funext sk
    rw [ho6]
    rfl
  · funext _sk nonce msg
    rw [show mkRecords false = r0Comp from r0_eq_comp, ho5, ho7]
    cases msg with
    | nil => exact ite_self _
    | cons b tl => simp only [ite_self]; split <;> rfl

noncomputable def myGhostComp : Ghost where
  σ := myGhostSigma
  addr := fun t =>
    match decEqBytesFast t msg0WireTerm with
    | isTrue _ => ((pqxdhSessionParams myParams).sendAddrs .A).getD []
    | isFalse _ =>
      match decEqBytesFast t msg1WireTerm with
      | isTrue _ => ((pqxdhSessionParams myParams).sendAddrs .A).getD []
      | isFalse _ => []

theorem myGhost_eq_comp : myGhost = myGhostComp := by
  unfold myGhost myGhostAddr myGhostComp
  congr 1
  funext t
  cases decEqBytesFast t msg0WireTerm with
  | isTrue h0 => simp [h0]
  | isFalse h0 =>
    cases decEqBytesFast t msg1WireTerm with
    | isTrue h1 => simp [h1]
    | isFalse h1 => simp [h0, h1]

theorem attackerKnows_of_getMessageSentAt {tr : ExecTrace} {idx : Nat} {t : DY.Bytes}
    (h : tr.getMessageSentAt idx = some t) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Trace.MessageSentAt_eq_getMessageSentAt t idx tr).mpr h)

end Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
