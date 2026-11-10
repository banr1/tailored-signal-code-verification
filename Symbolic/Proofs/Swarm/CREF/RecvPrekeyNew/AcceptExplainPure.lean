/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecordsBridgePure
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.CREF.MacInv
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
import Batteries.Data.UInt
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
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
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
# Symbolic Pre-Key Session Start Execution and Matched-Prefix Extension

Steps `MatchedPrefix` across `Move.bobStart` for an accepting `session_recv_prekey` call given a
pre-key representation and handshake witness.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR (StE EvE NetE RndE Runs)
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.TripleRatchet (consumeMessageKey)

theorem moveOK_bobStart {r : ProtocolSetup} {tr : ExecTrace} {b : Participant} {kh : PQXDH.BobKeyHandles}
    {regIdxA pqIdx : Nat} {mh : PQXDH.PreKeyMsgHandles} {spqrMsgIdx : UInt32}
    {o : PQXDH.BobHandshakeOut} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c' : DY.Libsignal.TripleRatchet.RecvChain}
    {spqr' key seed pqSalt m raw : DY.Bytes} {opk : Option DY.Bytes}
    (hnext : (Move.bobStart b r.alice kh regIdxA mh pqIdx spqrMsgIdx 3).next tr =
      bobStartTr tr b r.alice o msg c' spqr' key seed pqSalt m)
    (hopk : bobOpkPk b kh tr = opk) (hek : tr.getMessageSentAt mh.ek = some o.ek)
    (hct : tr.getMessageSentAt mh.ct = some o.ct) (hmsg : tr.getMessageSentAt mh.msg = some raw) :
    DY.Libsignal.Composed.Refinement.MoveOK r (Move.bobStart b r.alice kh regIdxA mh pqIdx spqrMsgIdx 3) tr :=
  ⟨rfl, anchored_bobStart hnext hopk hek hct hmsg, rfl, trivial, trivial⟩

private theorem tr_bobKeys_eq (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) :
    TR.bobKeys r p x = bobKeys r p x := by
  unfold TR.bobKeys bobKeys Symbolic.Swarm.Stage1Trials.bobOpk? bobKeysOf
  rcases p.preKeyId with _ | id
  · rfl
  · by_cases h : (r.withOpk && id == r.opkId) = true <;> simp [h, Bind.bind, Option.bind, Pure.pure]

private theorem bobSaltSeed_unpack (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep)
    (msg : TRSignalMsg) (salt seed : DY.Bytes)
    (hparse : parseTrSignalMsg x.msg = some msg) (hss : TR.bobSaltSeed r p x = some (salt, seed)) :
    ∃ opk c' st', OpkSel r p opk ∧
      consumeMessageKey (bobChain r (bobKeysOf r x opk) msg) msg.counter = some (seed, c') ∧
      DY.Spqr.spqrRecv (DY.Spqr.spqrInit (bobKeysOf r x opk).pqr TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p) = some (st', salt) := by
  unfold TR.bobSaltSeed at hss
  have hbc_eq : ∀ k, TR.bobChain r k msg = bobChain r k msg := fun _ => rfl
  rw [tr_bobKeys_eq] at hss
  rcases hbk : bobKeys r p x with _ | keys; · simp [hbk, Bind.bind, Option.bind] at hss
  obtain ⟨opk, hsel, rfl⟩ := bobKeys_unpack r p x keys hbk
  simp only [hbk, hparse, hbc_eq, Bind.bind, Option.bind, Pure.pure] at hss
  rcases hcmk : consumeMessageKey (bobChain r (bobKeysOf r x opk) msg) msg.counter with _ | ⟨seed', c'⟩
  · simp [hcmk] at hss
  · simp only [hcmk] at hss
    rcases hspqr : DY.Spqr.spqrRecv (DY.Spqr.spqrInit (bobKeysOf r x opk).pqr TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p) with _ | ⟨st', salt'⟩
    · simp [hspqr] at hss
    · simp only [hspqr, Option.some.injEq, Prod.mk.injEq] at hss
      rcases hss with ⟨rfl, rfl⟩; exact ⟨opk, c', st', hsel, hcmk, hspqr⟩

theorem version_eq_messageVersion_of_preKeyRepresentations
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {b : HwBytes} {p : PreKeyFields} {x : PreKeyRep} {msg : TRSignalMsg}
    (hp : parsePreKeyWire b = some p)
    (hver : p.inner.messageVersion = BitVec.ofNat 8 TripleRatchet.messageVersion.toNat)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b)
    (hparse : parseTrSignalMsg x.msg = some msg) :
    msg.version = TripleRatchet.messageVersion := by
  rcases hx with ⟨_, _, _, _, p₂, hp₂, msg₁, hparse₁, _, _, _, _, _, _, _, hver₁⟩
  cases hp.symm.trans hp₂; cases hparse.symm.trans hparse₁
  apply UInt8.ext; rw [hver₁, hver]; decide

theorem bobAgreement_of_not_implicitReject (r : ProtocolSetup) (x : PreKeyRep) (opk : Option DY.Bytes) :
    PQXDH.bobAgreement (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk
      (setupPublic r 0) x.ek x.ct = some (bobKeysOf r x opk) :=
  rfl

theorem bobAgreement_eq_some (r : ProtocolSetup) (x : PreKeyRep) (opk : Option DY.Bytes) :
    PQXDH.bobAgreement (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk
      (setupPublic r 0) x.ek x.ct = some (bobKeysOf r x opk) :=
  rfl

theorem rpk_at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace}
    (hle : t ≤ T) {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) :
    (T.at? j : Option E) = some x := by
  by_cases hj : j < t.length
  · rw [← h, at?_of_le hle hj]
  · simp [Trace.at?, hj] at h

local macro "rpk_peel_setup_at" : tactic => `(tactic|
  (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
   repeat (first
     | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Trace.append, Trace.length])
     | exact TR.at?_append_eq _ _ rfl)))

private theorem rpk_runTrace_at?_19 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 19 = some (StE r.bob { kind := .pqPrekey, sk := setupSecret r 4 }) := by
  refine rpk_at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [(TR.setupSecret_eq r hne).2.2.2.1, TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
     repeat (first
       | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
       | (refine TR.at?_append_eq _ _ ?_; simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

private theorem rpk_runTrace_at?_1 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 1 =
      some (EvE (.IdentityRegistered r.alice (setupPublic r 0)
        (DY.Signature.vk (randTerm 0 32)) true)) := by
  have h0 : setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) := by
    rw [(TR.setupPublic_eq r hne).1, (TR.setupSecret_eq r hne).1]
  rw [h0]; refine rpk_at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;>
    (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
     repeat (first
       | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
       | (refine TR.at?_append_eq _ _ ?_; simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

def bobKeyHandlesOf (opk : Option DY.Bytes) : PQXDH.BobKeyHandles :=
  ⟨9, 13, 19, opk.map (fun _ => 24)⟩

private theorem stOpt_bobKeyHandlesOf (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move)
    (p : PreKeyFields) (opk : Option DY.Bytes) (hsel : OpkSel r p opk) :
    StOpt (runTraceMoves r ms) r.bob (bobKeyHandlesOf opk).opk opk := by
  rcases hsel with ⟨_, rfl⟩ | ⟨hwith, _, rfl⟩
  · trivial
  · exact MacInv.runTrace_at?_24 r hne ms hwith

theorem rpk_setupPublic_8 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (hw : r.withOpk = true) :
    setupPublic r 8 = DY.DiffieHellman.dhPk (setupSecret r 6) := by
  rw [(TR.setupSecret_eq r hne).2.2.2.2 hw, setupPublic, setupSent, TR.setupTrace_eq r hne, hw]
  simp only [↓reduceIte]
  let f (T : ExecTrace) : List DY.Bytes :=
    (newIndices Trace.nil T).filterMap fun i => T.getMessageSentAt i
  change (f (TR.setupTr5 r.alice r.bob))[8]?.getD (randTerm 0 0) =
    DY.DiffieHellman.dhPk (randTerm 22 32)
  have hnil : f Trace.nil = [] := by
    simp [f, newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have happ : ∀ {E : Type} [ExecTraceTypes.Has E] (T : ExecTrace) (e : E),
      f (T.append e) = f T ++
        (match ((T.append e).at? T.length : Option Network.ExecEntryT) with
         | none => []
         | some entry => [entry.msg]) := by
    intro E _ T e
    have hidx : newIndices Trace.nil (T.append e) = newIndices Trace.nil T ++ [T.length] := by
      simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat]
    have hpre : List.filterMap (fun i => (T.append e).getMessageSentAt i) (newIndices Trace.nil T) =
        f T := by
      apply List.filterMap_congr
      intro i hi
      have hlt : i < T.length := by
        simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1, List.mem_range'] at hi
        omega
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, TR.at?_append_of_lt T e hlt]
    have hlast := Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1 T.length (T.append e)
    dsimp only [f]
    rw [hidx, List.filterMap_append, hpre]
    cases hproj : ((T.append e).at? T.length : Option Network.ExecEntryT) <;>
      simp [List.filterMap_cons, List.filterMap_nil, hlast, hproj, f]
  have hnet : ∀ (T : ExecTrace) (b : DY.Bytes), f (T.append (TR.NetE b)) = f T ++ [b] := by
    intro T b; rw [happ, TR.at?_append_eq T (TR.NetE b) rfl]
  have hrnd : ∀ (T : ExecTrace) (n : Nat), f (T.append (TR.RndE n)) = f T := by
    intro T n; rw [happ, TR.at?_append_eq_of_proj T (TR.RndE n) rfl none rfl, List.append_nil]
  have hev : ∀ (T : ExecTrace) (ev), f (T.append (TR.EvE ev)) = f T := by
    intro T ev; rw [happ, TR.at?_append_eq_of_proj T (TR.EvE ev) rfl none rfl, List.append_nil]
  have hst : ∀ (T : ExecTrace) (p : Participant) (s), f (T.append (TR.StE p s)) = f T := by
    intro T p s; rw [happ, TR.at?_append_eq_of_proj T (TR.StE p s) rfl none rfl, List.append_nil]
  simp only [TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1,
    hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
  rfl

private theorem eventMatchesEntry_recv_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} (_hne : r.alice ≠ r.bob) {S : OpaqueSymbolSemantics} {g : Ghost}
    (_hc : GhostAndSemMatchSetup interpretation r S g) {ms : List Move} {b : HwBytes}
    {p : PreKeyFields} {x : PreKeyRep} {opk : Option DY.Bytes}
    (hp : parsePreKeyWire b = some p)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) (hsel : OpkSel r p opk) :
    EventMatchesEntry interpretation r S g (.recv b)
      ⟨.recv, [x.ek, x.ct, x.msg] ++ (opk.map DY.DiffieHellman.dhPk).toList, .preKeyRecv, none⟩ := by
  refine ⟨rfl, ?_⟩; dsimp only [eventBytes]
  rcases hsel with ⟨hpk, rfl⟩ | ⟨hw, hpk, rfl⟩
  · refine ⟨hx.2.2.2.1, p, hp, ?_⟩; simp [hpk]
  · refine ⟨hx.2.2.2.1, p, hp, ?_⟩; simp [hpk, hw]

private theorem eventMatchesEntry_rng_updateFreshAt {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} (g : Ghost) (ts : Nat) (d : HwBytes) :
    EventMatchesEntry interpretation r S
      { g with σ := TR.FreshSigma.updateFreshAt g.σ ts 32 d } (.rng d)
      ⟨.rng, [randTerm ts 32], .single, none⟩ := by
  refine ⟨rfl, ?_⟩; dsimp only [eventBytes, List.map]; unfold randTerm
  rw [TR.gamma_rand]; simp [TR.FreshSigma.updateFreshAt_self]

private theorem eventMatchesEntry_accept_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {m : DY.Bytes} {pt : HwBytes} {anc : Option Nat}
    (hpt : gamma interpretation S g m = pt) :
    EventMatchesEntry interpretation r S g (.accept pt) ⟨.accept, [m], .single, anc⟩ := by
  refine ⟨rfl, ?_⟩; simp [eventBytes, hpt]

private theorem visStampsLt_recv_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {b : HwBytes} {p : PreKeyFields} {x : PreKeyRep} {opk : Option DY.Bytes} {ts : Nat}
    (hrun : ModelRun r ms) (hts : (runTraceMoves r ms).length ≤ ts)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) (hsel : OpkSel r p opk) :
    TR.FreshSigma.VisStampsLt interpretation S g ts
      ⟨.recv, [x.ek, x.ct, x.msg] ++ (opk.map DY.DiffieHellman.dhPk).toList, .preKeyRecv, none⟩ := by
  have htr := TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g ts hrun.2.2.1.1 hts
  refine TR.FreshSigma.visStampsLt_of_terms rfl ?_
  intro t ht; dsimp only at ht
  rcases List.mem_append.mp ht with ht | ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact TR.FreshSigma.traceEntriesLt_knows htr hx.1
    · exact TR.FreshSigma.traceEntriesLt_knows htr hx.2.1
    · exact TR.FreshSigma.traceEntriesLt_knows htr hx.2.2.1
  · rcases hsel with ⟨_, rfl⟩ | ⟨hw, _, rfl⟩
    · cases ht
    · simp only [Option.map_some, Option.toList_some, List.mem_singleton] at ht; subst ht
      rw [← rpk_setupPublic_8 r hne hw]; exact TR.FreshSigma.stampsLt_setupPublic hts htr 8

private theorem stampsLt_decrypted_plaintext {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b : HwBytes}
    {x : PreKeyRep} {msg : TRSignalMsg} {k iv m : DY.Bytes} {ts : Nat}
    (hrun : ModelRun r ms) (hts : (runTraceMoves r ms).length ≤ ts)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) (hparse : parseTrSignalMsg x.msg = some msg)
    (hdec : PQXDH.errToOption (DY.SymEnc.symDec k iv msg.ciphertext) = some m) :
    TR.FreshSigma.StampsLt interpretation S g ts m := by
  have htr := TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g ts hrun.2.2.1.1 hts
  have hmsg := TR.FreshSigma.traceEntriesLt_knows htr hx.2.2.1
  exact TR.FreshSigma.stampsLt_symDec hdec (TR.FreshSigma.stampsLt_parseTrSignalMsg hmsg hparse).2.2.2.1

theorem rpk_callStarts_accept_blk (b d pt : HwBytes) :
    callStarts [.recv b, .rng d, .accept pt] = [.recv b] := rfl

theorem rpk_bobStart_of_exactRep_pqSalt_at {interpretation : ExternInterpretation}
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} {b d pt : HwBytes} {p : PreKeyFields} {x : PreKeyRep}
    {msg : TRSignalMsg} {salt seed pqSalt m : DY.Bytes}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    (hmp : MatchedPrefix interpretation r S who g ms τ)
    (hlt_pre : ∀ i (mv : Move) promote, ms[i]? = some mv → mv.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts τ).length)
    (hwho : who[(callStarts τ).length]? = some r.bob)
    (hno_done : ∀ q, parsePreKeyWire b = some q →
      ¬ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms),
        ecKey (gamma interpretation S g ek) = q.baseKey.take 33)
    (hp : parsePreKeyWire b = some p)
    (hver : p.inner.messageVersion = BitVec.ofNat 8 TripleRatchet.messageVersion.toNat)
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b)
    (hcan : PQXDH.isCanonicalKey x.ek = true)
    (hparse : parseTrSignalMsg x.msg = some msg) (hlow : TripleRatchet.x25519LowOrder msg.ratchetKey = false)
    (hss : TR.bobSaltSeed r p x = some (salt, seed))
    (hpqSalt : (((runTraceMoves r ms).append (RndE 32)).append (NetE salt)).at? pqIdx = some (NetE pqSalt))
    (hmac : msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
      (PQXDH.serializedIk (setupPublic r 0))
      (PQXDH.serializedIk (setupPublic r 2)) msg.wire)
    (hdec : PQXDH.errToOption (DY.SymEnc.symDec
      (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m)
    (hpt : gamma interpretation S g m = pt)
    (hopk_unused : r.withOpk = true → p.preKeyId = some r.opkId →
      PQXDH.opkUsedB (runTraceMoves r ms) r.bob (DY.DiffieHellman.dhPk (setupSecret r 6)) = false)
    (hek : (runTraceMoves r ms).at? mh.ek = some (NetE x.ek))
    (hct : (runTraceMoves r ms).at? mh.ct = some (NetE x.ct))
    (hmsg : (runTraceMoves r ms).at? mh.msg = some (NetE x.msg)) :
    ∃ opk, OpkSel r p opk ∧
      let tr := runTraceMoves r ms; let kh := bobKeyHandlesOf opk
      let mBob := Move.bobStart r.bob r.alice kh 1 mh pqIdx (preKeySpqrIndex p) 3
      let g' : Ghost := { g with σ := TR.FreshSigma.updateFreshAt g.σ tr.length 32 d }
      MatchedPrefix interpretation r S who g' (ms ++ [mBob]) (τ ++ [.recv b, .rng d, .accept pt]) := by
  obtain ⟨opk, c', spqr', hsel, hcmk, hspqr⟩ := bobSaltSeed_unpack r p x msg salt seed hparse hss
  refine ⟨opk, hsel, ?_⟩; intro tr kh mBob g'
  have hopk_st : StOpt tr r.bob kh.opk opk := stOpt_bobKeyHandlesOf r hne ms p opk hsel
  have hmac_eq : msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
      (bobRatchetedSt r.alice (DY.DiffieHellman.dhPk (setupSecret r 1)) (setupPublic r 0)
        (bobKeysOf r x opk) (setupSecret r 2) msg.ratchetKey (randTerm tr.length 32)).peerIk
      (bobRatchetedSt r.alice (DY.DiffieHellman.dhPk (setupSecret r 1)) (setupPublic r 0)
        (bobKeysOf r x opk) (setupSecret r 2) msg.ratchetKey (randTerm tr.length 32)).myIk
      msg.wire := by
    have hm0 := hmac
    have hp2 : setupPublic r 2 = DY.DiffieHellman.dhPk (setupSecret r 1) := by
      rw [(TR.setupPublic_eq r hne).2.1, (TR.setupSecret_eq r hne).2.1]
    rw [hp2] at hm0; exact hm0
  have hused : ∀ o, opk = some o →
      PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE salt)) r.bob (DY.DiffieHellman.dhPk o) = false := by
    intro o ho; rw [opkUsedB_append_rnd_net]
    rcases hsel with ⟨_, rfl⟩ | ⟨hw, hpk, rfl⟩
    · cases ho
    · injection ho with ho; subst ho; exact hopk_unused hw hpk
  have hruns := Runs.bobStart (MacInv.runTrace_at?_9 r hne ms) (MacInv.runTrace_at?_13 r hne ms)
    (rpk_runTrace_at?_19 r hne ms) hopk_st (rpk_runTrace_at?_1 r hne ms) hek hct hcan
    (bobAgreement_of_not_implicitReject r x opk) hmsg hparse
    (version_eq_messageVersion_of_preKeyRepresentations hp hver hx hparse)
    hlow hcmk hspqr hpqSalt hmac_eq hdec hused
  have hnext : mBob.next tr = bobStartTr tr r.bob r.alice
      (bobOut (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk (setupPublic r 0)
        x.ek x.ct (bobKeysOf r x opk)) msg c' spqr' salt seed pqSalt m :=
    (TR.Runs.bind hruns (TR.Runs.pure () _)).2
  have hopk_pk : bobOpkPk r.bob kh tr = opk.map DY.DiffieHellman.dhPk := bobOpkPk_eq tr r.bob kh opk hopk_st
  have hek_sent := rpk_getMessageSentAt_of_at? hek
  have hct_sent := rpk_getMessageSentAt_of_at? hct
  have hmsg_sent := rpk_getMessageSentAt_of_at? hmsg
  have hvis := vis_bobStart hnext hopk_pk hek_sent hct_sent hmsg_sent
  have hmOK := moveOK_bobStart (r := r) hnext hopk_pk hek_sent hct_sent hmsg_sent
  have htr_lt := TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g tr.length hmp.2.1.2.2.1.1 (Nat.le_refl tr.length)
  have hmp' : MatchedPrefix interpretation r S who g' ms τ :=
    TR.FreshSigma.matchedPrefix_updateFreshAt hmp (Nat.le_refl tr.length) 32 d
  have hrun' : ModelRun r (ms ++ [mBob]) :=
    DY.Libsignal.Composed.Refinement.modelRun_snoc hmp'.2.1 hmOK
      (by rw [DY.Libsignal.Composed.Refinement.runTrace_snoc]; exact b5_bobStart_reachable hmp.2.1.2.2.1.1 _ _ _ _ _ _ _ _)
      (fun _ _ _ _ _ _ _ _ hl => nomatch hl)
  have hrole' : RoleFaithful r who (ms ++ [mBob]) :=
    DY.Libsignal.Composed.Refinement.roleFaithful_snoc_party hmp'.2.2.1 rfl
      (by rw [DY.Libsignal.Composed.Refinement.matchedPrefix_callCount_eq hmp']; exact hwho)
  have hpath' : PathFaithful interpretation r S g' (ms ++ [mBob]) (τ ++ [.recv b, .rng d, .accept pt]) := by
    have hcs_app : callStarts (τ ++ [.recv b, .rng d, .accept pt]) = callStarts τ ++ [.recv b] := by
      rw [DY.Libsignal.Composed.Refinement.callStarts_append, rpk_callStarts_accept_blk]
    intro i mv promote b' q hi hpath hcall hparse_q
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      rw [List.take_append_of_le_length hlt.le] at hcall ⊢
      have hk := hlt_pre i mv promote hi hpath
      rw [hcs_app, List.getElem?_append_left hk] at hcall
      exact hmp'.2.2.2.1 i mv promote b' q hi hpath hcall hparse_q
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; injection hpath with hprom; subst hprom
        have htk : (ms ++ [mBob]).take ms.length = ms := by simp
        rw [htk, DY.Libsignal.Composed.Refinement.matchedPrefix_callCount_eq hmp', hcs_app,
          List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at hcall
        injection hcall with hb_eq; subst hb_eq; rw [htk]
        refine ⟨fun h => Bool.noConfusion h, fun ⟨ek, hek_mem, heq⟩ => False.elim (hno_done q hparse_q ⟨ek, hek_mem, ?_⟩)⟩
        have hek_lt := TR.FreshSigma.stampsLt_of_mem_bobDoneBaseKeys (DY.Trace.le_refl _) htr_lt hek_mem
        rwa [TR.FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g tr.length 32 d ek hek_lt] at heq
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  have hx' : x ∈ preKeyRepresentations interpretation r S g' (ms ++ [mBob]) b :=
    preKeyRepresentations_mono_append (TR.FreshSigma.preKeyRepresentations_updateFreshAt_of_traceEntriesLt hx htr_lt 32 d)
  have hread_blk : ∀ ev ∈ ([MachineEvent.recv b, .rng d, .accept pt]).zip (runMoves [mBob] tr).2, ev.2.kind = .recv →
      DY.Libsignal.Composed.Refinement.ReadOKWith (recvRepresentations interpretation r S g' (ms ++ [mBob]))
        (preKeyRepresentations interpretation r S g' (ms ++ [mBob])) ev.1 ev.2 := by
    have hrm : (runMoves [mBob] tr).2 = mBob.vis tr := by simp [runMoves]
    rw [hrm, hvis]
    intro ev hev hk
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl | rfl
    · exact hx'
    · cases hk
    · cases hk
  have hrecv' : EventMatchesEntry interpretation r S g' (.recv b)
      ⟨.recv, [x.ek, x.ct, x.msg] ++ (opk.map DY.DiffieHellman.dhPk).toList, .preKeyRecv, none⟩ :=
    (TR.FreshSigma.eventMatchesEntry_updateFreshAt_of_visStampsLt interpretation r S g tr.length 32 d
      (.recv b) _ (visStampsLt_recv_bobStart hne hmp.2.1 (Nat.le_refl tr.length) hx hsel)).mpr
      (eventMatchesEntry_recv_bobStart hne hmp.1 hp hx hsel)
  have hrng' := eventMatchesEntry_rng_updateFreshAt (interpretation := interpretation) (r := r) (S := S) g tr.length d
  have hm_lt := stampsLt_decrypted_plaintext hmp.2.1 (Nat.le_refl tr.length) hx hparse hdec
  have hpt' : gamma interpretation S g' m = pt := by
    rw [TR.FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g tr.length 32 d m hm_lt]; exact hpt
  have hF_blk : List.Forall₂ (EventMatchesEntry interpretation r S g') [.recv b, .rng d, .accept pt] (runMoves [mBob] tr).2 := by
    have hrm : (runMoves [mBob] tr).2 = mBob.vis tr := by simp [runMoves]
    rw [hrm, hvis]
    exact .cons hrecv' (.cons hrng' (.cons (eventMatchesEntry_accept_bobStart (r := r) hpt') .nil))
  exact DY.Libsignal.Composed.Refinement.matchedPrefix_append hmp' hrun' hrole' hpath' hread_blk hF_blk

theorem bobSaltSeed_some_of_not_implicitReject {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {used : Bool} {p : PreKeyFields}
    {x : PreKeyRep} {msg : TRSignalMsg}
    (hopk : p.preKeyId = none ∨ (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId))
    (hparse : parseTrSignalMsg x.msg = some msg)
    (hctr : msg.counter.toNat ≤ TripleRatchet.maxForwardJumps)
    (hpq_ne : gamma interpretation S g msg.pqRatchet ≠ []) :
    ∃ keys c' st' salt seed,
      bobKeys r p x = some keys ∧
      TripleRatchet.consumeMessageKey (bobChain r keys msg) msg.counter = some (seed, c') ∧
      DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p) = some (st', salt) ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      TR.bobMac r p x = some (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire) := by
  let opk : Option DY.Bytes := match p.preKeyId with
    | none => none | some _ => some (setupSecret r 6)
  let spk := setupSecret r 2
  let keys := bobKeysOf r x opk
  have hbk : bobKeys r p x = some keys := by
    unfold bobKeys Symbolic.Swarm.Stage1Trials.bobOpk?
    rcases hopk with hnone | ⟨hw, _, hsome⟩
    · simp [keys, opk, hnone]
    · simp [keys, opk, hsome, hw]
  obtain ⟨c', hcmk⟩ :=
    TR.consumeMessageKey_index_zero msg.ratchetKey
      (TripleRatchet.createChain keys.rk msg.ratchetKey spk).2 msg.counter hctr 2
  obtain ⟨st', salt, hspqr, _⟩ :=
    TR.spqrRecv_init_b2a_of_gamma_ne_nil interpretation S g keys.pqr msg.pqRatchet (preKeySpqrIndex p) hpq_ne
  refine ⟨keys, c', st', salt,
    (TripleRatchet.kdfCk (TripleRatchet.chainKeyAt
      (TripleRatchet.createChain keys.rk msg.ratchetKey spk).2 msg.counter.toNat)).2,
    hbk, hcmk, hspqr, ?_, ?_⟩
  · unfold TR.bobSaltSeed TR.bobChain; rw [tr_bobKeys_eq]; simp only [hbk, hparse, Bind.bind, Option.bind, Pure.pure]
    rw [hcmk]; dsimp only; rw [hspqr]
  · unfold TR.bobMac TR.bobChain; rw [tr_bobKeys_eq]; simp only [hbk, hparse, Bind.bind, Option.bind, Pure.pure]
    rw [hcmk]; dsimp only; rw [hspqr]

private theorem rpk_gamma_variant_pack (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (v : DY.X25519.Variant.SubF DY.Bytes) :
    gamma i S g v.pack =
      variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g v.key) v.torsion)
        v.variation := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

private theorem rpk_torsionShift_length (i : ExternInterpretation) (point : HwBytes) (t : Fin 8) :
    (DY.Libsignal.Refinement.torsionShift i point t).length = point.length := by
  unfold DY.Libsignal.Refinement.torsionShift
  split
  · rfl
  · rename_i h
    have hlen : point.length = 32 := by revert h; simp
    split
    · split
      · rename_i q _ hq; omega
      · rfl
    · rfl

private theorem isLowOrderKey_gamma_x25519Key_rpk (i : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold i) (S : OpaqueSymbolSemantics)
    (g : Ghost) (pk : DY.Bytes) :
    DY.X25519.isLowOrderKey ((gamma i S g (DY.X25519.normalizeX25519Key pk)).map BitVec.toNat) =
      DY.X25519.isLowOrderKey ((gamma i S g pk).map BitVec.toNat) := by
  unfold DY.X25519.normalizeX25519Key; split
  · rename_i x h; have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    simp only [h] at hv
    have hgamma_pk : gamma i S g pk =
        variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion)
          x.variation := by
      rw [← hv, rpk_gamma_variant_pack]
    by_cases hl : (gamma i S g x.key).length = 32
    · have hl_ts :
          (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion).length = 32 := by
        rw [rpk_torsionShift_length, hl]
      have hs := TR.variantBytes_spec _ hl_ts x.variation
      have hl_pk : (gamma i S g pk).length = 32 := by
        rw [hgamma_pk]; exact hs.1
      have hu : DY.X25519.uCoord ((gamma i S g pk).map BitVec.toNat) =
          DY.X25519.uCoord
            ((DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion).map
              BitVec.toNat) := by
        rw [hgamma_pk]; exact hs.2
      have ha0 : (List.replicate 32 0#8).length = 32 := by simp
      have h_agr_u := hEq.x25519_agreement_reads_u_coordinate
        (List.replicate 32 0#8) (gamma i S g pk)
        (DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion)
        hl_pk hl_ts hu
      have h_agr_t := hEq.x25519_agreement_torsion_invariant
        (List.replicate 32 0#8) (gamma i S g x.key) x.torsion
      have h_iff_pk := hEq.x25519_agreement_zero_iff_low_order
        (List.replicate 32 0#8) (gamma i S g pk) ha0 hl_pk
      have h_iff_k := hEq.x25519_agreement_zero_iff_low_order
        (List.replicate 32 0#8) (gamma i S g x.key) ha0 hl
      apply Bool.eq_iff_iff.mpr
      rw [← h_iff_k, ← h_iff_pk, h_agr_u, h_agr_t]
    · have hts_eq : DY.Libsignal.Refinement.torsionShift i (gamma i S g x.key) x.torsion =
          gamma i S g x.key := by
        unfold DY.Libsignal.Refinement.torsionShift
        split
        · rfl
        · rename_i h_ts; exfalso; apply hl; revert h_ts; simp
      have hpk_eq : gamma i S g pk = gamma i S g x.key := by
        rw [hgamma_pk]; unfold variantBytes; simp only [hts_eq, hl, ↓reduceIte]
      rw [hpk_eq]
  · rfl

theorem x25519LowOrder_false_of_gamma_notLow
    (i : ExternInterpretation) (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold i)
    (S : OpaqueSymbolSemantics) (g : Ghost) {L : DY.Bytes}
    (hNotLow : DY.X25519.isLowOrderKey ((gamma i S g L).map BitVec.toNat) = false) :
    TripleRatchet.x25519LowOrder L = false := by
  unfold TripleRatchet.x25519LowOrder
  rcases hb : DY.Literal.bytesToLiteral (DY.X25519.normalizeX25519Key L) with _ | b; · rfl
  dsimp only
  have hlit : DY.X25519.normalizeX25519Key L = DY.Literal.literalToBytes b := by
    have := DY.Literal.literalToBytes_bytesToLiteral (DY.X25519.normalizeX25519Key L); rwa [hb] at this
  have h1 := isLowOrderKey_gamma_x25519Key_rpk i hEq S g L
  have hba : (gamma i S g (DY.Literal.literalToBytes b)).map BitVec.toNat =
      b.data.toList.map (·.toNat) := by
    have hgl : gamma i S g (DY.Literal.literalToBytes b) = ofByteArray b := by
      unfold gamma gamma'
      show ((({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
      rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]; rfl
    rw [hgl]; simp [ofByteArray]
  rw [hlit, hba, hNotLow] at h1; exact h1

/-- Hypothesis that an 8-byte MAC parsed from a pre-key representation is not SPQR-headed. -/
def RpkNotSpqrMacHyp (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) : Prop :=
  ∀ {g : Ghost} {ms : List Move} {b : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg},
    parsePreKeyWire b = some p →
    x' ∈ preKeyRepresentations interpretation r S g ms b →
    parseTrSignalMsg x'.msg = some msg' →
    (gamma interpretation S g msg'.mac).length = 8 →
    MacInv.notSpqrHeaded msg'.mac

/-- Hypothesis constructing a canonical forged pre-key representation when the receive seed is
attacker-known. -/
def RpkSeedAkHyp (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) : Prop :=
  ∀ {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b ct_wire pt : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {keys' : PQXDH.HandshakeKeys} {seed' salt' st'' : DY.Bytes} {c' : TripleRatchet.RecvChain},
    MatchedPrefix interpretation r S who g ms acc →
    parsePreKeyWire b = some p →
    ¬ KyberMismatch interpretation r p →
    p.kyberCiphertext = some (kyberKey ct_wire) →
    ct_wire.length = 1568 →
    (p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId)) →
    x' ∈ preKeyRepresentations interpretation r S g ms b →
    ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g ms p x' →
    bobKeys r p x' = some keys' →
    parseTrSignalMsg x'.msg = some msg' →
    TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c') →
    DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys'.pqr TripleRatchet.spqrB2A)
      msg'.pqRatchet (preKeySpqrIndex p) = some (st'', salt') →
    TR.bobSaltSeed r p x' = some (salt', seed') →
    (gamma interpretation S g x'.ek).length = 32 →
    DY.X25519.leValue ((gamma interpretation S g x'.ek).map BitVec.toNat) < DY.X25519.p25519 →
    (DY.X25519.isLowOrderKey ((gamma interpretation S g x'.ek).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation (gamma interpretation S g x'.ek)) →
    TripleRatchet.x25519LowOrder msg'.ratchetKey = false →
    msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps →
    gamma interpretation S g
      (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
      gamma interpretation S g msg'.mac →
    interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [gamma interpretation S g msg'.ciphertext,
       gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').cipherKey,
       (gamma interpretation S g (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt →
    gamma interpretation S g msg'.pqRatchet ≠ [] →
    seed'.AttackerKnows (runTraceMoves r ms) →
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (salt seed pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g ms b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      pqSalt.AttackerKnows (runTraceMoves r ms) ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m ∧
      gamma interpretation S g m = pt

end Symbolic.Swarm.CREF.CliPure
