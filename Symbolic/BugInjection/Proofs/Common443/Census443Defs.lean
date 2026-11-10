/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.Census443Defs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState AliceHandshakeOut aliceAgreement serializedIk BundleHandles)
open DY.Libsignal.TripleRatchet DY.DiffieHellman DY.Spqr DY.SymEnc DY.X25519 Witnesses
abbrev NetEntry : Type := Network.ExecEntryT
abbrev RndEntry : Type := Random.ExecEntryT
abbrev TREntry : Type := ProtocolEvent.ExecEntryT TREvent
abbrev PQXDHEntry : Type := ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEntry : Type := ProtocolEvent.ExecEntryT CEvent
abbrev TRStEntry : Type := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
abbrev PQXDHStEntry : Type := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState PQXDHState)
abbrev NetE (msg : Bytes) : NetEntry := ⟨msg⟩
abbrev RndE (n : Nat) : RndEntry := ⟨n⟩
abbrev TREvE (ev : TREvent) : TREntry := ⟨ev⟩
abbrev PQEvE (ev : PQXDHEvent) : PQXDHEntry := ⟨ev⟩
abbrev CEvE (ev : CEvent) : CEntry := ⟨ev⟩
abbrev TRStE (me : Participant) (st : TRState) : TRStEntry := ⟨({ participant := me, state := st } : PersistentLocalState.LocalState TRState)⟩
def iniAliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opk : Option Bytes) : AliceHandshakeOut :=
  let ek := randTerm tr.length 32; let e := randTerm (tr.length + 1) 32;
  { ikA := dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk, ek := dhPk ek, ct := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1, keys := (aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2 }
def iniAliceStartState (tr : ExecTrace) (b : Participant) (o : AliceHandshakeOut) : TRState :=
  let dhsA := randTerm (tr.length + 2) 32; let (rkA, cksA) := createChain o.keys.rk o.spk dhsA;
  { peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB, rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0, sid := Concat.concat (dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1, recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }], spqr := spqrInit o.keys.pqr spqrA2B }
def iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : AliceHandshakeOut) : ExecTrace :=
  let dhsA := randTerm (tr.length + 2) 32; let stA := iniAliceStartState tr b o;
  ((((((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).append (NetE o.ct)).append (PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append (TREvE (.InitSession a b (dhPk dhsA) o.spk))).append (CEvE (.HandshakeSession (stA.sinfo a) (tr.length + 5)))).append (TRStE a stA)
def encPreSaltTr (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : ExecTrace :=
  let (_, key, _) := spqrSend stA.spqr (randTerm (tr₂.length + 1) cl);
  (((tr₂.append (RndE 32)).append (RndE cl)).append (NetE key))
def encSalt (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : Bytes := ((encPreSaltTr tr₂ stA cl).getMessageSentAt pq).getD (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1
def encWire (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : Bytes :=
  let (_, _, pqMsg) := spqrSend stA.spqr (randTerm (tr₂.length + 1) cl); let (_, seed) := kdfCk stA.cks; let keys := trMsgKeys (encSalt tr₂ stA cl pq) seed;
  trHonestWireMsg (dhPk stA.dhs) stA.ns stA.pn (symEnc keys.cipherKey keys.iv (randTerm tr₂.length 32)) pqMsg
def encMac (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : Bytes :=
  let (_, seed) := kdfCk stA.cks; let keys := trMsgKeys (encSalt tr₂ stA cl pq) seed;
  computeMac keys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq)
def encOut (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : Bytes := Concat.concat (encWire tr₂ stA cl pq) (encMac tr₂ stA cl pq)
def encSt (tr₂ : ExecTrace) (stA : TRState) (cl : Nat) : TRState :=
  { stA with cks := (kdfCk stA.cks).1, ns := stA.ns + 1, spqr := (spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).1 }
def encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : TRState) (cl pq : Nat) : ExecTrace :=
  let (_, seed) := kdfCk stA.cks; (((((encPreSaltTr tr₂ stA cl).append (TREvE (.Sent me stA.peer (dhPk stA.dhs) stA.ns (randTerm tr₂.length 32)))).append (TREvE (.MessageKey (stA.sinfo me) .sender seed (encSalt tr₂ stA cl pq) stA.ns stA.rIdx sIdx))).append (TRStE me (encSt tr₂ stA cl))).append (NetE (encOut tr₂ stA cl pq)))
def NoSessionEffect (tr : ExecTrace) (m : Move) : Prop :=
  ∀ i ∈ newIndices tr (m.next tr),
    ((m.next tr).at? i : Option TRStEntry) = none ∧ ((m.next tr).at? i : Option PQXDHEntry) = none ∧
      ((m.next tr).at? i : Option TREntry) = none ∧ ((m.next tr).at? i : Option CEntry) = none
def InvisibleNoEffect (tr : ExecTrace) (m : Move) : Prop := m.vis tr = [] ∧ NoSessionEffect tr m
def MovesFrom (P : ExecTrace → Move → Prop) : ExecTrace → List Move → Prop
  | _, [] => True
  | tr, m :: δ => P tr m ∧ MovesFrom P (m.next tr) δ
def NBSC38' (r : Records) (S : Sem) (g : Ghost) (v : Fin 4) (t : Fin 8) (τ₁ : List MachineEvent) (p : PreKeyFields) : Prop := ∀ (pre mid post : List Move) (hb : BundleHandles) (shown cl e c' : Nat),
    let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    Compat compI0 r S g → ModelRun r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post) → List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post)) →
    MovesFrom InvisibleNoEffect (setupTrace r) pre → MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    bobDoneBaseKeys (runTraceMoves r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post)) = [] → ¬ BobStartCollision compI0 r S g (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) p ⟨x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩
def eventBytes : MachineEvent → HwBytes
  | .recv b | .rng b | .pt b | .send b | .accept b | .leak b => b
def highBitWireBytes : HwBytes := eventBytes ((Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []))
def torsionWireBytes : HwBytes := eventBytes ((Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []))
def NbscHighBitComp' : Prop := ∀ (i : ExternInterpretation) (r : Records) (S : Sem), compFitsPinned Cheval26SmallSubgroupHighBitComp.setup i r → ∀ (g : Ghost) (p : PreKeyFields), parsePreKeyWire highBitWireBytes = some p → NBSC38' r S g 1 0 (Cheval26SmallSubgroupHighBitComp.trace.take 38) p
def NbscTorsionComp' : Prop := ∀ (i : ExternInterpretation) (r : Records) (S : Sem), compFitsPinned Cheval26SmallSubgroupTorsionComp.setup i r → ∀ (g : Ghost) (p : PreKeyFields), parsePreKeyWire torsionWireBytes = some p → NBSC38' r S g 0 1 (Cheval26SmallSubgroupTorsionComp.trace.take 38) p
def NoBsc38HB : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned Cheval26SmallSubgroupHighBitComp.setup compI0 r → ExplainsMoves compI0 r S Cheval26SmallSubgroupHighBitComp.who Cheval26SmallSubgroupHighBitComp.ok g ms (Cheval26SmallSubgroupHighBitComp.trace.take 38) → parsePreKeyWire highBitWireBytes = some p → ∃ g' ms', ExplainsMoves compI0 r S Cheval26SmallSubgroupHighBitComp.who Cheval26SmallSubgroupHighBitComp.ok g' ms' (Cheval26SmallSubgroupHighBitComp.trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' highBitWireBytes, ¬ BobStartCollision compI0 r S g' ms' p x
def NoBsc38TC : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned Cheval26SmallSubgroupTorsionComp.setup compI0 r → ExplainsMoves compI0 r S Cheval26SmallSubgroupTorsionComp.who Cheval26SmallSubgroupTorsionComp.ok g ms (Cheval26SmallSubgroupTorsionComp.trace.take 38) → parsePreKeyWire torsionWireBytes = some p → ∃ g' ms', ExplainsMoves compI0 r S Cheval26SmallSubgroupTorsionComp.who Cheval26SmallSubgroupTorsionComp.ok g' ms' (Cheval26SmallSubgroupTorsionComp.trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' torsionWireBytes, ¬ BobStartCollision compI0 r S g' ms' p x
def Split38DecompSwapRep (setup : PQXDHSpqrSetup) (who : List Participant) (ok : Nat → Bool) (τ₁ : List MachineEvent) (recvMsg38 : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms τ₁ → parsePreKeyWire recvMsg38 = some p → ∃ (pre mid post : List Move) (hb : BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩;
      Compat compI0 r S g ∧ ModelRun r ms₀ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms₀) ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧ MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o ∧ bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧
      ExplainsMoves compI0 r S who ok g ms' τ₁ ∧ x₀ ∈ preKeyRepresentations compI0 r S g ms' recvMsg38
theorem noBsc38HB_of (hNbsc : NbscHighBitComp') (hDecomp : Split38DecompSwapRep Cheval26SmallSubgroupHighBitComp.setup Cheval26SmallSubgroupHighBitComp.who Cheval26SmallSubgroupHighBitComp.ok (Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0) : NoBsc38HB := by intro r S g ms p hfits hex hp; obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ := hDecomp r S g ms p hfits hex hp; exact ⟨g, _, hex', _, hx₀, hNbsc compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩
theorem noBsc38TC_of (hNbsc : NbscTorsionComp') (hDecomp : Split38DecompSwapRep Cheval26SmallSubgroupTorsionComp.setup Cheval26SmallSubgroupTorsionComp.who Cheval26SmallSubgroupTorsionComp.ok (Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1) : NoBsc38TC := by intro r S g ms p hfits hex hp; obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ := hDecomp r S g ms p hfits hex hp; exact ⟨g, _, hex', _, hx₀, hNbsc compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩
end Symbolic.BugInjection.Proofs.Common443.Census443Defs
