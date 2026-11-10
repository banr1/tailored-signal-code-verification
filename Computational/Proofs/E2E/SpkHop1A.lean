/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
public import Computational.Proofs.E2E.Relabel.GameEq
public import Computational.Proofs.E2E.SpkLeakRedModel
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Session-Model Relabelling and Epoch-0 Key Coupling for Hop 2

**Checked by Lean.**

Defines `configR1OnCurveSpk` incorporating the early-Bob-corruption guards (`DEV-LS33`, `DEV-LS34`)
and establishes the lazy random-oracle table bijection via `hker`, epoch-0 key patching
(`patchGameSpk`), and oracle step lemmas for Hop 2 coupling.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

/-! ## Early-Bob-corruption game configuration -/

/-- Extends `configR1OnCurve` with the early-Bob-corruption guards `noBobCorrInEpoch0` (`DEV-LS33`)
and `noBobCorrWhileAliceBelowEpoch10` (`DEV-LS34`). -/
def configR1OnCurveSpk {St Msg : Type} (onImage : List (BitVec 8) → Bool) :
    ConfigR St Msg (List (BitVec 8)) :=
  { configR1OnCurve onImage with
    corrOK := fun st P =>
      (configR1OnCurve onImage (St := St) (Msg := Msg)).corrOK st P && noBobCorrInEpoch0 st P &&
          noBobCorrWhileAliceBelowEpoch10 st P }

@[simp] theorem mapSt_noCorrB0 {St₁ St₂ Msg C : Type} (φ : St₁ → St₂)
    (s : GameState St₁ Msg C) (P : Party) :
    noBobCorrInEpoch0 (mapSt φ s) P = noBobCorrInEpoch0 s P := rfl

@[simp] theorem mapSt_noCorrBWin {St₁ St₂ Msg C : Type} (φ : St₁ → St₂)
    (s : GameState St₁ Msg C) (P : Party) :
    noBobCorrWhileAliceBelowEpoch10 (mapSt φ s) P = noBobCorrWhileAliceBelowEpoch10 s P := rfl

section RelabelSpk

variable {Key St₁ St₂ Msg Coins RCoins : Type}
variable [DecidableEq Msg] [SampleableType Coins] [SampleableType RCoins]

end RelabelSpk

/-! ## Hop 2 coupling under the random function -/

set_option linter.unusedSectionVars false

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

/-! ### Lazy random-oracle table bijection -/

/-- Maps an abstract point-tag table `L` to the concrete PRF table under scalar `x`. -/
def tableFor (Dh : DHFun (BitVec 256) Pt) (x : BitVec 256)
    (L : List (Pt × BitVec 256)) : List (Pt × BitVec 256) :=
  L.map fun pt => (Dh.dh x pt.1, pt.2)

omit [Zero Pt] [SampleableType Pt] in
theorem lookup_tableFor_eq (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P P' : Pt), Dh.dh x P = Dh.dh x P' ↔ Dh.dh s P = Dh.dh s P')
    (x : BitVec 256) (P_pt : Pt) (L : List (Pt × BitVec 256)) :
    (tableFor Dh x L).lookup (Dh.dh x P_pt) = (tableFor Dh s L).lookup (Dh.dh s P_pt) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨P', t⟩
    have hbeq : (Dh.dh x P_pt == Dh.dh x P') = (Dh.dh s P_pt == Dh.dh s P') := by
      by_cases hs : Dh.dh s P_pt = Dh.dh s P'
      · have hx : Dh.dh x P_pt = Dh.dh x P' := (hker x P_pt P').mpr hs
        simp [hs, hx]
      · have hx : Dh.dh x P_pt ≠ Dh.dh x P' := fun h => hs ((hker x P_pt P').mp h)
        simp [hs, hx]
    change (match Dh.dh x P_pt == Dh.dh x P' with
              | true => some t | false => (tableFor Dh x tl).lookup (Dh.dh x P_pt)) =
      (match Dh.dh s P_pt == Dh.dh s P' with
         | true => some t | false => (tableFor Dh s tl).lookup (Dh.dh s P_pt))
    rw [hbeq, ih]

def stepTableFor (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (P_pt : Pt) (L : List (Pt × BitVec 256)) :
    ProbComp (BitVec 256 × List (Pt × BitVec 256)) :=
  match (tableFor Dh s L).lookup (Dh.dh s P_pt) with
  | some t => pure (t, L)
  | none => do
    let t ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    return (t, (P_pt, t) :: L)

omit [Zero Pt] [SampleableType Pt] in
theorem prfEval_true_tableFor_bind {Key α : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P P' : Pt), Dh.dh x P = Dh.dh x P' ↔ Dh.dh s P = Dh.dh s P')
    (key : Key) (x : BitVec 256) (P_pt : Pt) (L : List (Pt × BitVec 256))
    (F : BitVec 256 × PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((MACScheme.prfEval mac (Dh.dh x P_pt)).run ⟨key, true, tableFor Dh x L⟩ >>= F) =
      (stepTableFor Dh s P_pt L >>= fun r => F (r.1, ⟨key, true, tableFor Dh x r.2⟩)) := by
  unfold MACScheme.prfEval stepTableFor
  simp only [StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte,
    lookup_tableFor_eq Dh s hker x P_pt L]
  cases (tableFor Dh s L).lookup (Dh.dh s P_pt) with
  | some t =>
    simp [StateT.run_pure]
  | none =>
    simp [StateT.run_monadLift, monadLift_self, StateT.run_set,
      tableFor]

/-! ### Bob epoch-0 sender-key patching -/

def setBobSpk (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  { g with session := { g.session with
      senderChain := g.session.senderChain.map fun _sc => ⟨kp, ⟨ck0, 0⟩⟩ } }

def patchBobSpk (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  if g.epoch = 0 then setBobSpk kp ck0 g else g

/-! ### Alice head public-key patching -/

def setHeadPubKey (spk : PublicKey) (cs : List ReceiverChain) : List ReceiverChain :=
  match cs with
  | [] => []
  | rc :: rest => { rc with senderRatchetKey := spk } :: rest

def setAliceSpkPub (spk : PublicKey) (g : GhostState PQ) : GhostState PQ :=
  { g with session := { g.session with
                        receiverChains := setHeadPubKey spk g.session.receiverChains } }

def patchAlicePub (spk : PublicKey) (g : GhostState PQ) : GhostState PQ :=
  if 0 ∈ g.chainEpochs then setAliceSpkPub spk g else g

theorem findIdx?_setHeadPubKey (spk : PublicKey) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (their : PublicKey)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    (setHeadPubKey spk (rc0 :: rest)).findIdx? (fun c => c.senderRatchetKey == their) =
      (rc0 :: rest).findIdx? (fun c => c.senderRatchetKey == their) := by
  simp [setHeadPubKey, List.findIdx?_cons, hne0, hne_spk]

theorem length_setHeadPubKey (spk : PublicKey) (cs : List ReceiverChain) :
    (setHeadPubKey spk cs).length = cs.length := by
  cases cs <;> rfl

theorem takeSkippedKey_setHeadPubKey (spk : PublicKey) (their : PublicKey)
    (counter : BitVec 32) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    Mut.exec (RatchetState.takeSkippedKey their counter)
      { r with receiverChains := setHeadPubKey spk r.receiverChains } =
      ( (Mut.exec (RatchetState.takeSkippedKey their counter) r).1,
        { (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 with
          receiverChains := setHeadPubKey spk
            (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.takeSkippedKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, setHeadPubKey, List.findIdx?_cons, hne0, hne_spk,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c =>
        dsimp only []
        cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
        | none => exact ⟨rfl, rest, rfl⟩
        | some pos =>
          dsimp only []
          cases c.messageKeys[pos]? with
          | none => exact ⟨rfl, rest, rfl⟩
          | some key => exact ⟨rfl, rest.set j _, rfl⟩

theorem storeSkippedKey_setHeadPubKey (spk : PublicKey) (their : PublicKey)
    (key : MessageKeyGenerator) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    Mut.exec (RatchetState.storeSkippedKey their key)
      { r with receiverChains := setHeadPubKey spk r.receiverChains } =
      ( (Mut.exec (RatchetState.storeSkippedKey their key) r).1,
        { (Mut.exec (RatchetState.storeSkippedKey their key) r).2 with
          receiverChains := setHeadPubKey spk
            (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.storeSkippedKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, setHeadPubKey, List.findIdx?_cons, hne0, hne_spk,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c => exact ⟨rfl, rest.set j _, rfl⟩

theorem setReceiverChainKey_setHeadPubKey (spk : PublicKey) (their : PublicKey)
    (ck : LibsignalSession.ChainKey) (r : RatchetState) (rc0 : ReceiverChain) (rest :
        List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    Mut.exec (RatchetState.setReceiverChainKey their ck)
      { r with receiverChains := setHeadPubKey spk r.receiverChains } =
      ( (Mut.exec (RatchetState.setReceiverChainKey their ck) r).1,
        { (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 with
          receiverChains := setHeadPubKey spk
            (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.setReceiverChainKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, setHeadPubKey, List.findIdx?_cons, hne0, hne_spk,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c => exact ⟨rfl, rest.set j _, rfl⟩

theorem advanceChain_setHeadPubKey (F : ShaState → List (BitVec 8) → ShaState)
    (spk : PublicKey) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState) (rc0 : ReceiverChain) (rest :
        List ReceiverChain),
      r.receiverChains = rc0 :: rest →
      (rc0.senderRatchetKey == their) = false →
      (spk == their) = false →
      Mut.exec (RatchetState.advanceChain F their counter fuel ck)
        { r with receiverChains := setHeadPubKey spk r.receiverChains } =
        ( (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).1,
          { (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2 with
            receiverChains := setHeadPubKey spk
              (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains } )
                  ∧
      ∃ rest', (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains =
        rc0 :: rest'
  | 0, ck, r, rc0, rest, hrc, _, _ => ⟨rfl, rest, hrc⟩
  | fuel + 1, ck, r, rc0, rest, hrc, hne0, hne_spk => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind]
      rcases storeSkippedKey_setHeadPubKey spk their (ck.messageKeys F) r rc0 rest hrc hne0 hne_spk
        with ⟨hstore, rest1, hrc1⟩
      rw [hstore]
      rcases h_st : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨r_st,
          s_st⟩
      rw [h_st] at hrc1
      cases r_st with
      | error e => exact ⟨rfl, rest1, hrc1⟩
      | ok _ =>
        dsimp only []
        cases ck.nextChainKey F with
        | error e => exact ⟨rfl, rest1, hrc1⟩
        | ok ck' =>
          simp only [Mut_exec_liftE]
          exact advanceChain_setHeadPubKey F spk their counter fuel ck' s_st rc0 rest1 hrc1 hne0
              hne_spk
    · simp only [hlt, ↓reduceIte]
      exact ⟨rfl, rest, hrc⟩

theorem consumeMessageKey_setHeadPubKey (F : ShaState → List (BitVec 8) → ShaState)
    (spk : PublicKey) (their : PublicKey) (ck : LibsignalSession.ChainKey) (counter : BitVec 32)
    (msgType : MessageType) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType)
      { r with receiverChains := setHeadPubKey spk r.receiverChains } =
      ( (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).1,
        { (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2 with
          receiverChains := setHeadPubKey spk
            (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType)
                r).2.receiverChains } ) ∧
    ∃ rest',
        (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains =
      rc0 :: rest' := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind]
    rcases takeSkippedKey_setHeadPubKey spk their counter r rc0 rest hrc hne0 hne_spk with ⟨htake,
        rest1, hrc1⟩
    rw [htake]
    rcases h_tk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨r_tk, s_tk⟩
    rw [h_tk] at hrc1
    cases r_tk with
    | error e => exact ⟨rfl, rest1, hrc1⟩
    | ok optK =>
      cases optK <;> exact ⟨rfl, rest1, hrc1⟩
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get]
    by_cases hj : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte]
      exact ⟨rfl, rest, hrc⟩
    · simp only [hj, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      rcases advanceChain_setHeadPubKey F spk their counter (counter - ck.index).toNat ck r rc0 rest
          hrc hne0 hne_spk
        with ⟨hadv, rest1, hrc1⟩
      rw [hadv]
      rcases h_adv :
          Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨r_adv, s_adv⟩
      rw [h_adv] at hrc1
      cases r_adv with
      | error e => exact ⟨rfl, rest1, hrc1⟩
      | ok ckOut =>
        dsimp only []
        cases ckOut.nextChainKey F with
        | error e => exact ⟨rfl, rest1, hrc1⟩
        | ok ckNext =>
          simp only [Mut_exec_liftE]
          rcases setReceiverChainKey_setHeadPubKey spk their ckNext s_adv rc0 rest1 hrc1 hne0
              hne_spk
            with ⟨hset, rest2, hrc2⟩
          rw [hset]
          rcases h_set :
              Mut.exec (RatchetState.setReceiverChainKey their ckNext) s_adv with ⟨r_set, s_set⟩
          rw [h_set] at hrc2
          cases r_set <;> exact ⟨rfl, rest2, hrc2⟩

theorem Mut_exec_outgoingFromSessionState_pub (spk : PublicKey) (s : SessionState PQ) :
    Mut.exec OutgoingTripleRatchet.fromSessionState
      { s with receiverChains := setHeadPubKey spk s.receiverChains } =
      ( (Mut.exec OutgoingTripleRatchet.fromSessionState s).1,
        { (Mut.exec OutgoingTripleRatchet.fromSessionState s).2 with
          receiverChains := setHeadPubKey spk
            (Mut.exec OutgoingTripleRatchet.fromSessionState s).2.receiverChains } ) := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.version
  simp only [Mut_exec_bind, Mut_exec_get]
  cases hsc : s.senderChain with
  | none => simp [hsc, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_takePqRatchetState
      ]
    by_cases hv : 256 ≤ (if s.sessionVersion = 0 then (2 : BitVec 32) else s.sessionVersion).toNat
    · simp only [hv, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
    · simp only [hv, ↓reduceIte]
      cases s.remoteIdentity <;> rfl

omit [SampleableType PQC] in
theorem messageEncrypt_setHeadPubKey (P : Params PQ PQC) (spk : PublicKey)
    (addr : Option (List (BitVec 8))) (m : List (BitVec 8)) (r : PQC) (s : SessionState PQ) :
    SessionState.messageEncrypt P.C P.codec P.spqr addr m r
      { s with receiverChains := setHeadPubKey spk s.receiverChains } =
      ( (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).1,
        { (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).2 with
          receiverChains := setHeadPubKey spk
            (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).2.receiverChains } ) := by
  unfold SessionState.messageEncrypt SessionState.encryptAddresses
    OutgoingTripleRatchet.applyToSessionState
  simp only [Mut_exec_outgoingFromSessionState_pub]
  rcases Mut.exec OutgoingTripleRatchet.fromSessionState s with ⟨r_out, s_out⟩
  cases r_out with
  | error e => rfl
  | ok o =>
    simp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
      (if s.pendingPreKey then addr else none) r) o with ⟨r_enc, s_enc⟩
    cases r_enc <;> rfl

omit [SampleableType PQC] in
theorem send_setAliceSpkPub_eq (P : Params PQ PQC) (spk : PublicKey) (g : GhostState PQ)
    (m : List (BitVec 8)) (r : PQC) :
    P.send (setAliceSpkPub spk g) m r =
      (setAliceSpkPub spk (P.send g m r).1, (P.send g m r).2) := by
  unfold Params.send setAliceSpkPub
  simp only [messageEncrypt_setHeadPubKey]
  rcases SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨r_enc, s_enc⟩
  cases r_enc <;> rfl

theorem send_patchAlicePub (P : Params PQ PQC) (spk₀ spk : PublicKey)
    (g : GhostState PQ) (m : List (BitVec 8)) (r : PQC) (hinv : AliceInv P spk₀ g) :
    P.send (patchAlicePub spk g) m r =
      (patchAlicePub spk (P.send g m r).1, (P.send g m r).2) ∧
    AliceInv P spk₀ (P.send g m r).1 := by
  have hp := send_preserve_fields P g m r
  refine ⟨?_, (send_patchAlice P 0 spk₀ g m r hinv).2⟩
  unfold patchAlicePub
  rw [hp.2.1]
  split
  · exact send_setAliceSpkPub_eq P spk g m r
  · rfl

theorem dhRatchetStep_setHeadPubKey (C : Crypto) (spk : PublicKey) (their : PublicKey)
    (coins : BitVec 256) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) :
    (Mut.exec (RatchetState.dhRatchetStep C their coins)
      { r with receiverChains := setHeadPubKey spk r.receiverChains }).1 =
      (Mut.exec (RatchetState.dhRatchetStep C their coins) r).1 ∧
    (∀ rck r_ens, Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok rck, r_ens) →
      if (rest.length + 1 + 1) - maxReceiverChains = 0 then
        Mut.exec (RatchetState.dhRatchetStep C their coins)
          { r with receiverChains := setHeadPubKey spk r.receiverChains } =
          (.ok rck, { r_ens with receiverChains := setHeadPubKey spk r_ens.receiverChains }) ∧
        r_ens.receiverChains = rc0 :: (rest ++ [⟨their, some rck, []⟩]) ∧
        r_ens.receiverChains.length = r.receiverChains.length + 1
      else
        Mut.exec (RatchetState.dhRatchetStep C their coins)
          { r with receiverChains := setHeadPubKey spk r.receiverChains } =
          (.ok rck, r_ens) ∧
        r_ens.receiverChains.length < r.receiverChains.length + 1) := by
  unfold RatchetState.dhRatchetStep RatchetState.evictReceiverChains
  cases hsc : r.senderChain with
  | none =>
    simp [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_takeRootKey,
      Mut_exec_liftE, Mut_exec_modify, Mut_exec_pure]
    cases rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error e => simp
    | ok p1 =>
      dsimp only []
      cases rootCreateChain C p1.1 their (KeyPair.generate C coins).privateKey with
      | error e => simp
      | ok p2 =>
        dsimp only []
        refine ⟨rfl, ?_⟩
        intro rck r_ens hok
        injection hok with h1 h2
        injection h1 with hrck
        subst hrck
        subst h2
        simp only [hrc, setHeadPubKey, List.cons_append, List.length_cons, List.length_append
          ]
        cases hd : (rest.length + 1 + 1) - maxReceiverChains with
        | zero =>
          simp []
        | succ k =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, List.drop_succ_cons, List.length_drop,
            List.length_append, List.length_singleton]
          exact ⟨trivial, by omega⟩

theorem ratchetDecryptStep_setHeadPubKey (C : Crypto) (spk : PublicKey) (their : PublicKey)
    (counter : BitVec 32) (msgType : MessageType) (coins : BitVec 256)
    (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest)
    (hne0 : (rc0.senderRatchetKey == their) = false)
    (hne_spk : (spk == their) = false) :
    (Mut.exec (ratchetDecryptStep C their counter msgType coins)
      { r with receiverChains := setHeadPubKey spk r.receiverChains }).1 =
      (Mut.exec (ratchetDecryptStep C their counter msgType coins) r).1 ∧
    (∀ gen r', Mut.exec (ratchetDecryptStep C their counter msgType coins) r = (.ok gen, r') →
      (∀ idx, r.findReceiverChainIndex their = some idx →
        Mut.exec (ratchetDecryptStep C their counter msgType coins)
          { r with receiverChains := setHeadPubKey spk r.receiverChains } =
          (.ok gen, { r' with receiverChains := setHeadPubKey spk r'.receiverChains }) ∧
        r'.receiverChains.length = r.receiverChains.length ∧
        (∃ j, idx = j + 1 ∧ j < rest.length) ∧
        ∃ rest', r'.receiverChains = rc0 :: rest') ∧
      (r.findReceiverChainIndex their = none →
        if (rest.length + 1 + 1) - maxReceiverChains = 0 then
          Mut.exec (ratchetDecryptStep C their counter msgType coins)
            { r with receiverChains := setHeadPubKey spk r.receiverChains } =
            (.ok gen, { r' with receiverChains := setHeadPubKey spk r'.receiverChains }) ∧
          r'.receiverChains.length = r.receiverChains.length + 1 ∧
          ∃ rest', r'.receiverChains = rc0 :: rest'
        else
          Mut.exec (ratchetDecryptStep C their counter msgType coins)
            { r with receiverChains := setHeadPubKey spk r.receiverChains } =
            (.ok gen, r') ∧
          r'.receiverChains.length < r.receiverChains.length + 1)) := by
  unfold ratchetDecryptStep RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
  have hidx_eq : ({ r with
                    receiverChains :=
                    setHeadPubKey spk r.receiverChains }).findReceiverChainIndex their =
      r.findReceiverChainIndex their := by
    unfold RatchetState.findReceiverChainIndex
    rw [hrc]
    exact findIdx?_setHeadPubKey spk rc0 rest their hne0 hne_spk
  have hidx_val : r.findReceiverChainIndex their =
      Option.map Nat.succ (rest.findIdx? (fun c => c.senderRatchetKey == their)) := by
    unfold RatchetState.findReceiverChainIndex
    simp [hrc, List.findIdx?_cons, hne0]
  simp only [Mut_exec_bind, Mut_exec_liftE, Mut_exec_get, hidx_eq, hidx_val]
  cases hfind : rest.findIdx? (fun c => c.senderRatchetKey == their) with
  | some j =>
    have hget_succ : (setHeadPubKey spk r.receiverChains)[j + 1]? = rest[j]? := by
      simp [hrc, setHeadPubKey]
    have hget_r : r.receiverChains[j + 1]? = rest[j]? := by
      simp [hrc]
    simp only [Option.map_some, hget_succ, hget_r]
    cases hc : rest[j]? with
    | none => simp []
    | some c =>
      cases hck : c.chainKey with
      | none => simp [hck]
      | some ck =>
        simp only [hck, Mut_exec_pure]
        have hcmk :=
            consumeMessageKey_setHeadPubKey C.F spk their ck counter msgType r rc0 rest hrc hne0
            hne_spk
        have hlen := consumeMessageKey_length C.F their ck counter msgType r
        refine ⟨by rw [hcmk.1], ?_⟩
        intro gen r' hok
        refine ⟨fun idx hidx => ⟨by rw [hcmk.1, hok], ?_, ?_, ?_⟩, by simp⟩
        · rw [hok] at hlen; exact hlen
        · exact ⟨j, (Option.some.inj hidx).symm, (List.getElem?_eq_some_iff.mp hc).1⟩
        · rcases hcmk.2 with ⟨rest', hrest'⟩
          rw [hok] at hrest'
          exact ⟨rest', hrest'⟩
  | none =>
    simp only [Option.map_none]
    have hdh := dhRatchetStep_setHeadPubKey C spk their coins r rc0 rest hrc
    rcases h_dh : Mut.exec (RatchetState.dhRatchetStep C their coins) r with ⟨r_dh, s_dh⟩
    rw [h_dh] at hdh
    cases r_dh with
    | error e =>
      rcases h_dh1 : Mut.exec (RatchetState.dhRatchetStep C their coins)
        { r with receiverChains := setHeadPubKey spk r.receiverChains } with ⟨r_dh1, s_dh1⟩
      have herr : r_dh1 = .error e := by
        have h1 := hdh.1
        rw [h_dh1] at h1
        exact h1
      subst herr
      simp
    | ok rck =>
      have h2 := hdh.2 rck s_dh rfl
      by_cases hd : (rest.length + 1 + 1) - maxReceiverChains = 0
      · simp only [hd, ↓reduceIte] at h2
        rcases h2 with ⟨hdh1, hrc_dh, hlen_dh⟩
        rw [hdh1]
        dsimp only []
        have hcmk := consumeMessageKey_setHeadPubKey C.F spk their rck counter msgType s_dh rc0
          (rest ++ [⟨their, some rck, []⟩]) hrc_dh hne0 hne_spk
        have hlen := consumeMessageKey_length C.F their rck counter msgType s_dh
        refine ⟨by rw [hcmk.1], ?_⟩
        intro gen r' hok
        refine ⟨by simp, fun _ => ?_⟩
        simp only [hd, ↓reduceIte]
        refine ⟨by rw [hcmk.1, hok], ?_, ?_⟩
        · rw [hok] at hlen; exact hlen.trans hlen_dh
        · rcases hcmk.2 with ⟨rest', hrest'⟩
          rw [hok] at hrest'
          exact ⟨rest', hrest'⟩
      · simp only [hd, ↓reduceIte] at h2
        rcases h2 with ⟨hdh1, hlen_dh⟩
        rw [hdh1]
        dsimp only []
        have hlen := consumeMessageKey_length C.F their rck counter msgType s_dh
        refine ⟨rfl, ?_⟩
        intro gen r' hok
        refine ⟨by simp, fun _ => ?_⟩
        simp only [hd, ↓reduceIte]
        rw [hok] at hlen ⊢
        exact ⟨rfl, hlen.symm ▸ hlen_dh⟩

theorem AliceInv_receive_noZero_pub (P : Params PQ PQC) (spk₀ spk : PublicKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (hparty : g.party = .A) (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (hlen : g.chainEpochs.length = g.session.receiverChains.length)
    (hno0 : 0 ∉ g.chainEpochs) (hpos : ∀ e ∈ g.chainEpochs, 0 < e) :
    P.receive (patchAlicePub spk g) c rc =
      (P.receive g c rc).map (fun x => (patchAlicePub spk x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk₀ g' ∧ 0 < t := by
  have hpatch_g : patchAlicePub spk g = g := by unfold patchAlicePub; simp [hno0]
  have hmain : ∀ g' t i m, P.receive g c rc = some (g', t, i, m) →
      0 ∉ g'.chainEpochs ∧ AliceInv P spk₀ g' ∧ 0 < t := by
    intro g' t i m hrecv
    obtain ⟨hp, hrem', hloc', hlen', hno0', hpos', ht_pos, _⟩ :=
      receive_noZero_props P P.idB g c rc hrem hlen hpos g' t i m hrecv
    exact ⟨hno0', ⟨hp.trans hparty, hrem', hloc'.trans hloc, hlen', Or.inl ⟨hno0', hpos'⟩⟩, ht_pos⟩
  refine ⟨?_, fun g' t i m h => ⟨(hmain g' t i m h).2.1, (hmain g' t i m h).2.2⟩⟩
  rw [hpatch_g]
  cases h : P.receive g c rc with
  | none => rfl
  | some val =>
    rcases val with ⟨g', t, i, m⟩
    have h0 := (hmain g' t i m h).1
    simp only [Option.map_some, patchAlicePub, h0, ↓reduceIte]

theorem AliceInv_receive_hasZero_pub (P : Params PQ PQC) (spk₀ spk : PublicKey)
    (g : GhostState PQ) (rest : List ReceiverChain) (epochsTail : List ℕ)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (hparty : g.party = .A) (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (hlen : g.chainEpochs.length = g.session.receiverChains.length)
    (hrc : g.session.receiverChains = ⟨spk₀, some ⟨0, 0⟩, []⟩ :: rest)
    (hep : g.chainEpochs = 0 :: epochsTail) (hpos : ∀ e ∈ epochsTail, 0 < e)
    (hmsg0 : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → (spk₀ == msg.senderRatchetKey) =
        false)
    (hmsg_spk : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → (spk == msg.senderRatchetKey) =
        false) :
    P.receive (patchAlicePub spk g) c rc =
      (P.receive g c rc).map (fun x => (patchAlicePub spk x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk₀ g' ∧ 0 < t := by
  have hpatch_g : patchAlicePub spk g = setAliceSpkPub spk g := by
    unfold patchAlicePub; simp [hep]
  refine ⟨?_,
      (AliceInv_receive_hasZero P 0 spk₀ g rest epochsTail c rc hparty hrem hloc hlen hrc hep hpos
      hmsg0).2⟩
  rw [hpatch_g]
  unfold Params.receive
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp
  | ok msg =>
    dsimp only [setAliceSpkPub]
    have hne0 : ((⟨spk₀, some ⟨0, 0⟩, []⟩ :
        ReceiverChain).senderRatchetKey == msg.senderRatchetKey) = false :=
      hmsg0 msg htry
    have hne_spk : (spk == msg.senderRatchetKey) = false := hmsg_spk msg htry
    have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
      { g.session with receiverChains := setHeadPubKey spk g.session.receiverChains }
    have hdec2 :=
        tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session
    have hver : ({ g.session with
                   receiverChains := setHeadPubKey spk g.session.receiverChains } :
                   SessionState PQ).version =
        g.session.version := rfl
    have hrem1 : ({ g.session with
                    receiverChains := setHeadPubKey spk g.session.receiverChains } :
                    SessionState PQ).remoteIdentity =
        some P.idB := hrem
    rw [hver, hrem1] at hdec1
    rw [hrem] at hdec2
    by_cases hv : g.session.version.toNat = msg.messageVersion.toNat
    · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec1 hdec2
      have hrat_step := ratchetDecryptStep_setHeadPubKey P.C spk msg.senderRatchetKey
        msg.counter .whisper rc
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩
        ⟨spk₀, some ⟨0, 0⟩, []⟩ rest hrc hne0 hne_spk
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat, r'⟩
      rw [hrat] at hdec2
      cases r_rat with
      | error e =>
        rcases hrat1 :
            Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          ⟨g.session.rootKey, g.session.senderChain, setHeadPubKey spk g.session.receiverChains,
           g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat1, r1'⟩
        have herr : r_rat1 = .error e := by
          have h1 := hrat_step.1
          rw [hrat, hrat1] at h1
          exact h1
        subst herr
        rw [hrat1] at hdec1
        rw [hdec1, hdec2]; simp
      | ok gen =>
        dsimp only [] at hdec2
        have hstep := hrat_step.2 gen r' hrat
        have hidx_eq :
            (setHeadPubKey spk g.session.receiverChains).findIdx? (·.senderRatchetKey ==
            msg.senderRatchetKey) =
            g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) := by
          rw [hrc]
          exact findIdx?_setHeadPubKey spk ⟨spk₀, some ⟨0, 0⟩,
              []⟩ rest msg.senderRatchetKey hne0 hne_spk
        cases hidx :
            g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
        | some idx =>
          rcases hstep.1 idx hidx with ⟨hrat1, hlen_r', ⟨j, rfl, hj⟩, rest', hrc_r'⟩
          dsimp only [] at hrat1
          rw [hrat1] at hdec1
          dsimp only [] at hdec1
          have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
            msg .whisper g.session P.idB gen r'
            (setHeadPubKey spk g.session.receiverChains) (setHeadPubKey spk r'.receiverChains)
          rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            g.session P.idB gen r' with ⟨r_post, s⟩
          rw [hp] at hdec2 hpost
          cases r_post with
          | error e =>
            rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              { g.session with receiverChains := setHeadPubKey spk g.session.receiverChains }
              P.idB gen { r' with receiverChains := setHeadPubKey spk r'.receiverChains }
              with ⟨r_post1, s1⟩
            rw [hp1] at hpost hdec1
            have herr : r_post1 = .error e := hpost.1
            subst herr
            rw [hdec1, hdec2]; simp
          | ok ptext =>
            rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
            rw [hp1] at hdec1
            rw [hdec1, hdec2]
            dsimp only []
            rw [hidx_eq, hidx]
            dsimp only []
            have hlen_s1 : (setHeadPubKey spk r'.receiverChains).length = g.chainEpochs.length := by
              rw [length_setHeadPubKey, hlen_r', hlen]
            have hlen_s2 : s.receiverChains.length = g.chainEpochs.length := by
              rw [hs_rc, hlen_r', hlen]
            have hdrop1 : g.chainEpochs.length - (setHeadPubKey spk r'.receiverChains).length =
                0 := by omega
            have hdrop2 : g.chainEpochs.length - s.receiverChains.length = 0 := by omega
            simp only [hdrop1, hdrop2, List.drop_zero]
            have h0_mem : 0 ∈ g.chainEpochs := by simp [hep]
            simp only [Option.map_some, patchAlicePub, h0_mem, ↓reduceIte, setAliceSpkPub, hs_rc]
        | none =>
          have hstep_none := hstep.2 hidx
          by_cases hd : (rest.length + 1 + 1) - maxReceiverChains = 0
          · simp only [hd, ↓reduceIte] at hstep_none
            rcases hstep_none with ⟨hrat1, hlen_r', rest', hrc_r'⟩
            rw [hrat1] at hdec1
            dsimp only [] at hdec1
            have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper g.session P.idB gen r'
              (setHeadPubKey spk g.session.receiverChains) (setHeadPubKey spk r'.receiverChains)
            rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session P.idB gen r' with ⟨r_post, s⟩
            rw [hp] at hdec2 hpost
            cases r_post with
            | error e =>
              rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                { g.session with receiverChains := setHeadPubKey spk g.session.receiverChains }
                P.idB gen { r' with receiverChains := setHeadPubKey spk r'.receiverChains }
                with ⟨r_post1, s1⟩
              rw [hp1] at hpost hdec1
              have herr : r_post1 = .error e := hpost.1
              subst herr
              rw [hdec1, hdec2]; simp
            | ok ptext =>
              rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
              rw [hp1] at hdec1
              rw [hdec1, hdec2]
              dsimp only []
              rw [hidx_eq, hidx]
              dsimp only []
              have hlen_s1 : (setHeadPubKey spk r'.receiverChains).length =
                  (g.chainEpochs ++ [g.epoch + 1]).length := by
                rw [length_setHeadPubKey, List.length_append, List.length_singleton, hlen_r', hlen]
              have hlen_s2 : s.receiverChains.length = (g.chainEpochs ++ [g.epoch + 1]).length := by
                rw [hs_rc, List.length_append, List.length_singleton, hlen_r', hlen]
              have hdrop1 : (g.chainEpochs ++ [g.epoch + 1]).length -
                  (setHeadPubKey spk r'.receiverChains).length = 0 := by omega
              have hdrop2 : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length =
                  0 := by omega
              simp only [hdrop1, hdrop2, List.drop_zero]
              have h0_mem : 0 ∈ g.chainEpochs ++ [g.epoch + 1] := by simp [hep]
              simp only [Option.map_some, patchAlicePub, h0_mem, ↓reduceIte, setAliceSpkPub, hs_rc]
          · simp only [hd, ↓reduceIte] at hstep_none
            rcases hstep_none with ⟨hrat1, hlen_r'⟩
            rw [hrat1] at hdec1
            dsimp only [] at hdec1
            have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper g.session P.idB gen r'
              (setHeadPubKey spk g.session.receiverChains) r'.receiverChains
            rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session P.idB gen r' with ⟨r_post, s⟩
            rw [hp] at hdec2 hpost
            cases r_post with
            | error e =>
              rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                { g.session with receiverChains := setHeadPubKey spk g.session.receiverChains }
                P.idB gen r' with ⟨r_post1, s1⟩
              rw [hp1] at hpost hdec1
              have herr : r_post1 = .error e := hpost.1
              subst herr
              rw [hdec1, hdec2]; simp
            | ok ptext =>
              rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
              have hs_eq : { s with receiverChains := r'.receiverChains } = s := by
                cases s; congr 1; exact hs_rc.symm
              rw [hs_eq] at hp1
              rw [hp1] at hdec1
              rw [hdec1, hdec2]
              dsimp only []
              rw [hidx_eq, hidx]
              dsimp only []
              have hdrop_pos : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length =
                  ((epochsTail ++ [g.epoch + 1]).length - s.receiverChains.length) + 1 := by
                rw [hep, hs_rc]
                simp only [List.cons_append, List.length_cons, List.length_append
                    ] at hlen_r' ⊢
                have hlen_eq : epochsTail.length + 1 = g.session.receiverChains.length := by
                  rw [← List.length_cons (a := 0), ← hep, hlen]
                omega
              have hpos_drop : ∀ e ∈ (g.chainEpochs ++ [g.epoch + 1]).drop
                  ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length), 0 < e := by
                rw [hdrop_pos, hep, List.cons_append, List.drop_succ_cons]
                intro e he
                have hmem := mem_of_mem_drop _ _ _ he
                rw [List.mem_append, List.mem_singleton] at hmem
                rcases hmem with hmem | rfl
                · exact hpos e hmem
                · omega
              have hno0_drop : 0 ∉ (g.chainEpochs ++ [g.epoch + 1]).drop
                  ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length) := by
                intro h0; have := hpos_drop 0 h0; omega
              simp only [Option.map_some, patchAlicePub, hno0_drop, ↓reduceIte]
    · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec1 hdec2
      rw [hdec1, hdec2]; simp

theorem receive_patchAlicePub_nonSpk (P : Params PQ PQC) (spk₀ spk : PublicKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : AliceInv P spk₀ g)
    (hnonSpk : 0 ∉ g.chainEpochs ∨
      ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg →
        (spk₀ == msg.senderRatchetKey) = false ∧ (spk == msg.senderRatchetKey) = false) :
    P.receive (patchAlicePub spk g) c rc =
      (P.receive g c rc).map (fun x => (patchAlicePub spk x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk₀ g' ∧ 0 < t := by
  rcases hinv with ⟨hparty, hrem, hloc, hlen, hcases⟩
  rcases hcases with ⟨hno0, hpos⟩ | ⟨rest, epochsTail, hrc, hep, hpos⟩
  · exact AliceInv_receive_noZero_pub P spk₀ spk g c rc hparty hrem hloc hlen hno0 hpos
  · rcases hnonSpk with hno0 | hmsg
    · exfalso; apply hno0; simp [hep]
    · exact AliceInv_receive_hasZero_pub P spk₀ spk g rest epochsTail c rc hparty hrem hloc hlen hrc
        hep hpos
        (fun msg h => (hmsg msg h).1) (fun msg h => (hmsg msg h).2)

/-! ### Full game-state SPK patching -/

def patchPartyPub (spk : PublicKey) (kp : KeyPair) : Party → GhostState PQ → GhostState PQ
  | .A => patchAlicePub spk
  | .B => patchBobSpk kp 0

def patchGamePub (C : Crypto) (x : BitVec 256) (s : GameSt PQ ℓ) : GameSt PQ ℓ :=
  { s with st := fun p => match p with
      | .A => patchAlicePub (KeyPair.generate C x).publicKey (s.st .A)
      | .B => patchBobSpk (KeyPair.generate C x) 0 (s.st .B) }

/-- Patches both `(KeyPair.generate C x)` and `ck0` across the game state. -/
def patchGameSpk (C : Crypto) (x ck0 : BitVec 256) (s : GameSt PQ ℓ) : GameSt PQ ℓ :=
  patchGameState ck0 (patchGamePub C x s)

omit [Inhabited PQ] in
theorem patchAlicePub_chainEpochs (spk : PublicKey) (g : GhostState PQ) :
    (patchAlicePub spk g).chainEpochs = g.chainEpochs := by
  unfold patchAlicePub setAliceSpkPub
  split <;> rfl

omit [Inhabited PQ] in
theorem patchBob_patchBobSpk_zero (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState PQ) :
    patchBob ck0 (patchBobSpk kp 0 g) = patchBobSpk kp ck0 g := by
  unfold patchBob patchBobSpk setBobSenderKey setBobSpk
  by_cases h : g.epoch = 0
  · simp [h]
    cases g.session.senderChain <;> rfl
  · simp [h]

omit [Inhabited PQ] in
@[simp]
theorem patchGameSpk_st_A (C : Crypto) (x ck0 : BitVec 256) (s : GameSt PQ ℓ) :
    (patchGameSpk C x ck0 s).st .A =
      patchAlice ck0 (patchAlicePub (KeyPair.generate C x).publicKey (s.st .A)) :=
  rfl

omit [Inhabited PQ] in
@[simp]
theorem patchGameSpk_st_B (C : Crypto) (x ck0 : BitVec 256) (s : GameSt PQ ℓ) :
    (patchGameSpk C x ck0 s).st .B =
      patchBobSpk (KeyPair.generate C x) ck0 (s.st .B) :=
  patchBob_patchBobSpk_zero (KeyPair.generate C x) ck0 (s.st .B)

omit [Inhabited PQ] [SampleableType PQC] in
theorem aliceInv_patchAlicePub (P : Params PQ PQC) (spk₀ spk : PublicKey) (g : GhostState PQ)
    (hinv : AliceInv P spk₀ g) :
    AliceInv P spk (patchAlicePub spk g) := by
  rcases hinv with ⟨hp, hrem, hloc, hlen, ⟨hno0, hpos⟩ | ⟨rest, epochsTail, hrc, hep, hpos⟩⟩
  · unfold patchAlicePub
    simp only [hno0, ↓reduceIte]
    exact ⟨hp, hrem, hloc, hlen, Or.inl ⟨hno0, hpos⟩⟩
  · have h0 : 0 ∈ g.chainEpochs := by simp [hep]
    unfold patchAlicePub setAliceSpkPub
    simp only [h0, ↓reduceIte]
    refine ⟨hp, hrem, hloc, ?_, Or.inr ⟨rest, epochsTail, ?_, hep, hpos⟩⟩
    · rw [length_setHeadPubKey]; exact hlen
    · simp [hrc, setHeadPubKey]

omit [Inhabited PQ] [SampleableType PQC] in
theorem bobInv_patchBobSpk (P : Params PQ PQC) (s_ep : ℕ) (kp : KeyPair) (g : GhostState PQ)
    (hinv : BobInv P s_ep g) :
    BobInv P s_ep (patchBobSpk kp 0 g) := by
  rcases hinv with ⟨hrem, hlen, hpos, h0⟩
  by_cases hep : g.epoch = 0
  · obtain ⟨hsep, hrc, _hidx⟩ := h0 hep
    unfold patchBobSpk setBobSpk
    simp only [hep, ↓reduceIte]
    refine ⟨hrem, hlen, hpos, fun _ => ⟨hsep, hrc, ?_⟩⟩
    intro sc hsc
    simp only [Option.mem_def, Option.map_eq_some_iff] at hsc
    rcases hsc with ⟨_, _, rfl⟩
    rfl
  · unfold patchBobSpk
    simp only [hep, ↓reduceIte]
    exact ⟨hrem, hlen, hpos, h0⟩

omit [Inhabited PQ] [SampleableType PQC] in
theorem gameInv_patchGamePub (P : Params PQ PQC) (spk₀ : PublicKey) (x : BitVec 256)
    (s : GameSt PQ ℓ) (hinv : GameInv P spk₀ s) :
    GameInv P (KeyPair.generate P.C x).publicKey (patchGamePub P.C x s) :=
  ⟨aliceInv_patchAlicePub P spk₀ (KeyPair.generate P.C x).publicKey (s.st .A) hinv.1,
   bobInv_patchBobSpk P (s.epoch .B) (KeyPair.generate P.C x) (s.st .B) hinv.2.1,
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2⟩

/-! ### Oracle step lemmas -/

theorem spkForgeTerm_eq_mul_eps0IdealUnit (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) :
    epoch0ChainForgeryTerm F q = q * eps0IdealUnit F :=
  rfl

def prfOracleImpl {Key : Type} (mac : MACScheme Key Pt (BitVec 256)) :
    QueryImpl (unifSpec + prfSpec Pt (BitVec 256))
      (StateT (PRFState Key Pt (BitVec 256)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (PRFState Key Pt (BitVec 256)) ProbComp) + MACScheme.prfEval mac

omit [Zero Pt] [SampleableType Pt] in
@[local simp]
theorem simulateQ_prfOracleImpl_evalQuery {Key : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (y : Pt) :
    simulateQ (prfOracleImpl mac) (evalQuery y) = MACScheme.prfEval mac y := by
  simp [evalQuery, prfOracleImpl]

def initARef (P : Params Bytes PQC) (s prk alice pqr : BitVec 256) : GhostState Bytes :=
  let (rk1, ck1) := (expandPRG P.C.F).gen prk
  let spk := (KeyPair.generate P.C s).publicKey
  let sendingRatchetKey := KeyPair.generate P.C alice
  let sess := ((SessionState.new currentVersion P.idA P.idB rk1
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨0, 0⟩).setSenderChain
    sendingRatchetKey ⟨ck1, 0⟩
  ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩

/-- Reference initial `GameState` after `initAOracle` receives `prk`, with `s` and `ck0 = 0`. -/
def initGameSpkRef (P : Params Bytes PQC) (ℓ : ℕ) (b : Bool) (s prk alice pqr : BitVec 256) :
    GameSt Bytes ℓ :=
  { st := fun Q => match Q with
      | .A => initARef P s prk alice pqr
      | .B => P.initB ⟨0, 0, s, alice, pqr⟩,
    b := b }

omit [Zero Pt] [SampleableType Pt] in
theorem initAOracle_true_tableFor_bind {Key α : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P_pt P' : Pt), Dh.dh x P_pt = Dh.dh x P' ↔ Dh.dh s P_pt =
        Dh.dh s P')
    (key : Key) (ck0 x alice pqr : BitVec 256) (L : List (Pt × BitVec 256))
    (F : GhostState Bytes × PRFState Key Pt (BitVec 256) → ProbComp α) :
    ((simulateQ (prfOracleImpl mac) (initAOracle P Dh ck0 x alice pqr)).run
        ⟨key, true, tableFor Dh x L⟩ >>= F) =
      (stepTableFor Dh s (Dh.dh alice Dh.base) L >>= fun r =>
        F (patchAlice ck0 (patchAlicePub (KeyPair.generate P.C x).publicKey
            (initARef P s r.1 alice pqr)),
           ⟨key, true, tableFor Dh x r.2⟩)) := by
  unfold initAOracle
  simp only [simulateQ_bind, simulateQ_prfOracleImpl_evalQuery, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [prfEval_true_tableFor_bind mac Dh s hker key x (Dh.dh alice Dh.base) L]
  exact rfl

theorem initGameSpk_eq_patchGameSpk (P : Params Bytes PQC) (ℓ : ℕ) (b : Bool)
    (s prk ck0 x alice pqr : BitVec 256) :
    ({ st := fun Q => match Q with
        | .A => patchAlice ck0 (patchAlicePub (KeyPair.generate P.C x).publicKey
            (initARef P s prk alice pqr))
        | .B => P.initB ⟨0, ck0, x, alice, pqr⟩,
       b := b } : GameSt Bytes ℓ) =
      patchGameSpk P.C x ck0 (initGameSpkRef P ℓ b s prk alice pqr) := by
  unfold patchGameSpk patchGameState patchGamePub initGameSpkRef
  congr 1

theorem gameInv_initGameSpkRef (P : Params Bytes PQC) (ℓ : ℕ) (b : Bool)
    (s prk alice pqr : BitVec 256) :
    GameInv P (KeyPair.generate P.C s).publicKey (initGameSpkRef P ℓ b s prk alice pqr) := by
  refine ⟨?_, ?_, rfl, rfl, by simp [initGameSpkRef]⟩
  · refine ⟨rfl, rfl, rfl, rfl, Or.inr ⟨[], [], rfl, rfl, by simp⟩⟩
  · refine ⟨rfl, rfl, by simp [initGameSpkRef, Params.initB], fun _ => ⟨rfl, rfl, ?_⟩⟩
    intro sc hsc
    dsimp only [initGameSpkRef, Params.initB, initializeRecipientSession,
      SessionState.new, SessionState.setSenderChain] at hsc
    injection hsc with hsc
    subst hsc
    rfl

def receiveB0Post (P : Params Bytes PQC) (ℓ : ℕ)
    (g : GhostState Bytes) (msg : SignalMessage) (rc prk : BitVec 256) :
    Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) :=
  let (rk1, ck1) := (expandPRG P.C.F).gen prk
  match rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | .error _ => none
  | .ok (rk2, ck2) =>
    let sess' : SessionState Bytes :=
      { g.session with
        previousCounter := 0
        rootKey := rk2
        receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
        senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
    match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc sess'
        with
    | (.error _, _) => none
    | (.ok m, s_out) =>
      let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
      some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
        1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m)

def stepReceiveB0 (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (L : List (Pt × BitVec 256)) :
    ProbComp (Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × List (Pt × BitVec 256)) := do
  match SignalMessage.tryFrom P.codec c with
  | .error _ => return (none, L)
  | .ok msg =>
    match decT msg.senderRatchetKey with
    | none => return (none, L)
    | some T =>
      if T = 0 ∨ encT T ≠ msg.senderRatchetKey then
        return (none, L)
      else
        let r ← stepTableFor Dh s T L
        return (receiveB0Post P ℓ g msg rc r.1, r.2)

omit [SampleableType Pt] in
theorem receiveB0_eq_bind_receiveB0Post (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (x : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) :
    receiveB0 P ℓ Dh encT decT x g c rc =
      match SignalMessage.tryFrom P.codec c with
      | .error _ => pure none
      | .ok msg =>
        match decT msg.senderRatchetKey with
        | none => pure none
        | some T =>
          if T = 0 ∨ encT T ≠ msg.senderRatchetKey then
            pure none
          else do
            let prk ← evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh x T)
            return receiveB0Post P ℓ g msg rc prk := by
  unfold receiveB0 receiveB0Post
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only []
    cases decT msg.senderRatchetKey with
    | none => rfl
    | some T =>
      dsimp only []
      split
      · rfl
      · refine bind_congr fun prk => ?_
        cases rootCreateChain P.C ((expandPRG P.C.F).gen prk).1 msg.senderRatchetKey
          (KeyPair.generate P.C rc).privateKey with
        | error _ => rfl
        | ok rkck =>
          rcases rkck with ⟨rk2, ck2⟩
          dsimp only []
          cases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc _
              with
          | mk res s_out => cases res <;> rfl

theorem receiveB0Post_preserves_BobInv (P : Params Bytes PQC) (ℓ : ℕ)
    (s_ep : ℕ) (g : GhostState Bytes) (msg : SignalMessage) (rc prk : BitVec 256)
    (g' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hinv : BobInv P s_ep g)
    (hpost_eq : receiveB0Post P ℓ g msg rc prk = some (g', t', i', m')) :
    (∀ s_ep', BobInv P s_ep' g') ∧ t' = 1 ∧ g'.epoch = 1 ∧
    ∀ kp ck0, patchBobSpk kp ck0 g' = g' ∧ patchBob ck0 g' = g' := by
  unfold receiveB0Post at hpost_eq
  dsimp only [] at hpost_eq
  cases hrc : rootCreateChain P.C ((expandPRG P.C.F).gen prk).1 msg.senderRatchetKey
    (KeyPair.generate P.C rc).privateKey with
  | error _ => rw [hrc] at hpost_eq; simp at hpost_eq
  | ok rkck =>
    rcases rkck with ⟨rk2, ck2⟩
    rw [hrc] at hpost_eq
    dsimp only [] at hpost_eq
    let sess' : SessionState Bytes :=
      { g.session with
        previousCounter := 0
        rootKey := rk2
        receiverChains := [⟨msg.senderRatchetKey, some ⟨((expandPRG P.C.F).gen prk).2, 0⟩, []⟩]
        senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
    have hdec := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs .B) msg .whisper rc sess'
    have hrem : sess'.remoteIdentity = some P.idA := hinv.1
    rw [hrem] at hdec
    rcases htry_dec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
      msg .whisper rc sess' with ⟨res_dec, s_out⟩
    rw [htry_dec] at hpost_eq hdec
    cases res_dec with
    | error _ => simp at hpost_eq
    | ok m_plain =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hpost_eq
      rcases hpost_eq with ⟨hg', ht', _, _⟩
      subst hg' ht'
      by_cases hv : sess'.version.toNat = msg.messageVersion.toNat
      · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec
        rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          ⟨sess'.rootKey, sess'.senderChain, sess'.receiverChains,
           sess'.previousCounter, maxForwardJumps⟩ with ⟨r_rat, r'⟩
        rw [hrat] at hdec
        cases r_rat with
        | error _ => simp at hdec
        | ok gen =>
          dsimp only [] at hdec
          have hpost := (postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs .B)
            msg .whisper sess' P.idA gen r' sess'.receiverChains r'.receiverChains).2
          rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs .B) msg .whisper
            sess' P.idA gen r' with ⟨r_post, s_post⟩
          rw [hp] at hdec
          cases r_post with
          | error _ => simp at hdec
          | ok ptext =>
            injection hdec with _ hs_out
            subst hs_out
            have hfields := (hpost ptext s_out hp).2
            have hrat_len := ratchetDecryptStep_length P.C msg.senderRatchetKey msg.counter
              .whisper rc _ r' gen hrat
            have hfind0 : (RatchetState.mk sess'.rootKey sess'.senderChain
                sess'.receiverChains sess'.previousCounter maxForwardJumps).findReceiverChainIndex
                  msg.senderRatchetKey = some 0 := by
              unfold RatchetState.findReceiverChainIndex
              simp [sess']
            have hlen_r' : r'.receiverChains.length = 1 := (hrat_len.1 0 hfind0).1
            have hlen_sout : s_out.receiverChains.length = 1 := by rw [hfields.2.2, hlen_r']
            refine ⟨fun _ => ⟨hfields.1.trans hrem, ?_, ?_, fun h0 => by contradiction⟩,
              rfl, rfl, fun kp ck0 => ⟨rfl, rfl⟩⟩
            · simp [hlen_sout]
            · intro e he
              have hmem_e := mem_of_mem_drop _ _ _ he
              simp only [List.mem_singleton] at hmem_e
              omega
      · simp [hv] at hdec

omit [Inhabited PQ] in
theorem patchGamePub_epMgmt (C : Crypto) (x : BitVec 256)
    (s : GameSt PQ ℓ) (Δ qep : ℕ) (Q : Party) (bad : Bool) :
    (patchGamePub C x s).epMgmt Δ qep Q bad =
      (s.epMgmt Δ qep Q bad).map (patchGamePub C x) := by
  unfold GameState.epMgmt GameState.safeCh GameState.leak patchGamePub
  dsimp only []
  split
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl

theorem patchGameSpk_epMgmt (C : Crypto) (x ck0 : BitVec 256)
    (s : GameSt PQ ℓ) (Δ qep : ℕ) (Q : Party) (bad : Bool) :
    (patchGameSpk C x ck0 s).epMgmt Δ qep Q bad =
      (s.epMgmt Δ qep Q bad).map (patchGameSpk C x ck0) := by
  unfold patchGameSpk
  rw [patchGameState_epMgmt, patchGamePub_epMgmt, Option.map_map]
  rfl

omit [Inhabited PQ] in
theorem patchGamePub_record (C : Crypto) (x : BitVec 256)
    (s : GameSt PQ ℓ) (Δ : ℕ) (Q : Party)
    (st' : GhostState PQ) (r : Record (Plain ℓ) (List (BitVec 8))) (isChall : Bool) :
    (patchGamePub C x s).record Δ Q
      (patchPartyPub (KeyPair.generate C x).publicKey (KeyPair.generate C x) Q st') r isChall =
      patchGamePub C x (s.record Δ Q st' r isChall) := by
  unfold GameState.record GameState.safeCh patchGamePub patchPartyPub
  dsimp only []
  congr 1
  funext p
  cases Q <;> cases p <;> rfl

omit [Inhabited PQ] in
theorem patchGamePub_accept (C : Crypto) (x : BitVec 256)
    (s : GameSt PQ ℓ) (Q : Party) (st' : GhostState PQ) (pos : Pos) :
    (patchGamePub C x s).accept Q
      (patchPartyPub (KeyPair.generate C x).publicKey (KeyPair.generate C x) Q st') pos =
      patchGamePub C x (s.accept Q st' pos) := by
  unfold GameState.accept GameState.delete patchGamePub patchPartyPub
  dsimp only []
  congr 1
  funext p
  cases Q <;> cases p <;> rfl

theorem patchGameSpk_accept (C : Crypto) (x ck0 : BitVec 256)
    (s : GameSt PQ ℓ) (Q : Party) (st' : GhostState PQ) (pos : Pos) :
    (patchGameSpk C x ck0 s).accept Q
      (patchParty ck0 Q (patchPartyPub (KeyPair.generate C x).publicKey (KeyPair.generate C x) Q
          st')) pos =
      patchGameSpk C x ck0 (s.accept Q st' pos) := by
  unfold patchGameSpk
  rw [patchGameState_accept, patchGamePub_accept]

omit [Inhabited PQ] in
theorem patchGameSpk_afterCorr (C : Crypto) (x ck0 : BitVec 256) (sRef : GameSt PQ ℓ) (Q : Party) :
    (patchGameSpk C x ck0 sRef).afterCorr Q = patchGameSpk C x ck0 (sRef.afterCorr Q) :=
  rfl

theorem send_patchBobSpk (P : Params PQ PQC) (kp : KeyPair) (ck0 : BitVec 256) (g : GhostState PQ)
    (m : List (BitVec 8)) (r : PQC) (hne : g.epoch ≠ 0) :
    P.send (patchBobSpk kp ck0 g) m r = (patchBobSpk kp ck0 (P.send g m r).1, (P.send g m r).2) ∧
    (P.send g m r).1.epoch ≠ 0 := by
  have h1 : patchBobSpk kp ck0 g = g := by unfold patchBobSpk; simp [hne]
  have h2 : (P.send g m r).1.epoch ≠ 0 := (send_patchBob P ck0 g m r hne).2
  have h3 : patchBobSpk kp ck0 (P.send g m r).1 = (P.send g m r).1 := by
    unfold patchBobSpk; simp [h2]
  rw [h1, h3]
  exact ⟨rfl, h2⟩

theorem send_record_patchGameSpk (P : Params PQ PQC) (ℓ : ℕ) (x ck0 : BitVec 256)
    (spk₀ : PublicKey) (sRef s₁ : GameSt PQ ℓ) (qep : ℕ) (Q : Party) (m : Plain ℓ)
    (coins : PQC) (bad isChall : Bool)
    (hinv : GameInv P spk₀ sRef)
    (hsend : noBobSendInEpoch0 sRef Q = true)
    (hep : sRef.epMgmt 3 qep Q bad = some s₁) :
    let out := (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m coins
    let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩
    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameSpk P.C x ck0 s₁).st Q) m coins).2 = out.2 ∧
    (patchGameSpk P.C x ck0 s₁).record 3 Q
      ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameSpk P.C x ck0 s₁).st Q) m coins).1
      ⟨⟨Q, (patchGameSpk P.C x ck0 s₁).epoch Q, (patchGameSpk P.C x ck0 s₁).idx Q + 1⟩, m,
        ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameSpk P.C x ck0 s₁).st Q) m coins).2⟩ isChall =
      patchGameSpk P.C x ck0 (s₁.record 3 Q out.1 rec' isChall) ∧
    GameInv P spk₀ (s₁.record 3 Q out.1 rec' isChall) := by
  intro out rec'
  have hinv_pub : GameInv P (KeyPair.generate P.C x).publicKey (patchGamePub P.C x sRef) :=
    gameInv_patchGamePub P spk₀ x sRef hinv
  have hsend_pub : noBobSendInEpoch0 (patchGamePub P.C x sRef) Q = true := hsend
  have hep_pub : (patchGamePub P.C x sRef).epMgmt 3 qep Q bad = some (patchGamePub P.C x s₁) := by
    rw [patchGamePub_epMgmt, hep]; rfl
  obtain ⟨hc1, hc2, _⟩ := send_record_patchGameState P ℓ ck0 (KeyPair.generate P.C x).publicKey
    (patchGamePub P.C x sRef) (patchGamePub P.C x s₁) qep Q m coins bad isChall
    hinv_pub hsend_pub hep_pub
  obtain ⟨_, _, hinv_next⟩ := send_record_patchGameState P ℓ 0 spk₀ sRef s₁ qep Q m coins
    bad isChall hinv hsend hep
  obtain ⟨_, hB_ne, hst, _, _, _, _⟩ := epMgmt_epoch_pos sRef 3 qep Q bad s₁ hsend hep
  have hout_pub : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGamePub P.C x s₁).st Q) m coins =
      (patchPartyPub (KeyPair.generate P.C x).publicKey (KeyPair.generate P.C x) Q out.1,
          out.2) := by
    cases Q with
    | A =>
      change P.send (patchAlicePub (KeyPair.generate P.C x).publicKey (s₁.st .A)) m.toList coins =
        (patchAlicePub (KeyPair.generate P.C x).publicKey (P.send (s₁.st .A) m.toList coins).1,
         (P.send (s₁.st .A) m.toList coins).2)
      rw [hst]
      exact (send_patchAlicePub P spk₀ (KeyPair.generate P.C x).publicKey (sRef.st .A) m.toList
          coins hinv.1).1
    | B =>
      have hne_ep : (sRef.st .B).epoch ≠ 0 := fun h0 => (hB_ne rfl).1 (hinv.2.1.2.2.2 h0).1
      change P.send (patchBobSpk (KeyPair.generate P.C x) 0 (s₁.st .B)) m.toList coins =
        (patchBobSpk (KeyPair.generate P.C x) 0 (P.send (s₁.st .B) m.toList coins).1,
         (P.send (s₁.st .B) m.toList coins).2)
      rw [hst]
      exact (send_patchBobSpk P (KeyPair.generate P.C x) 0 (sRef.st .B) m.toList coins hne_ep).1
  have hout_2 : ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGamePub P.C x s₁).st Q) m coins).2 = out.2 := by
    rw [hout_pub]
  have hout_1 : ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGamePub P.C x s₁).st Q) m coins).1 =
      patchPartyPub (KeyPair.generate P.C x).publicKey (KeyPair.generate P.C x) Q out.1 := by
    rw [hout_pub]
  refine ⟨hc1.trans hout_2, ?_, hinv_next⟩
  dsimp only [patchGameSpk] at hc2 ⊢
  rw [hc2, hout_1, hout_2]
  exact congrArg (patchGameState ck0) (patchGamePub_record P.C x s₁ 3 Q out.1 rec' isChall)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC] [Inhabited PQ] in
theorem corrR_patchGameSpk (P : Params PQ PQC) (ℓ : ℕ) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (x ck0 : BitVec 256) (spk₀ : PublicKey)
    (sRef : GameSt PQ ℓ) (Q : Party) (hinv : GameInv P spk₀ sRef)
    (hA0 : Q = .A → (configRefuseEarlyBobCorr (Pt := Pt) decT encT).corrOK sRef .A = true →
      0 ∉ (sRef.st .A).chainEpochs) :
    (SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run (patchGameSpk P.C x ck0 sRef) =
      (Prod.map id (patchGameSpk P.C x ck0) <$> (SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run sRef) := by
  unfold SM.corrR
  have hguard : ((patchGameSpk P.C x ck0 sRef).win ||
      !(patchGameSpk P.C x ck0 sRef).corrAllowed Q ||
      ((configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).r1 &&
        inWindow (patchGameSpk P.C x ck0 sRef) Q) ||
      !(configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).corrOK
        (patchGameSpk P.C x ck0 sRef) Q) =
    (sRef.win || !sRef.corrAllowed Q ||
      ((configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).r1 && inWindow sRef Q) ||
      !(configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).corrOK sRef Q) := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hguard]
  by_cases hg : (sRef.win || !sRef.corrAllowed Q ||
      ((configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).r1 && inWindow sRef Q) ||
      !(configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).corrOK sRef Q) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq, patchGameSpk_afterCorr]
    have hcorrOK : (configRefuseEarlyBobCorr (St := GhostState PQ) (Msg := Plain ℓ) decT encT).corrOK sRef Q =
        true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
      exact hg.2
    cases Q with
    | A =>
      have hno0 : 0 ∉ (sRef.st .A).chainEpochs := hA0 rfl hcorrOK
      have hstA : (patchGameSpk P.C x ck0 sRef).st .A = sRef.st .A := by
        simp [patchGameSpk_st_A, patchAlice, patchAlicePub, hno0]
      rw [hstA]
    | B =>
      have hnoB0 : sRef.epoch .B ≠ 0 := by
        unfold configRefuseEarlyBobCorr noBobCorrInEpoch0 at hcorrOK
        simp only [Bool.and_eq_true, beq_self_eq_true, Bool.true_and, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq] at hcorrOK
        exact hcorrOK.1.2
      have hne : (sRef.st .B).epoch ≠ 0 := fun h0 => hnoB0 (hinv.2.1.2.2.2 h0).1
      have hstB : (patchGameSpk P.C x ck0 sRef).st .B = sRef.st .B := by
        simp [patchGameSpk_st_B, patchBobSpk, hne]
      rw [hstB]

theorem receive_patchGameSpk_of_not_spk (P : Params PQ PQC) (ℓ : ℕ) (x ck0 : BitVec 256)
    (spk₀ : PublicKey) (sRef : GameSt PQ ℓ) (Q : Party) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : GameInv P spk₀ sRef)
    (hB_ne : Q = .B → (sRef.st .B).epoch ≠ 0)
    (hnspk₀ : isAliceSpkQuery P spk₀ Q (sRef.st .A) c = false)
    (hnspkx : isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c = false) :
    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameSpk P.C x ck0 sRef).st Q) c rc =
      ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc).map fun y =>
        (patchParty ck0 Q (patchPartyPub (KeyPair.generate P.C x).publicKey (KeyPair.generate P.C x)
            Q y.1),
         y.2.1, y.2.2.1, y.2.2.2)) ∧
    ∀ st' t' i' m', (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc = some (st', t', i', m') →
      0 < t' ∧
      (∀ pos : Pos, (Q = .A → 0 < pos.epoch) →
        (patchGameSpk P.C x ck0 sRef).accept Q
          (patchParty ck0 Q (patchPartyPub (KeyPair.generate P.C x).publicKey (KeyPair.generate P.C
              x) Q st')) pos =
          patchGameSpk P.C x ck0 (sRef.accept Q st' pos) ∧
        GameInv P spk₀ (sRef.accept Q st' pos)) := by
  have hinv_pub : GameInv P (KeyPair.generate P.C x).publicKey (patchGamePub P.C x sRef) :=
    gameInv_patchGamePub P spk₀ x sRef hinv
  have hnspkx_pub : isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q
      ((patchGamePub P.C x sRef).st .A) c = false := by
    simp only [isAliceSpkQuery, patchGamePub, patchAlicePub_chainEpochs] at hnspkx ⊢
    exact hnspkx
  have hstep1 := receive_patchGameState_of_not_spk P ℓ ck0 (KeyPair.generate P.C x).publicKey
    (patchGamePub P.C x sRef) Q c rc hinv_pub hnspkx_pub
  have hstep0 := receive_patchGameState_of_not_spk P ℓ 0 spk₀ sRef Q c rc hinv hnspk₀
  have hpub : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGamePub P.C x sRef).st Q) c rc =
      ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc).map fun y =>
        (patchPartyPub (KeyPair.generate P.C x).publicKey (KeyPair.generate P.C x) Q y.1,
         y.2.1, y.2.2.1, y.2.2.2) := by
    cases Q with
    | A =>
      have hnonSpk : 0 ∉ (sRef.st .A).chainEpochs ∨
          ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg →
            ((spk₀ == msg.senderRatchetKey) = false ∧
             ((KeyPair.generate P.C x).publicKey == msg.senderRatchetKey) = false) := by
        by_cases h0 : 0 ∈ (sRef.st .A).chainEpochs
        · right
          intro msg htry
          unfold isAliceSpkQuery at hnspk₀ hnspkx
          simp only [beq_self_eq_true, h0, decide_true, Bool.and_self, Bool.true_and,
              htry] at hnspk₀ hnspkx
          exact ⟨hnspk₀, hnspkx⟩
        · exact Or.inl h0
      have hA := (receive_patchAlicePub_nonSpk P spk₀ (KeyPair.generate P.C x).publicKey
        (sRef.st .A) c rc hinv.1 hnonSpk).1
      unfold libsignalSessionSchemeFromEpoch0Keys
      dsimp only [patchGamePub, patchPartyPub]
      rw [hA]
      cases P.receive (sRef.st .A) c rc <;> rfl
    | B =>
      have hne0 : (sRef.st .B).epoch ≠ 0 := hB_ne rfl
      have hpatch_in : patchBobSpk (KeyPair.generate P.C x) 0 (sRef.st .B) = sRef.st .B := by
        unfold patchBobSpk; simp [hne0]
      unfold libsignalSessionSchemeFromEpoch0Keys
      dsimp only [patchGamePub, patchPartyPub]
      rw [hpatch_in]
      cases hrecv : P.receive (sRef.st .B) c rc with
      | none => rfl
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        obtain ⟨_, _, _, _, _, _, _, hep_cases⟩ :=
          receive_noZero_props P P.idA (sRef.st .B) c rc hinv.2.1.1 hinv.2.1.2.1 hinv.2.1.2.2.1
            st' t' i' m' hrecv
        have hne' : st'.epoch ≠ 0 := by
          rcases hep_cases with ⟨heq, _⟩ | heq
          · exact heq.symm ▸ hne0
          · omega
        simp only [Option.map_some, patchBobSpk, hne', ↓reduceIte]
  refine ⟨?_, ?_⟩
  · dsimp only [patchGameSpk]
    rw [hstep1.1, hpub, Option.map_map]
    rfl
  · intro st' t' i' m' hrecv
    have h0 := hstep0.2 st' t' i' m' hrecv
    refine ⟨h0.1, fun pos hpos => ⟨patchGameSpk_accept P.C x ck0 sRef Q st' pos, h0.2 pos hpos⟩⟩

theorem receive_patchGameSpk_of_spk_test_false (P : Params PQ PQC) (ℓ : ℕ) (x ck0 : BitVec 256)
    (spk₀ : PublicKey) (sRef : GameSt PQ ℓ) (Q : Party) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : GameInv P spk₀ sRef)
    (hspk : isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q (sRef.st .A) c = true)
    (htest : testSpk P (sRef.st .A).session.pqRatchetState c ck0 = false) :
    Q = .A ∧
    (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameSpk P.C x ck0 sRef).st Q) c rc = none := by
  have hinv_pub : GameInv P (KeyPair.generate P.C x).publicKey (patchGamePub P.C x sRef) :=
    gameInv_patchGamePub P spk₀ x sRef hinv
  have hspk_pub : isAliceSpkQuery P (KeyPair.generate P.C x).publicKey Q
      ((patchGamePub P.C x sRef).st .A) c = true := by
    simp only [isAliceSpkQuery, patchGamePub, patchAlicePub_chainEpochs] at hspk ⊢
    exact hspk
  have hpqr_pub : ((patchGamePub P.C x sRef).st .A).session.pqRatchetState =
      (sRef.st .A).session.pqRatchetState := by
    dsimp only [patchGamePub]
    unfold patchAlicePub setAliceSpkPub
    split <;> rfl
  have htest_pub : testSpk P ((patchGamePub P.C x sRef).st .A).session.pqRatchetState c ck0 =
      false := by
    rw [hpqr_pub]; exact htest
  exact receive_patchGameState_of_spk_test_false P ℓ ck0 (KeyPair.generate P.C x).publicKey
    (patchGamePub P.C x sRef) Q c rc hinv_pub hspk_pub htest_pub

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
