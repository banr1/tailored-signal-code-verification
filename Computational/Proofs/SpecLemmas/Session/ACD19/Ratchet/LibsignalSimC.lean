/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# The decision-C simulator `libsignalToModularSchemeSim`

**Checked by Lean.**

Defines the simulator `runLibsignalToModularSchemeSim` and the hidden-salt probe game
`hiddenSaltGame` / `hiddenSaltTerm` for refining the libsignal session to ACD19's Double Ratchet
scheme (`lFig8`) without assuming SPQR salt binding (`DEV-LS36`). It extends `LibsignalSimShallow`
by tracking post-corruption Fig. 8 states and pre-corruption snapshot seeds (`DEV-LS37`), handling
evicted salt mismatches (`DEV-LS11`, `DEV-AEAD3`, `DEV-LS31`), and rejecting SPQR receive panics.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSimC

open HMAC HKDF CBC LibsignalAead WireAEAD SM SM.Construction CKA LibsignalSession LibsignalInst
open LibsignalSim

/-- Known portion of a party's Fig. 8 state after corruptions. -/
structure Kept (Pt : Type) where
  full : Option (Fig8St Pt)
  rs : ℕ → Option (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))

def Kept.unknown {Pt : Type} : Kept Pt := ⟨none, fun _ => none⟩

def Kept.ofSt {Pt : Type} (st : Fig8St Pt) : Kept Pt := ⟨some st, st.vR⟩

/-- State of `libsignalToModularSchemeSim`: base simulator state plus tracked Fig. 8 states, sender
sessions, and corruption snapshots (`DEV-LS37`). -/
structure LibsignalToModularSchemeSimState (PQ Pt : Type) (ℓ : ℕ) where
  base : SimState PQ Pt ℓ
  kept : Party → Kept Pt
  sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256))
  snaps : List (Party × ℕ × GhostState PQ) := []

/-- Monad lift and hidden-salt probe hook for `simRunCWith`. -/
structure Hook (Pt : Type) (ℓ : ℕ) (M : Type → Type) where
  lift : {α : Type} → Fig8Comp Pt ℓ α → M α
  probe : Party → Fig8C Pt → M Unit

def idHook {Pt : Type} {ℓ : ℕ} : Hook Pt ℓ (Fig8Comp Pt ℓ) := ⟨fun x => x, fun _ _ => pure ()⟩

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

section Impl

variable (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
  (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
  (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
    (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
    (ℕ × LibsignalCiphertextWithSalt32))

/-! ## Tracked Fig. 8 state and seed prediction -/

/-- Advance `Kept` across a party send, dropping `full` when a new sending epoch starts. -/
def Kept.send (k : Kept Pt) : Kept Pt :=
  match k.full with
  | none => k
  | some st =>
    if st.id.sendsIn (st.tcur + 1) then ⟨none, st.vR⟩
    else { k with full := some (fig.send st (⟨0, [], effectiveHkdfSalt32 none, none⟩, default) 0).1 }

/-- Advance `Kept` after Fig. 8 accepts `c`. -/
def Kept.recv (c : Fig8C Pt) (k : Kept Pt) : Kept Pt :=
  match k.full with
  | some st =>
    match fig.receive st c with
    | some (st', _) => { k with full := some st' }
    | none => ⟨none, st.vR⟩
  | none =>
    let v' := (k.rs c.1.1).bind fun v => (fs.receive v c.1 c.2).map (·.1)
    { k with rs := Function.update k.rs c.1.1 v' }

/-- Predict Fig. 8's `receive` of `c` from `Kept`, returning `none` when undetermined. -/
def Kept.eval (c : Fig8C Pt) (k : Kept Pt) : Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  match k.full with
  | some st => some ((fig.receive st c).map (·.2))
  | none => (k.rs c.1.1).map fun v => (fs.receive v c.1 c.2).map fun x => (c.1.1, x.2.1, x.2.2)

/-- Predict the receiver's `receive` of `c'` from the sender session recorded for `c`. -/
def sentEval (sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256))) (c c' : Fig8C Pt) :
    Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  (sent.find? fun e => decide (e.1 = c)).map fun e =>
    (fs.receive ⟨e.2.chainKey, e.2.lastIndex, []⟩ c'.1 c'.2).map fun x => (c'.1.1, x.2.1, x.2.2)

def predictReceive (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (c c' : Fig8C Pt) :
    Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  match Kept.eval (fig := fig) (fs := fs) c' (sC.kept Q) with
  | some r => some r
  | none => sentEval (fs := fs) sC.sent c c'

def chainKeyAfter (F : ShaCompress) : ℕ → BitVec 256 → BitVec 256
  | 0, k => k
  | n + 1, k => chainKeyAfter F n (bytesToKey32 (Ratchet.chainHmac F k Ratchet.chainKeySeed))

def chainSeedAt (F : ShaCompress) (ck : LibsignalSession.ChainKey) (counter : BitVec 32) :
    Option (List (BitVec 8)) :=
  if counter.toNat < ck.index.toNat then none
  else some (Ratchet.chainHmac F (chainKeyAfter F (counter.toNat - ck.index.toNat) ck.key)
    Ratchet.messageKeySeed)

/-- Derive the message-key seed of wire `w` for receiver `Q` from corruption snapshots `snaps`
(`DEV-LS37`). -/
def snapshotMessageKeySeed {PQ PQC : Type} (P : Params PQ PQC) (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (t : ℕ) (w : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    let k1 := snaps.findSome? fun e =>
      if e.1 = Q then
        (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).bind fun rc =>
          match rc.messageKeys.find? (·.counter == n) with
          | some mkg => some mkg.seed
          | none => rc.chainKey.bind fun ck => chainSeedAt P.C.F ck n
      else none
    let k3 := snaps.findSome? fun e =>
      if e.1 = Q.other then
        e.2.2.session.senderChain.bind fun sc =>
          if sc.ratchetKey.publicKey = Y then chainSeedAt P.C.F sc.chainKey n else none
      else none
    let k2 := snaps.findSome? fun e =>
      if e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1 then
        e.2.2.session.senderChain.bind fun sc =>
          match rootCreateChain P.C e.2.2.session.rootKey Y sc.ratchetKey.privateKey with
          | .ok (_, ck) => chainSeedAt P.C.F ck n
          | .error _ => none
      else none
    let k4 := (snaps.findSome? fun e_cur =>
        if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
          e_cur.2.2.session.senderChain.bind fun sc_cur =>
            if sc_cur.ratchetKey.publicKey = Y then
              e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
                (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
            else none
        else none).bind fun p =>
      snaps.findSome? fun e_prev =>
        if e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧
            t = e_prev.2.1 + 2 then
          e_prev.2.2.session.senderChain.bind fun sc_prev =>
            match rootCreateChain P.C e_prev.2.2.session.rootKey
                p.1 sc_prev.ratchetKey.privateKey with
            | .ok (rk1, _) =>
              match rootCreateChain P.C rk1 p.1 p.2 with
              | .ok (_, ck0) => chainSeedAt P.C.F ck0 n
              | .error _ => none
            | .error _ => none
        else none
    k1 <|> k3 <|> k2 <|> k4

def decryptWithKnownSeed {PQ PQC : Type} (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8))
    (salt : HKDF.Salt) (seed : List (BitVec 8)) : Option (List (BitVec 8)) :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let mk := deriveMessageKeys P.C.F salt seed
    if !(msg.verifyMacWithAddresses P.C.F (P.expectedAddrs Q) (idOf Q.other) (idOf Q) mk.2) then
      none
    else aesCbcDecrypt P.C.D mk.1.1 mk.1.2 msg.ciphertext

def kDecryptFig8 {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) (Q : Party)
    (w : List (BitVec 8)) (c' : Fig8C Pt) (seed : List (BitVec 8)) :
    Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)) :=
  match lPubOf P.codec c'.2.2, decryptWithKnownSeed P Q w (some c'.2.2.2) seed with
  | some pub, some m_raw => some (c'.1.1, c'.2.1, (pub, padOrTruncatePlain ℓ m_raw))
  | _, _ => none

/-- **DEV-LS37 (formalization): pre-corruption snapshot seed evaluation.** Extends `predictReceive`
with message-key seed recovery from `sC.snaps`. -/
def predictReceiveWithSnapshots {PQ PQC : Type} (P : Params PQ PQC) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt) :
    Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  (predictReceive (fig := fig) (fs := fs) sC Q c c').orElse fun _ =>
    (snapshotMessageKeySeed P sC.snaps Q c.1.1 w).map (kDecryptFig8 P ℓ Q w c')

/-! ## Simulated oracles -/

variable {M : Type → Type} [Monad M] (H : Hook Pt ℓ M)

local notation "SimCM" => StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M

def runOnBaseState {α : Type} (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) : SimCM α := fun sC => do
  let (a, s') ← H.lift (x.run sC.base)
  return (a, { sC with base := s' })

def liftC {α : Type} (x : Fig8Comp Pt ℓ α) : SimCM α := StateT.lift (H.lift x)

/-- Simulated `transmit` and `chall` oracle, recording known sender sessions and updating `kept`. -/
def simSendC (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    SimCM (Option (List (BitVec 8))) := do
  let res ← runOnBaseState H (simSend (P := P) (qep := qep) Q m₀ chal r)
  match res with
  | none => return none
  | some w =>
    let sC ← get
    let sent := match (sC.kept Q).full, sC.base.honest.head? with
      | some st, some (_, c) =>
        if st.id.sendsIn (st.tcur + 1) then sC.sent
        else match st.vS with
          | some v => (c, v) :: sC.sent
          | none => sC.sent
      | _, _ => sC.sent
    set { sC with kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)), sent }
    return some w

def fwdAnswerC (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) : SimCM (Option (RecvResult (Plain ℓ))) := do
  let res ← runOnBaseState H (fwd Q c')
  match res with
  | some (.accepted _ _ _) =>
    modify fun sC => { sC with kept := Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c' (sC.kept Q)) }
  | _ => pure ()
  runOnBaseState H (onAnswer (qep := qep) Q w isDel ci? T pq' res)

/-- Resynchronize Fig. 8 via `deliver` of the honest record `c` when case-3a acceptance of `c'` is
determined. -/
def resyncC (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    SimCM (Option (RecvResult (Plain ℓ))) := do
  match r with
  | none => return some .rejected
  | some (t, i, pm) =>
    let res ← liftC H (SM.deliverQuery (St := Fig8St Pt) Q c)
    match res with
    | some (.accepted _ _ _) =>
      modify fun sC => { sC with kept := Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c (sC.kept Q)) }
      runOnBaseState H (onAccept (qep := qep) Q w true t i pm.2 ci? T pq')
    | _ => return some .rejected

/-- Forward `c'`, resynchronizing or probing on salt-mismatched deliveries under `¬safe-inj`. -/
def fwdC (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    SimCM (Option (RecvResult (Plain ℓ))) := do
  let sC ← get
  match honestC with
  | some c =>
    if decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3) then
      match predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
      | some r => resyncC (qep := qep) (fig := fig) (fs := fs) (H := H) Q w ci? T pq' c r
      | none =>
        StateT.lift (H.probe Q c')
        return some .rejected
    else fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel ci? T pq' c'
  | none => fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel ci? T pq' c'

/-- Forward an evicted honest wire with a mismatched salt as a new ratchet key, or probe under
`¬safe-inj`. -/
def fwdEvictC (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey) (pq' : PQ)
    (c' : Fig8C Pt) : SimCM (Option (RecvResult (Plain ℓ))) := do
  let sC ← get
  if isDel && !(sC.base.mir.safeInj 3) then
    StateT.lift (H.probe Q c')
    return some .rejected
  else fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel none T pq' c'

/-- Simulated `deliver` (`isDel = true`) and `inject` (`isDel = false`) oracle. -/
def simRecvC (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    SimCM (Option (RecvResult (Plain ℓ))) := do
  let s := (← get).base
  if s.mir.win then return none
  if isDel && (s.mir.inTransit Q.other w).isNone then return none
  if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) then return none
  if w.length < 9 then return some .rejected
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  match (signalWireCodec P.codec).parse ser with
  | none => return some .rejected
  | some (h, _) =>
    if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then return some .rejected
    if P.spqr.recvPanics (s.pq Q) h.pqRatchet then return some .rejected
    match P.spqr.recv (s.pq Q) h.pqRatchet with
    | .error _ => return some .rejected
    | .ok (pq', salt) =>
      let i := h.counter.toNat + 1
      let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
        match honestC with
        | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        | none => ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      let T? := decT h.senderRatchetKey
      let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
      match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
        if g.rejects i then return some .rejected
        fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel (some ci)
          h.senderRatchetKey pq' honestC (mkC g.epoch T?)
      | none =>
        let evicted := (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true
        if evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true then
          return some .rejected
        if T? == some 0 then return some .rejected
        if inReceiveOnlyEpoch s.mir Q || spkAmb then
          modify fun sC => { sC with base := { sC.base with amb := sC.base.amb + 1 } }
        if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then return some .rejected
        match T? with
        | none => return some .rejected
        | some T =>
          if evicted then
            fwdEvictC (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel h.senderRatchetKey pq'
              ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          else
            fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := H) Q w isDel none
              h.senderRatchetKey pq' honestC (mkC (s.mir.epoch Q + 1) (some T))

/-- Simulated `corr` oracle, recording the party's Fig. 8 state in `kept` and snapshot in `snaps`. -/
def simCorrC (Dh : DHFun (BitVec 256) Pt) (Q : Party) : SimCM (Option (GhostState PQ)) := do
  let sC ← get
  let s := sC.base
  if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then return none
  let res ← liftC H (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)
  match res with
  | none => return none
  | some st =>
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match st.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let g := toGhost (P := P) { s with chains } Q st
    set { sC with base := { s with mir := s.mir.afterCorr Q, chains },
                  kept := Function.update sC.kept Q (Kept.ofSt st),
                  snaps := (Q, s.mir.epoch Q, g) :: sC.snaps }
    return some g

def guardC {α : Type} (x : SimCM (Option α)) : SimCM (Option α) := do
  if (← get).base.stopped then return none
  x

/-- Query implementation for `libsignalToModularSchemeSim`. -/
def simImplC (Dh : DHFun (BitVec 256) Pt) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) SimCM :=
  let c : QueryImpl unifSpec SimCM := fun n =>
    liftC H (query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) SimCM :=
    fun ⟨Q, m, r⟩ => guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := H) Q m none r)
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) SimCM :=
    fun ⟨Q, m₀, m₁, r⟩ => guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := H) Q m₀ (some m₁) r)
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimCM :=
    fun ⟨Q, w⟩ => guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
      (H := H) Q w true)
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimCM :=
    fun ⟨Q, w⟩ => guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
      (H := H) Q w false)
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) SimCM :=
    fun Q => guardC (simCorrC (P := P) (encT := encT) (H := H) Dh Q)
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

def initSimC (pqA pqB : PQ) : LibsignalToModularSchemeSimState PQ Pt ℓ :=
  { base := initSim pqA pqB, kept := fun _ => Kept.unknown, sent := [], snaps := [] }

/-- Run adversary `A` against `simImplC` with hook `H`. -/
def simRunCWith (Dh : DHFun (BitVec 256) Pt)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : M Bool := do
  let pqrKey ← H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  (simulateQ (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
    (H := H) Dh) A).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))

end Impl

/-! ## Simulator and hidden-salt probe game -/

/-- The decision-C simulator `simRunCWith idHook` against `lFig8` with `maxSkip = 25000`. -/
def runLibsignalToModularSchemeSim (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    Fig8Comp Pt ℓ Bool :=
  simRunCWith (P := P) (encT := encT) (decT := decT) (qep := qep)
    (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (fs := lFS P.C P.codec ℓ encT idOf 25000)
    (H := idHook) Dh A

end LibsignalSimC
end Ratchet
end CryptoGames

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSimC

open HMAC HKDF CBC LibsignalAead WireAEAD SM SM.Construction CKA LibsignalSession LibsignalInst
open LibsignalSim

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

abbrev ProbeM (Pt : Type) (ℓ : ℕ) :=
  StateT (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ProbComp

def fig8ImplH1
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) :
    QueryImpl (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (StateT (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp)
    + oracleImpl fig (2 + 1) qepF Config.h1

/-- Hook running Fig. 8 `H1` oracles and setting the probe flag when `fig.receive` accepts `c'`. -/
def probeHook
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) : Hook Pt ℓ (ProbeM Pt ℓ) where
  lift x := fun gh => do
    let (a, g') ← (simulateQ (fig8ImplH1 fig qepF) x).run gh.1
    return (a, (g', gh.2))
  probe Q c' := modify fun gh => (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)

/-- Probe game running `simRunCWith probeHook` in Fig. 8's `H1` game and returning whether an
undetermined salt-mismatched delivery would be accepted. -/
def hiddenSaltGame (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ (BitVec 256 × BitVec 256)
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, gh) ← (simRunCWith (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
    (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := probeHook fig (qep + 1)) Dh A).run
    (initState fig k b, false)
  return gh.2

/-- **DEV-LS36 (formalization): without SPQR salt binding the refinement has a hidden-salt term.**
Probability that `hiddenSaltGame` sets its probe flag (`DEV-LS37`). -/
noncomputable def hiddenSaltTerm (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ℝ≥0∞ :=
  𝒟[hiddenSaltGame P ℓ Dh encPt encT decT idOf lam qep A] {true}

end LibsignalSimC
end Ratchet
end CryptoGames
