/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
public import ProofLib.Lemmas
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Shallow libsignal-to-Fig. 8 simulator

**Checked by Lean.**

Defines the shallow reduction `simRun` (`Refine.sim`) and its state and step helpers (`SimState`,
`simSend`, `simRecv`, `simCorr`, `toGhost`), which simulate the libsignal session game's oracles
against ACD19's Double Ratchet scheme (`lFig8`).
-/

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSim

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst

/-- State of the shallow simulator: game mirror plus libsignal state not modeled by Fig. 8. -/
structure SimState (PQ Pt : Type) (ℓ : ℕ) where
  mir : GameState Unit (Plain ℓ) (List (BitVec 8))
  pq : Party → PQ
  pn : Party → BitVec 32
  unackA : Bool
  honest : List (List (BitVec 8) × Fig8C Pt)
  chains : Party → List GhostChain
  amb : ℕ
  stopped : Bool

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

def pushChain (cs : List GhostChain) (g : GhostChain) : List GhostChain :=
  let cs' := cs ++ [g]
  cs'.drop (cs'.length - 5)

def inReceiveOnlyEpoch (s : GameState Unit (Plain ℓ) (List (BitVec 8))) (P : Party) : Bool :=
  !(P.sendsIn (s.epoch P))

section Impl

variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
  (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)

local notation "SimM" => StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)

def putS (s : SimState PQ Pt ℓ) : SimM Unit := set s

def liftQ {α : Type} (x : Fig8Comp Pt ℓ α) : SimM α := StateT.lift x

def coin (α : Type) [SampleableType α] : SimM α :=
  liftQ (liftM ($ᵗ α : ProbComp α))

def mkPub (s : SimState PQ Pt ℓ) (Q : Party) (r : PQC) (pn : BitVec 32) : Option (PQ × LibsignalMsgPublicPart) :=
  (P.spqr.send (s.pq Q) r).map fun x =>
    (x.1, ⟨pn, x.2.2, effectiveHkdfSalt32 x.2.1, if Q == Party.A && s.unackA then P.addrAB else none⟩)

/-- Simulated `transmit` and `chall` oracle. -/
def simSend (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    SimM (Option (List (BitVec 8))) := do
  let s ← get
  if s.mir.win || !(noBobSendInEpoch0 s.mir Q) then return none
  match s.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
    let rq ← match r with
      | some rq => pure rq
      | none => coin PQC
    let rc : Option (BitVec 256) ← match r with
      | some _ => some <$> coin (BitVec 256)
      | none => pure none
    match mkPub (P := P) s Q rq pn with
    | none => return none
    | some (pq', pub) =>
      let res ← match chal with
        | none => liftQ (SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
        | some m₁ => liftQ (SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
      match res with
      | none => return none
      | some c =>
        let w := toWire c
        let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
        let mir' := s₁.record 3 Q () rec' chal.isSome
        putS { s with mir := mir', pq := Function.update s.pq Q pq',
                      pn := Function.update s.pn Q pn, honest := (w, c) :: s.honest }
        return some w

/-- Forward `c` as `deliver` if it is an honest record in transit, and as `inject` otherwise. -/
def fwd (Q : Party) (c : Fig8C Pt) : SimM (Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) := do
  let s ← get
  let inT := s.honest.any fun wc => decide (wc.2 = c) && (s.mir.inTransit Q.other wc.1).isSome
  if inT then liftQ (SM.deliverQuery (St := Fig8St Pt) Q c)
  else liftQ (SM.injectQuery (St := Fig8St Pt) Q c)

/-- Update ghost chains, SPQR state, and game mirror after Fig. 8 accepts a message. -/
def onAccept (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) : SimM (Option (RecvResult (Plain ℓ))) := do
  let s ← get
  let cs := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)
  let s' := { s with chains := Function.update s.chains Q cs, pq := Function.update s.pq Q pq',
                     unackA := s.unackA && Q != Party.A }
  if isDel then
    match s.mir.inTransit Q.other w with
    | none => return none
    | some r =>
      putS { s' with mir := s.mir.accept Q () r.pos }
      return some (.accepted t i (if s.mir.chall.contains r.pos then none else some m))
  else
    if qep + 1 < t then return some .rejected
    let pos : Pos := ⟨Q.other, t, i⟩
    if s.mir.trivial 3 pos then
      putS { s' with mir := s.mir.accept Q () pos }
      return some (.accepted t i (some m))
    else
      putS { s with mir := { s.mir with win := true } }
      return some .rejected

def onAnswer (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    SimM (Option (RecvResult (Plain ℓ))) :=
  match res with
  | some (.accepted t i pm) =>
    onAccept (qep := qep) Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq'
  | _ => return some .rejected

/-- Reconstruct a libsignal `GhostState` from a Fig. 8 party state and simulator bookkeeping. -/
def toGhost (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) : GhostState PQ :=
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let sender : Option SenderChain :=
    match st.γ, st.vS with
    | .exp x, some v => some ⟨KeyPair.generate P.C x, ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩⟩
    | _, _ => none
  let recv : GhostChain → ReceiverChain := fun g =>
    match st.vR g.epoch with
    | some v =>
      ⟨g.key.getD dummyKey, some ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩,
        g.skipped.filterMap fun j =>
          (v.skippedKeys.lookup j).map fun mk => ⟨keyToBytes32 mk, BitVec.ofNat 32 (j - 1)⟩⟩
    | none => ⟨g.key.getD dummyKey, none, []⟩
  ⟨Q, { sessionVersion := BitVec.ofNat 32 currentVersion.toNat, localIdentity := idOf Q,
         remoteIdentity := some (idOf Q.other), rootKey := st.root, previousCounter := s.pn Q,
         senderChain := sender, receiverChains := (s.chains Q).map recv,
         pendingPreKey := Q == Party.A && s.unackA, pqRatchetState := s.pq Q },
    s.mir.epoch Q, (s.chains Q).map (·.epoch)⟩

end Impl

def initSim (pqA pqB : PQ) : SimState PQ Pt ℓ :=
  { mir := { st := fun _ => (), b := false }, pq := fun Q => if Q == Party.A then pqA else pqB,
    pn := fun _ => 0, unackA := true, honest := [],
    chains := fun Q => if Q == Party.A then [⟨none, 0, 0, []⟩] else [], amb := 0, stopped := false }

end LibsignalSim
end Ratchet

end CryptoGames

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSim

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

section Impl

variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
  (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)

local notation "SimM" => StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)

/-- Simulated `deliver` (`isDel = true`) and `inject` (`isDel = false`) oracle. -/
def simRecv (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    SimM (Option (RecvResult (Plain ℓ))) := do
  let s ← get
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
    match P.spqr.recv (s.pq Q) h.pqRatchet with
    | .error _ => return some .rejected
    | .ok (pq', salt) =>
      let i := h.counter.toNat + 1
      let honestC :=
        (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
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
        let res ← fwd Q (mkC g.epoch T?)
        onAnswer (qep := qep) Q w isDel (some ci) h.senderRatchetKey pq' res
      | none =>
        if (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true then
          return some .rejected
        if T? == some 0 then return some .rejected
        let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
        if amb then putS { s with amb := s.amb + 1 }
        if amb && k == some s.amb then
          if !(inReceiveOnlyEpoch s.mir Q) then
            if !(25000 < i - 1 || 2 ^ 32 ≤ i) then
              match T? with
              | none => pure ()
              | some T => let _ ← fwd Q (mkC (s.mir.epoch Q + 1) (some T))
            modify fun s' : SimState PQ Pt ℓ => { s' with stopped := true }
            return none
          let _ ← liftQ (SM.transmitQuery (St := Fig8St Pt) Q
            (⟨0, [], effectiveHkdfSalt32 none, none⟩, default) none)
          match T? with
          | none => pure ()
          | some T => let _ ← fwd Q (mkC (s.mir.epoch Q + 2) (some T))
          modify fun s' : SimState PQ Pt ℓ => { s' with stopped := true }
          return none
        else
          if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then return some .rejected
          match T? with
          | none => return some .rejected
          | some T =>
            let res ← fwd Q (mkC (s.mir.epoch Q + 1) (some T))
            onAnswer (qep := qep) Q w isDel none h.senderRatchetKey pq' res

/-- Simulated `corr` oracle. -/
def simCorr (Q : Party) : SimM (Option (GhostState PQ)) := do
  let s ← get
  if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then return none
  let res ← liftQ (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)
  match res with
  | none => return none
  | some st =>
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match st.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    putS { s with mir := s.mir.afterCorr Q, chains }
    return some (toGhost (P := P) { s with chains } Q st)

def «guard» {α : Type} (x : SimM (Option α)) : SimM (Option α) := do
  if (← get).stopped then return none
  x

def simImpl :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) SimM :=
  let c : QueryImpl unifSpec SimM := fun n =>
    liftQ (query (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) SimM :=
    fun ⟨Q, m, r⟩ => «guard» (simSend (P := P) (qep := qep) Q m none r)
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) SimM :=
    fun ⟨Q, m₀, m₁, r⟩ => «guard» (simSend (P := P) (qep := qep) Q m₀ (some m₁) r)
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimM :=
    fun ⟨Q, w⟩ =>
      «guard» (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) Q w true)
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimM :=
    fun ⟨Q, w⟩ =>
      «guard» (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) Q w false)
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) SimM :=
    fun Q => «guard» (simCorr (P := P) (Dh := Dh) (encT := encT) Q)
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

end Impl

/-- Run adversary `A` against `simImpl` (`k = none` for `sim`, `k = some k` for `simWin k`). -/
def simRun (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : Fig8Comp Pt ℓ Bool := do
  let pqrKey ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  let b' ← (simulateQ (simImpl (P := P) (Dh := Dh) (encT := encT) (decT := decT) (qep := qep)
    (k := k)) A).run' (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
  match k with
  | none => return b'
  | some _ => (liftM ($ᵗ Bool : ProbComp Bool) : Fig8Comp Pt ℓ Bool)

end LibsignalSim
end Ratchet

namespace LibsignalSM.Refine

open Ratchet LibsignalInst LibsignalSession CKA

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC]

/-- Shallow reduction from the libsignal session game to `lFig8`. -/
def sim (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) : Fig8Adv Pt ℓ :=
  LibsignalSim.simRun P Dh encT decT qep none A

end LibsignalSM.Refine
end CryptoGames
