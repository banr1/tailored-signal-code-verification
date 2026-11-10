/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.SpkHop2Red
public import ProofLib.Lemmas

/-!
# Shallow Reference Reductions for Hop 2

Defines the shallow `OracleComp` reference game `hop2Game` and the PRG/PRF reductions
`hop2PrgRedK` and `hop2PrfRedK` for the 9 root-KDF hybrids of Hop 2.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec

abbrev Hop2Comp (Pt : Type) : Type → Type := OracleComp (unifSpec + prfSpec Pt (BitVec 256))

/-- Parameters of Hop 2 hybrid `k`: hybrid index, table `k` creation entry, and table `k + 1` KDF step. -/
structure Hop2Hyb (Pt : Type) where
  k : ℕ
  chall : Ratchet.RootKey × BitVec 256
  step : Pt → Hop2Comp Pt (BitVec 256)

/-- Auxiliary state tracking lazy off-chain PRKs, on-chain creation entries, party chain indices,
ratchet secrets, and the bad event. -/
structure Hop2Aux (Pt : Type) where
  lazy : List ((ℕ × Pt) × BitVec 256) := []
  made : List ((ℕ × Pt) × BitVec 256) := []
  idx : Party → Option ℕ
  coins : Party → BitVec 256
  bad : Bool := false

abbrev Hop2M (Pt : Type) (ℓ : ℕ) : Type → Type :=
  StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt) (Hop2Comp Pt)

/-- Auxiliary-state update produced by a committed DH step. -/
structure Hop2Upd (Pt : Type) where
  idx : Option ℕ
  coins : BitVec 256
  made : Option ((ℕ × Pt) × BitVec 256)

abbrev Hop2Out (Pt : Type) (ℓ : ℕ) : Type :=
  Option ((GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) × Option (Hop2Upd Pt))

section Hop2

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ} {PQC : Type} [SampleableType PQC]

def hop2Unif : Hop2Comp Pt (BitVec 256) :=
  (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Hop2Comp Pt (BitVec 256))

def hop2Lift {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α) :
    Hop2M Pt ℓ α :=
  StateT.mk fun st => do
    let r ← (liftM (m.run st.1) :
      Hop2Comp Pt (α × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes))
    return (r.1, (r.2, st.2))

/-- Look up or lazily sample the off-chain PRK for table `t` at `Q`. -/
def hop2Lazy (t : ℕ) (Q : Pt) : Hop2M Pt ℓ (BitVec 256) := do
  let st ← get
  match st.2.lazy.lookup (t, Q) with
  | some u => return u
  | none =>
    let u ← StateT.lift (hop2Unif (Pt := Pt))
    set (st.1, { st.2 with lazy := ((t, Q), u) :: st.2.lazy })
    return u

/-- Receiving half of a hooked DH step at index `idx` and DH output `Q`. -/
def hop2RecvHalf (P : Params Bytes PQC) (h : Hop2Hyb Pt) (idx : Option ℕ) (rk : Ratchet.RootKey)
    (their : PublicKey) (our : PrivateKey) (Q : Pt) :
    Hop2M Pt ℓ (Option (Option ℕ × Ratchet.RootKey × BitVec 256)) := do
  match idx with
  | none =>
    match rootCreateChain P.C rk their our with
    | .error _ => return none
    | .ok (rk', ck) => return some (none, rk', ck.key)
  | some t =>
    if Q = 0 then return none
    if t ≤ h.k then
      match (← get).2.made.lookup (t, Q) with
      | some ck => return some (some (t + 1), 0, ck)
      | none =>
        let u ← hop2Lazy t Q
        let (rk', ck) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
        return some (none, rk', ck)
    else
      let u ← StateT.lift (h.step Q)
      let (rk', ck) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
      return some (none, rk', ck)

/-- Sending half of a hooked DH step at index `idx` and DH output `Q'`. -/
def hop2SendHalf (P : Params Bytes PQC) (h : Hop2Hyb Pt) (idx : Option ℕ) (rk : Ratchet.RootKey)
    (their : PublicKey) (our' : PrivateKey) (Q' : Pt) :
    Hop2Comp Pt
      (Option (Option ℕ × Ratchet.RootKey × BitVec 256 × Option ((ℕ × Pt) × BitVec 256))) := do
  match idx with
  | none =>
    match rootCreateChain P.C rk their our' with
    | .error _ => return none
    | .ok (rk', ck) => return some (none, rk', ck.key, none)
  | some j =>
    if Q' = 0 then return none
    if j < h.k then
      let ck ← hop2Unif (Pt := Pt)
      return some (some (j + 1), 0, ck, some ((j, Q'), ck))
    else if j = h.k then
      return some (some (j + 1), 0, h.chall.2, some ((j, Q'), h.chall.2))
    else
      let u ← h.step Q'
      let (rk', ck) := Ratchet.rootExpand P.C.F (keyToBytes32 u)
      return some (none, rk', ck, none)

/-- Hooked DH ratchet step and message decryption when no receiver chain matches `msg.senderRatchetKey`. -/
def hop2DH (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt) (idx : Option ℕ) (coins : BitVec 256)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256) : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
  match decT msg.senderRatchetKey with
  | none => return none
  | some T =>
    if T = 0 ∨ encT T ≠ msg.senderRatchetKey then return none
    let some sc := g.session.senderChain | return none
    match ← hop2RecvHalf P h idx g.session.rootKey msg.senderRatchetKey
        sc.ratchetKey.privateKey (Dh.dh coins T) with
    | none => return none
    | some (idx1, rkM, ckR) =>
      let newKey := KeyPair.generate P.C rc
      match ← StateT.lift (hop2SendHalf P h idx1 rkM msg.senderRatchetKey newKey.privateKey
          (Dh.dh rc T)) with
      | none => return none
      | some (idx2, rk2, ckS, pend) =>
        let cur := sc.chainKey.index
        let sess' : SessionState Bytes :=
          { g.session with
            previousCounter := if cur = 0 then 0 else cur - 1
            rootKey := rk2
            receiverChains := RatchetState.evictReceiverChains
              (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
            senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
        match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            rc sess' with
        | (.error _, _) => return none
        | (.ok m, s_out) =>
          let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
            ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
          return some (({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
            g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m), some ⟨idx2, rc, pend⟩)

/-- Hooked receive dispatching new-chain receives on the hybrid chain to `hop2DH`. -/
def hop2Recv (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt) (g : GhostState Bytes) (c : Bytes)
    (rc : BitVec 256) : Hop2M Pt ℓ (Hop2Out Pt ℓ) := do
  match SignalMessage.tryFrom P.codec c with
  | .error _ => return none
  | .ok msg =>
    let aux := (← get).2
    match aux.idx g.party with
    | some t =>
      if (g.session.receiverChains.findIdx?
          (·.senderRatchetKey == msg.senderRatchetKey)).isNone then
        hop2DH P Dh encT decT h (some t) (aux.coins g.party) g msg rc
      else
        return ((sessionSchemeU P ℓ).receive g c rc).map fun r => (r, none)
    | none => return ((sessionSchemeU P ℓ).receive g c rc).map fun r => (r, none)

/-- Bad-event predicate: Alice holds her epoch-0 receiver chain and parses a message with sender key `pub s`. -/
def hop2BadAt (P : Params Bytes PQC) (s : BitVec 256) (g : GhostState Bytes) (c : Bytes) : Bool :=
  g.party == .A && g.chainEpochs.contains 0 &&
    match SignalMessage.tryFrom P.codec c with
    | .error _ => false
    | .ok msg => msg.senderRatchetKey == (KeyPair.generate P.C s).publicKey

def hop2Commit (aux : Hop2Aux Pt) (Q : Party) : Option (Hop2Upd Pt) → Hop2Aux Pt
  | none => aux
  | some u =>
    { aux with
      idx := Function.update aux.idx Q u.idx
      coins := Function.update aux.coins Q u.coins
      made := match u.made with | some e => e :: aux.made | none => aux.made }

def hop2Deliver (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (s : BitVec 256) (h : Hop2Hyb Pt) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ))) (Hop2M Pt ℓ) :=
  fun ⟨Q, c⟩ => do
    let st ← get
    if st.1.win then return none
    match st.1.inTransit Q.other c with
    | none => return none
    | some r =>
      let rc ← StateT.lift (hop2Unif (Pt := Pt))
      match ← hop2Recv P Dh encT decT h (st.1.st Q) c rc with
      | none => return some .rejected
      | some ((st', t', i', m'), u) =>
        let st2 ← get
        set (st2.1.accept Q st' r.pos,
          { hop2Commit st2.2 Q u with bad := st2.2.bad || hop2BadAt P s (st.1.st Q) c })
        return some (.accepted t' i' (if st2.1.chall.contains r.pos then none else some m'))

def hop2Inject (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ))) (Hop2M Pt ℓ) :=
  fun ⟨Q, c⟩ => do
    let st ← get
    if st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
      return none
    let rc ← StateT.lift (hop2Unif (Pt := Pt))
    match ← hop2Recv P Dh encT decT h (st.1.st Q) c rc with
    | none => return some .rejected
    | some ((st', t', i', m'), u) =>
      let st2 ← get
      let aux := { st2.2 with bad := st2.2.bad || hop2BadAt P s (st.1.st Q) c }
      if qep + 1 < t' then
        set (st2.1, aux)
        return some .rejected
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st2.1.trivial 3 pos then
        set (st2.1.accept Q st' pos, hop2Commit aux Q u)
        return some (.accepted t' i' (some m'))
      else
        set ({ st2.1 with win := true }, aux)
        return some .rejected

def hop2Impl (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (Hop2M Pt ℓ)
  | .inl u => StateT.lift (query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u))
  | .inr (.inl (.inl (.inl (.inl y)))) =>
    hop2Lift (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inl (.inr y)))) =>
    hop2Lift (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) y)
  | .inr (.inl (.inl (.inr y))) => hop2Deliver P Dh encT decT s h y
  | .inr (.inl (.inr y)) => hop2Inject P Dh encT decT qep s h y
  | .inr (.inr y) => hop2Lift (SM.corrR (configRefuseEarlyBobCorr decT encT) y)

/-- Hybrid game `G(k)` for `A` in Hop 2's uniform-SPK world, returning the bad-event flag. -/
def hop2Game (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) : Hop2Comp Pt Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : Hop2Comp Pt Bool)
  let ck0 ← hop2Unif (Pt := Pt)
  let x ← hop2Unif (Pt := Pt)
  let alice ← hop2Unif (Pt := Pt)
  let pqr ← hop2Unif (Pt := Pt)
  let u1 ← hop2Unif (Pt := Pt)
  let ck1 := if h.k = 0 then h.chall.2 else u1
  let I0 := Dh.dh x (Dh.dh alice Dh.base)
  let spk := (KeyPair.generate P.C x).publicKey
  let sessA := ((SessionState.new currentVersion P.idA P.idB 0
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    (KeyPair.generate P.C alice) ⟨ck1, 0⟩
  let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
  let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
  let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
    { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
  let aux0 : Hop2Aux Pt :=
    { made := [((0, I0), ck1)]
      idx := fun Q => match Q with | .A => some 1 | .B => some 0
      coins := fun Q => match Q with | .A => alice | .B => x }
  let (_, fin) ← (simulateQ (hop2Impl P Dh encT decT qep s h) A).run (initSt, aux0)
  return fin.2.bad

/-- Hop 2 PRG reduction against `expandPRG` at hybrid `k`. -/
def hop2PrgRedK (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    PRGScheme.PRGAdversary (Ratchet.RootKey × BitVec 256) := fun rc =>
  let step : Pt → Hop2Comp Pt (BitVec 256) := fun I =>
    (pure ((extractPRF P.C.F encPt).tag rc.1 I) : Hop2Comp Pt (BitVec 256))
  let prfReal : QueryImpl (prfSpec Pt (BitVec 256)) ProbComp := fun I =>
    (pure ((extractPRF P.C.F encPt).tag rc.1 I) : ProbComp (BitVec 256))
  let impl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp :=
    QueryImpl.ofLift unifSpec ProbComp + prfReal
  simulateQ impl (hop2Game P ℓ Dh encT decT qep s ⟨k, rc, step⟩ A)

/-- Hop 2 PRF reduction against `extractPRF` at hybrid `k`. -/
def hop2PrfRedK (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) := (do
  let r ← hop2Unif (Pt := Pt)
  let c ← hop2Unif (Pt := Pt)
  hop2Game P ℓ Dh encT decT qep s
    ⟨k, (r, c), fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I⟩ A :
    Hop2Comp Pt Bool)

end Hop2

end CryptoVerification.E2E
