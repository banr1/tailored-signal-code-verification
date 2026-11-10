/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Auth1KeyStatements

/-!
# One-key `Auth` oracle in the two-key match shape

Defines `pqxdhAuthImpl1KeyG`, which matches `pqxdhAuthImpl` except that `.initPrin` samples a
single Curve25519 scalar shared by X25519 and XEdDSA (`pqxdhAuthImpl1KeyG true true = pqxdhAuthImpl1Key`),
and proves agreement with `pqxdhAuthImpl` on all non-`.initPrin` queries.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Stage-flag one-key `Auth` oracle agreeing with `pqxdhAuthImpl` outside `.initPrin`. -/
def pqxdhAuthImpl1KeyG (useRo checkAuth : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q => do
  let st ← get
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM sampleScalar32
    let ikAPk := P.x25519Base secIKA0
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKA0
      ikSignPk   := ikAPk
      corrupted  := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikAPk
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return .noneResp
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      set { st with principals := principals' }
      return .corrResp entry.secIKA0 entry.secIKAsign
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return .noneResp
    let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
      | return .noneResp
    let spkSk ← liftM sampleScalar32
    let spkPk := P.x25519Base spkSk
    let rSpk ← liftM sampleRandom64
    let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
    let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
    let rPq ← liftM sampleRandom64
    let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    set { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return .bundleResp bundleOut
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return .noneResp
    let opkSk ← liftM sampleScalar32
    let opkPk := P.x25519Base opkSk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    set { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
    return .pkResp opkPk
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return .noneResp
    runAuthSend useRo S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return .noneResp
    runAuthSend useRo S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    -- Reject non-canonical ratchet keys `msg.ephAPk` (DEV-PQ16).
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
      return .noneResp
    if msg.hdr.kemCt.length != kyberCtLen then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some (_, senderEntry) =>
      if !senderEntry.corrupted then
        let recvEv : RecvdOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        let (matchedOk, sentOPK') := consumeMatchingSentOPK P recvEv st.sentOPKEvents
        let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
        set { st with
          hasWonAuth       := wonAuth'
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          sentOPKEvents    := sentOPK'
          recvdOPKEvents   := recvEv :: st.recvdOPKEvents
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
      else
        set { st with
          opkEntries       := opkEntries'
          usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
    | none =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .recvNoOPK k j l msg =>
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
      return .noneResp
    if msg.hdr.kemCt.length != kyberCtLen then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo useRo P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some (_, senderEntry) =>
      if !senderEntry.corrupted then
        let recvEv : RecvdNoOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        let (matchedOk, sentNoOPK') := consumeMatchingSentNoOPK P recvEv st.sentNoOPKEvents
        let wonAuth' := st.hasWonAuth || (checkAuth && !matchedOk)
        set { st with
          hasWonAuth       := wonAuth'
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          sentNoOPKEvents  := sentNoOPK'
          recvdNoOPKEvents := recvEv :: st.recvdNoOPKEvents
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
      else
        set { st with
          usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
          seenKyberBaseKeys := usedTriples'
          roCache          := roCache'
          rootRoCache      := rootRoCache' }
        return .recvHonestResp
    | none =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .registerKey sk =>
    match registerAdvKey P st.advKeys sk with
    | none => return .noneResp
    | some (pk, advKeys') =>
      set { st with advKeys := advKeys' }
      return .pkResp pk
  | .roQuery secrets =>
    if !useRo then
      return .noneResp
    let (dk, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    set { st with roCache := roCache' }
    return .drKeyResp dk
  | .roRootQuery rk dh =>
    if !useRo then
      return .noneResp
    let (out, rootRoCache') ← liftM (evalRootKdfOrRo true P st.rootRoCache rk dh)
    set { st with rootRoCache := rootRoCache' }
    return .rootKdfResp out.1 out.2
  | .revealDhSecrets =>
    if useRo then
      return .noneResp
    let ikDhSks := st.principals.map (fun (_, e) => e.secIKA0)
    let spkSks  := st.spkBundles.map (fun (_, b) => b.spkSk)
    let opkSks  := st.opkEntries.map (fun (_, o) => o.opkSk)
    let ekSks   := (st.sessions.map (fun s => s.ekASk)) ++ (st.sessions.map (fun s => s.ephASk))
    return .dhSecretsResp ikDhSks spkSks opkSks ekSks

theorem pqxdhAuthImpl1KeyG_true_true (S : Setup) (P : Primitives) :
    pqxdhAuthImpl1KeyG true true S P = pqxdhAuthImpl1Key S P := by
  funext q
  cases q <;> rfl

theorem pqxdhAuthImpl1KeyG_eq_of_ne_initPrin (useRo checkAuth : Bool) (S : Setup)
    (P : Primitives) (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthImpl1KeyG useRo checkAuth S P q = pqxdhAuthImpl useRo checkAuth S P q := by
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | _ => rfl

theorem pqxdhAuth1KeyExp_eq_with_1KeyG (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    pqxdhAuth1KeyExp S P A =
      pqxdhAuthExpCoreWith true true S P (pqxdhAuthImpl1KeyG true true S P) A := by
  rw [pqxdhAuthImpl1KeyG_true_true]; rfl

end SignalPqxdh
