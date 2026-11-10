/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh

/-!
# Black-Box Reductions for PQXDH `Auth`: Handshake Simulators

**Checked by Lean.** Shallow reduction simulators (`sigReductionAuth`, `shcrReductionAuth`, and
`fgAuthGapDhAdv4`) for the handshake game hops of the PQXDH `Auth` security game.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open FgGapDh

/-! ## `SigEufCma` simulator -/

def evalRootKdfOrRoPrim (useRo : Bool)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (rk dh : Bytes) :
    OracleComp PrimBaseSpec ((Bytes × Bytes) × List ((Bytes × Bytes) × (Bytes × Bytes))) := do
  if !useRo then
    let out ← primQ (.rootCreateChain rk dh)
    return (out, rootRoCache)
  else
    match rootRoCache.find? (fun (inp, _) => inp == (rk, dh)) with
    | some (_, out) => return (out, rootRoCache)
    | none =>
      let rk1 ← embedUnif sampleBytes32
      let ck1 ← embedUnif sampleBytes32
      return ((rk1, ck1), ((rk, dh), (rk1, ck1)) :: rootRoCache)

def runAuthSendSimPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let st ← get
  if m0.length != m1.length then return .noneResp
  if st.usedSendSessions.contains sid then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let peerPrincipal? ← liftM (findHonestPrincipalPrim S st.principals bundle.ikB)
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return .noneResp
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  let koskOk ← liftM (koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys
      bundle)
  if !koskOk then
    return .noneResp
  let ekASk ← liftM (embedUnif sampleScalar32)
  let kemCoins ← liftM (embedUnif sampleCoins32)
  let ephASk ← liftM (embedUnif sampleScalar32)
  let spqrCoins ← liftM (embedUnif sampleCoins32)
  let sigPkB ← liftM (resolveSigPkPrim S st.principals bundle.ikB)
  let v1 ← liftM (primQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig))
  let v2 ← liftM (primQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig))
  if !(v1 && v2) then
    return .noneResp
  let some (ss, kemCt) ← liftM (primQ (.kemEncaps bundle.pqspkB kemCoins))
    | return .noneResp
  let ekAPk ← liftM (primQ (.x25519Base ekASk))
  let dh1 ← liftM (primQ (.x25519 uEntry.secIKA0 bundle.spkB))
  let dh2 ← liftM (primQ (.x25519 ekASk bundle.ikB))
  let dh3 ← liftM (primQ (.x25519 ekASk bundle.spkB))
  let dh4 ← liftM (primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD [])))
  let dh4? := bundle.opkB?.map (fun _ => dh4)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← liftM (evalHkdfOrRoPrim true st.roCache secrets)
  let ephAPk ← liftM (primQ (.x25519Base ephASk))
  let dhRatchet ← liftM (primQ (.x25519 ephASk bundle.spkB))
  let (rkCk, rootRoCache') ←
    liftM (evalRootKdfOrRoPrim true st.rootRoCache drKey.rootKey dhRatchet)
  let mkSeed ← liftM (primQ (.chainKdfSeed rkCk.2))
  let ck1_1 ← liftM (primQ (.chainKdfNext rkCk.2))
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) ← liftM (primQ (.spqrInitSend drKey.pqrKey spqrCoins))
    | return .noneResp
  let deriveMessageKeys ← liftM (primQ (.deriveMsgKeys mkSeed spqrSalt?))
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt ← liftM (primQ (.aeadEnc deriveMessageKeys ad msgPlain))
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let wireMsg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  let (spkHon, opkHon, pqspkHon) :=
    match peerPrincipal? with
    | none => (false, false, false)
    | some (k, _) =>
      (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
       false,
       st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
  let sessEntry : AuthInitiatorEntry S := {
    sid         := sid
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    ephASk      := ephASk
    fresh       := isFreshPeer
    challenged  := isFreshPeer && (m0 != m1)
  }
  set { st with
    sessions         := sessEntry :: st.sessions
    usedSendSessions := sid :: st.usedSendSessions
    roCache          := roCache'
    rootRoCache      := rootRoCache' }
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rkCk.1 ck1_1 wireMsg

def runAuthRecvStep2SimPrim (S : Setup)
    (st : AuthState S) (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (drKey : DRKey) (roCache' : List (Bytes × DRKey))
    (rk1 : Bytes) (ck1_1 : Bytes) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (mkSeed : Bytes) (spqrSalt? : Option Bytes)
    (opkEntries' : List ((Nat × Nat × Nat) × OpkEntry))
    (usedRecvOPK' : List (Nat × Nat × Nat))
    (usedRecvNoOPK' : List (Nat × Nat × Nat))
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) :
    StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let deriveMessageKeys ← liftM (primQ (.deriveMsgKeys mkSeed spqrSalt?))
  let pt? ← liftM (primQ (.aeadDec deriveMessageKeys (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk
      msg.pqRatchetMsg) msg.aeadCt))
  match pt? with
  | none => pure .noneResp
  | some pt =>
    let sender? ← liftM (findHonestPrincipalPrim S st.principals msg.hdr.ikAPk)
    match sender? with
    | some _ =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := usedRecvOPK'
        usedRecvNoOPK    := usedRecvNoOPK'
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      pure .recvHonestResp
    | none =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := usedRecvOPK'
        usedRecvNoOPK    := usedRecvNoOPK'
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      pure (.recvUnfreshResp drKey rk1 ck1_1 pt)

def runAuthRecvFinishSimPrim (S : Setup)
    (st : AuthState S) (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (drKey : DRKey) (roCache' : List (Bytes × DRKey))
    (rk1 : Bytes) (ck1_0 : Bytes) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (opkEntries' : List ((Nat × Nat × Nat) × OpkEntry))
    (usedRecvOPK' : List (Nat × Nat × Nat))
    (usedRecvNoOPK' : List (Nat × Nat × Nat))
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) :
    StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let mkSeed ← liftM (primQ (.chainKdfSeed ck1_0))
  let ck1_1 ← liftM (primQ (.chainKdfNext ck1_0))
  let spqr? ← liftM (primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg))
  match spqr? with
  | none => pure .noneResp
  | some (_, spqrSalt?) =>
    runAuthRecvStep2SimPrim S st kEntry msg drKey roCache' rk1 ck1_1 rootRoCache' mkSeed spqrSalt?
      opkEntries' usedRecvOPK' usedRecvNoOPK' usedTriples'

def runAuthRecvOPKSimPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) :
    StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let st ← get
  if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    pure .noneResp
  else if st.usedRecvOPK.contains (k.val, j.val, o.val) then
    pure .noneResp
  else
    let koskOk ← liftM (koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk)
    if !koskOk then
      pure .noneResp
    else
      match st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => pure .noneResp
      | some (_, kEntry) =>
        match st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => pure .noneResp
        | some (_, bEntry) =>
          match st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => pure .noneResp
          | some (_, oEntry) =>
            if oEntry.consumed then
              pure .noneResp
            else
              let canOk ← liftM (primQ (.isCanonical msg.hdr.ekAPk))
              let canEphOk ← liftM (primQ (.isCanonical msg.ephAPk))
              if !(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
                msg.hdr.ekAPk).1 || !canOk || !canEphOk then
                pure .noneResp
              else
                let ss? ← liftM (primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt))
                match ss? with
                | none => pure .noneResp
                | some ss =>
                  let dh1 ← liftM (primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk))
                  let dh2 ← liftM (primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk))
                  let dh3 ← liftM (primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk))
                  let dh4 ← liftM (primQ (.x25519 oEntry.opkSk msg.hdr.ekAPk))
                  let drOut ← liftM (evalHkdfOrRoPrim true st.roCache (buildSecrets dh1 dh2 dh3
                      (some dh4) ss))
                  let dhRatchet ← liftM (primQ (.x25519 bEntry.spkSk msg.ephAPk))
                  let rkOut ← liftM (evalRootKdfOrRoPrim true st.rootRoCache drOut.1.rootKey
                      dhRatchet)
                  let opkEntries' : List ((Nat × Nat × Nat) × OpkEntry) :=
                    st.opkEntries.map (fun ((idx, e) : (Nat × Nat × Nat) × OpkEntry) =>
                      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                        (idx, e))
                  runAuthRecvFinishSimPrim S st kEntry msg drOut.1 drOut.2 rkOut.1.1 rkOut.1.2
                    rkOut.2
                    opkEntries'
                    ((k.val, j.val, o.val) :: st.usedRecvOPK)
                    st.usedRecvNoOPK
                    (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
                      msg.hdr.ekAPk).2

def runAuthRecvNoOPKSimPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) :
    StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let st ← get
  if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    pure .noneResp
  else if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    pure .noneResp
  else
    let koskOk ← liftM (koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk)
    if !koskOk then
      pure .noneResp
    else
      match st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => pure .noneResp
      | some (_, kEntry) =>
        match st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => pure .noneResp
        | some (_, bEntry) =>
          let canOk ← liftM (primQ (.isCanonical msg.hdr.ekAPk))
          let canEphOk ← liftM (primQ (.isCanonical msg.ephAPk))
          if !(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
            msg.hdr.ekAPk).1 || !canOk || !canEphOk then
            pure .noneResp
          else
            let ss? ← liftM (primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt))
            match ss? with
            | none => pure .noneResp
            | some ss =>
              let dh1 ← liftM (primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk))
              let dh2 ← liftM (primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk))
              let dh3 ← liftM (primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk))
              let drOut ← liftM (evalHkdfOrRoPrim true st.roCache (buildSecrets dh1 dh2 dh3 none
                  ss))
              let dhRatchet ← liftM (primQ (.x25519 bEntry.spkSk msg.ephAPk))
              let rkOut ← liftM (evalRootKdfOrRoPrim true st.rootRoCache drOut.1.rootKey dhRatchet)
              runAuthRecvFinishSimPrim S st kEntry msg drOut.1 drOut.2 rkOut.1.1 rkOut.1.2 rkOut.2
                st.opkEntries
                st.usedRecvOPK
                ((k.val, j.val, l.val) :: st.usedRecvNoOPK)
                (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
                  msg.hdr.ekAPk).2

def pqxdhAuthSimImplPrim (S : Setup) :
    QueryImpl (authSpec S) (StateT (AuthState S) (OracleComp PrimBaseSpec)) := fun q =>
  match q with
  | .initPrin u => do
    let st ← get
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM (embedUnif sampleScalar32)
    let ikAPk ← liftM (primQ (.x25519Base secIKA0))
    let secIKAsign ← liftM (embedUnif sampleScalar32)
    let ikSignPk ← liftM (primQ (.sigPkGen secIKAsign))
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKAsign
      ikSignPk   := ikSignPk
      corrupted  := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikSignPk
  | .corruptIK u => do
    let st ← get
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return .noneResp
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      set { st with principals := principals' }
      return .corrResp entry.secIKA0 entry.secIKAsign
  | .genSPK u j => do
    let st ← get
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return .noneResp
    let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
      | return .noneResp
    let spkSk ← liftM (embedUnif sampleScalar32)
    let spkPk ← liftM (primQ (.x25519Base spkSk))
    let rSpk ← liftM (embedUnif sampleRandom64)
    let spkSig ← liftM (primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk))
    let (pqspkPk, pqspkSk) ← liftM sampleKemKeyGenPrim
    let rPq ← liftM (embedUnif sampleRandom64)
    let pqspkSig ← liftM (primQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq))
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
  | .genOPK u j o => do
    let st ← get
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return .noneResp
    let opkSk ← liftM (embedUnif sampleScalar32)
    let opkPk ← liftM (primQ (.x25519Base opkSk))
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    set { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
    return .pkResp opkPk
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthSendSimPrim S (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthSendSimPrim S (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    runAuthRecvOPKSimPrim S k j o msg
  | .recvNoOPK k j l msg =>
    runAuthRecvNoOPKSimPrim S k j l msg
  | .roQuery secrets => do
    let st ← get
    let (dk, roCache') ← liftM (evalHkdfOrRoPrim true st.roCache secrets)
    set { st with roCache := roCache' }
    return .drKeyResp dk
  | .roRootQuery rk dh => do
    let st ← get
    let ((rk1, ck1), rootRoCache') ← liftM (evalRootKdfOrRoPrim true st.rootRoCache rk dh)
    set { st with rootRoCache := rootRoCache' }
    return .rootKdfResp rk1 ck1
  | .revealDhSecrets => do
    return .noneResp
  | .registerKey sk => do
    let st ← get
    if sk.length != 32 then return .noneResp
    let pk ← liftM (primQ (.x25519Base sk))
    let p8 ← liftM (primQ (.pow8 pk))
    set { st with advKeys := (p8, pk) :: st.advKeys }
    return .pkResp pk

def stepAuthForSigPrim (S : Setup)
    (q : AuthQuery S) (s : SigReductionState (AuthState S)) :
    OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState (AuthState S)) AuthResponse) := do
  if s.forgery.isSome then
    return .done .noneResp s
  else
    match q with
    | .initPrin u =>
      if s.gameState.principals.any (fun (idx, _) => idx == u.val) then
        return .done .noneResp s
      else if u.val == s.targetParty then
        let secIKA0 ← embedUnif sampleScalar32
        let ikAPk ← primQ (.x25519Base secIKA0)
        let entry : PrincipalEntry := {
          secIKA0    := secIKA0
          ikAPk      := ikAPk
          secIKAsign := []
          ikSignPk   := s.targetPk
          corrupted  := false
        }
        let gs' := { s.gameState with principals := (u.val, entry) :: s.gameState.principals }
        return .done (.initPrinResp ikAPk s.targetPk) { s with gameState := gs' }
      else
        let (out, gs') ← (pqxdhAuthSimImplPrim S (.initPrin u)).run s.gameState
        return .done out { s with gameState := gs' }
    | .corruptIK u =>
      if u.val == s.targetParty then
        match s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
        | none => return .done .noneResp s
        | some _ =>
          let principals' := s.gameState.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
          return .done .noneResp { s with gameState := { s.gameState with principals := principals'
            } }
      else
        let (out, gs') ← (pqxdhAuthSimImplPrim S (.corruptIK u)).run s.gameState
        return .done out { s with gameState := gs' }
    | .genSPK u j =>
      if u.val == s.targetParty then
        if s.gameState.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
          return .done .noneResp s
        else
          match s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
          | none => return .done .noneResp s
          | some (_, uEntry) =>
            let spkSk ← embedUnif sampleScalar32
            let spkPk ← primQ (.x25519Base spkSk)
            return .signTwo (encodeEC spkPk)
              (fun (pqspkPk, pqspkSk) spkSig =>
                (encodeKEM pqspkPk, fun pqspkSig =>
                  let bEntry : SpkBundleEntry := {
                    spkSk    := spkSk
                    spkPk    := spkPk
                    spkSig   := spkSig
                    pqspkSk  := pqspkSk
                    pqspkPk  := pqspkPk
                    pqspkSig := pqspkSig
                  }
                  let gs' := { s.gameState with spkBundles := ((u.val, j.val), bEntry) ::
                      s.gameState.spkBundles }
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
                  (.bundleResp bundleOut, { s with gameState := gs' })))
              (.noneResp, s)
      else
        let (out, gs') ← (pqxdhAuthSimImplPrim S (.genSPK u j)).run s.gameState
        return .done out { s with gameState := gs' }
    | .sendOPK u i bundle m0 m1 =>
      let forgery' ← extractBundleForgeryPrim S s.targetParty s.targetPk
        s.gameState.principals s.gameState.spkBundles bundle s.forgery
      let (out, gs') ← (pqxdhAuthSimImplPrim S (.sendOPK u i bundle m0 m1)).run s.gameState
      return .done out { s with gameState := gs', forgery := forgery' }
    | .sendNoOPK u i bundle m0 m1 =>
      let forgery' ← extractBundleForgeryPrim S s.targetParty s.targetPk
        s.gameState.principals s.gameState.spkBundles bundle s.forgery
      let (out, gs') ← (pqxdhAuthSimImplPrim S (.sendNoOPK u i bundle m0 m1)).run s.gameState
      return .done out { s with gameState := gs', forgery := forgery' }
    | q_other =>
      let (out, gs') ← (pqxdhAuthSimImplPrim S q_other).run s.gameState
      return .done out { s with gameState := gs' }

@[reducible]
def simulateAuthForSigPrim (S : Setup) (targetParty : Nat) (targetPk : Bytes)
    (A : AuthAdversary S) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes) :=
  simulateForSigPrim S (AuthState.empty S) (stepAuthForSigPrim S) targetParty targetPk A.run

def sigReductionAuthAt (S : Setup) (b : QueryBudget) (k : Nat)
    (A : BoundedAdv (AuthAdversary S) b) : SigEufCmaAdv where
  run := fun pk => simulateAuthForSigPrim S k pk A.val
  q_sig := 2 * S.N_spk_tot
  q_prim := b.q_total * (S.N_dh * 14 + 23)

def sigReductionAuthRun (S : Setup) (A : AuthAdversary S) (pk : Bytes) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (Bytes × Bytes) :=
  if hN : 0 < S.N_id then
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    do
      let k ← embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id)))
      simulateAuthForSigPrim S k.val pk A
  else
    pure ([], [])

/-- `SigEufCma` reduction adversary for `Auth` embedding the challenge verification key at a
    uniformly sampled principal. -/
def sigReductionAuth (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : SigEufCmaAdv where
  run := sigReductionAuthRun S A.val
  q_sig := 2 * S.N_spk_tot
  q_prim := b.q_total * (S.N_dh * 14 + 23)

/-! ## `KemShCr` simulator -/

abbrev AuthShCrState (S : Setup) := ShCrState S (AuthState S)

def isNoneAuthShCrResp (_ : AuthResponse) : Bool := false

def runAuthShCrAcceptPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : AuthQuery S) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let out ← liftShCrBasePrim (pqxdhAuthSimImplPrim S gq)
  recordAcceptKemGenericPrim AuthState.spkBundles isNoneAuthShCrResp k j hdr out

def genSpkTargetAuthPrim (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := fun hst => do
  let st := hst.base
  if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
    return (.noneResp, hst)
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, hst)
  let spkSk ← embedUnif sampleScalar32
  let spkPk ← primQ (.x25519Base spkSk)
  let rSpk ← embedUnif sampleRandom64
  let spkSig ← primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
  let pqspkPk := hst.targetPk
  let pqspkSk := hst.targetSk
  let rPq ← embedUnif sampleRandom64
  let pqspkSig ← primQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq)
  let bEntry : SpkBundleEntry := {
    spkSk    := spkSk
    spkPk    := spkPk
    spkSig   := spkSig
    pqspkSk  := pqspkSk
    pqspkPk  := pqspkPk
    pqspkSig := pqspkSig
  }
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
  return (.bundleResp bundleOut,
    { hst with base := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles } })

def runAuthShCrGenSPKPrim (embedTarget : Bool) (S : Setup)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := fun hst =>
  if !embedTarget then
    (liftShCrBasePrim (pqxdhAuthSimImplPrim S (.genSPK u j))).run hst
  else
    match hst.targetBIdx? with
    | none => (liftShCrBasePrim (pqxdhAuthSimImplPrim S (.genSPK u j))).run hst
    | some bIdx =>
      if RoKem.spkBundleFlatIdx S u j == bIdx then
        (genSpkTargetAuthPrim S u j).run hst
      else
        (liftShCrBasePrim (pqxdhAuthSimImplPrim S (.genSPK u j))).run hst

def preCheckAuthSimPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) : OracleComp PrimBaseSpec (Option (PrincipalEntry × Option (Nat ×
        PrincipalEntry) × Bytes)) :=
  if m0.length != m1.length then pure none
  else if st.usedSendSessions.contains sid then pure none
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure none
    | some (_, uEntry) => do
      let peerPrincipal? ← findHonestPrincipalPrim S st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then return none
      else
        let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
        if !koskOk then return none
        else
          let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
          return some (uEntry, peerPrincipal?, msgPlain)

def finishAuthSimBasePrim (S : Setup)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (ekASk ephASk spqrCoins ss kemCt : Bytes) (st : AuthState S) :
    OracleComp PrimBaseSpec (AuthResponse × Option (AuthState S)) := do
  let (uEntry, peerPrincipal?, msgPlain) := uInfo
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ekAPk ← primQ (.x25519Base ekASk)
  let dh1 ← primQ (.x25519 uEntry.secIKA0 bundle.spkB)
  let dh2 ← primQ (.x25519 ekASk bundle.ikB)
  let dh3 ← primQ (.x25519 ekASk bundle.spkB)
  let dh4 ← primQ (.x25519 ekASk (bundle.opkB?.map Prod.snd |>.getD []))
  let dh4? := bundle.opkB?.map (fun _ => dh4)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← evalHkdfOrRoPrim true st.roCache secrets
  let ephAPk ← primQ (.x25519Base ephASk)
  let dhRatchet ← primQ (.x25519 ephASk bundle.spkB)
  let ((rk1, ck1_0), rootRoCache') ←
    evalRootKdfOrRoPrim true st.rootRoCache drKey.rootKey dhRatchet
  let mkSeed ← primQ (.chainKdfSeed ck1_0)
  let ck1_1 ← primQ (.chainKdfNext ck1_0)
  match ← primQ (.spqrInitSend drKey.pqrKey spqrCoins) with
  | none => return (.noneResp, none)
  | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
    let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
    let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
    let aeadCt ← primQ (.aeadEnc deriveMessageKeys ad msgPlain)
    let hdr : HandshakeHdr := {
      ikAPk   := uEntry.ikAPk
      ekAPk   := ekAPk
      spkId   := bundle.spkId
      opkId?  := bundle.opkB?.map Prod.fst
      pqspkId := bundle.pqspkId
      kemCt   := kemCt
    }
    let wireMsg : PreKeyMsg := {
      hdr          := hdr
      ephAPk       := ephAPk
      pqRatchetMsg := pqRatchetMsg
      aeadCt       := aeadCt
    }
    let (spkHon, opkHon, pqspkHon) :=
      match peerPrincipal? with
      | none => (false, false, false)
      | some (k, _) =>
        (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
         false,
         st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
    let sessEntry : AuthInitiatorEntry S := {
      sid         := sid
      peerIkPk    := bundle.ikB
      peerSpkPk   := bundle.spkB
      peerOpkPk?  := bundle.opkB?.map Prod.snd
      peerPqspkPk := bundle.pqspkB
      spkHonest   := spkHon
      opkHonest   := opkHon
      pqspkHonest := pqspkHon
      ekASk       := ekASk
      ephASk      := ephASk
      fresh       := isFreshPeer
      challenged  := isFreshPeer && (m0 != m1)
    }
    let base' : AuthState S := { st with
      sessions         := sessEntry :: st.sessions
      usedSendSessions := sid :: st.usedSendSessions
      roCache          := roCache'
      rootRoCache      := rootRoCache' }
    let resp : AuthResponse :=
      if peerPrincipal?.isSome then .sendFreshResp wireMsg
      else .sendUnfreshResp drKey rk1 ck1_1 wireMsg
    return (resp, some base')

def postKemAuthPrim (S : Setup)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uInfo : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes)
    (hst : AuthShCrState S) (ss kemCt : Bytes) :
    OracleComp PrimBaseSpec (AuthResponse × AuthShCrState S) := do
  let ekASk ← embedUnif sampleScalar32
  let ephASk ← embedUnif sampleScalar32
  let spqrCoins ← embedUnif sampleCoins32
  let out ← finishAuthSimBasePrim S sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt hst.base
  return applyShCrFinish sid bundle.pqspkB ss kemCt hst out

def runAuthShCrSendPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := fun hst => do
  match ← preCheckAuthSimPrim S sid u bundle m0 m1 hst.base with
  | none => return (.noneResp, hst)
  | some uInfo =>
    let ekASk ← embedUnif sampleScalar32
    let kemCoins ← embedUnif sampleCoins32
    let ephASk ← embedUnif sampleScalar32
    let spqrCoins ← embedUnif sampleCoins32
    let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
    if !sigOk then
      return (.noneResp, hst)
    else
      match ← primQ (.kemEncaps bundle.pqspkB kemCoins) with
      | none =>
        return (.noneResp, { hst with sendCount := hst.sendCount + 1 })
      | some (ss, kemCt) =>
        let out ← finishAuthSimBasePrim S sid bundle m0 m1 uInfo ekASk ephASk spqrCoins ss kemCt
            hst.base
        return applyShCrFinish sid bundle.pqspkB ss kemCt hst out

def pqxdhAuthShCrPrimImpl (embedTarget : Bool) (S : Setup) :
    QueryImpl (authSpec S) (StateT (AuthShCrState S) (OracleComp PrimBaseSpec))
  | .genSPK u j => runAuthShCrGenSPKPrim embedTarget S u j
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure .noneResp
    else runAuthShCrSendPrim S (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure .noneResp
    else runAuthShCrSendPrim S (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    runAuthShCrAcceptPrim S k j msg.hdr (.recvOPK k j o msg)
  | .recvNoOPK k j l msg =>
    runAuthShCrAcceptPrim S k j msg.hdr (.recvNoOPK k j l msg)
  | q_other => liftShCrBasePrim (pqxdhAuthSimImplPrim S q_other)

structure PausedShCrAuthData (S : Setup) where
  sid    : SessionId S
  bundle : PreKeyBundleInput
  m0     : Bytes
  m1     : Bytes
  uInfo  : PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes
  hst    : AuthShCrState S
  cont   : AuthResponse → OracleComp (unifSpec + authSpec S) Bool

def tryPauseAuthQueryPrim (S : Setup) (sIdx : Nat) (gq : AuthQuery S)
    (cont : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) : OracleComp PrimBaseSpec (Option (PausedShCrAuthData S)) :=
  match gq, cont with
  | .sendOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isNone then pure none
    else do
      match ← preCheckAuthSimPrim S (.sendOPK u i) u bundle m0 m1 hst.base with
      | none => pure none
      | some uInfo =>
        let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
        if !sigOk then pure none
        else if hst.sendCount == sIdx then
          pure (some {
            sid    := .sendOPK u i
            bundle := bundle
            m0     := m0
            m1     := m1
            uInfo  := uInfo
            hst    := hst
            cont   := cont
          })
        else pure none
  | .sendNoOPK u i bundle m0 m1, cont =>
    if bundle.opkB?.isSome then pure none
    else do
      match ← preCheckAuthSimPrim S (.sendNoOPK u i) u bundle m0 m1 hst.base with
      | none => pure none
      | some uInfo =>
        let sigOk ← checkBundleSigsPrim S hst.base.principals bundle
        if !sigOk then pure none
        else if hst.sendCount == sIdx then
          pure (some {
            sid    := .sendNoOPK u i
            bundle := bundle
            m0     := m0
            m1     := m1
            uInfo  := uInfo
            hst    := hst
            cont   := cont
          })
        else pure none
  | _, _ => pure none

def runWithFuelAuthShCrPrim (S : Setup)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Bool × AuthShCrState S) :=
  OracleComp.construct
    (C := fun _ => AuthShCrState S → ℕ → OracleComp PrimBaseSpec (Bool × AuthShCrState S))
    (fun b hst _ => return (b, hst))
    (fun q _ r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return (false, hst)
        | f + 1 => do
          let (out, hst') ← (pqxdhAuthShCrPrimImpl true S gq).run hst
          r out hst' f)
    oa hst fuel

def stepUntilShCrFuelAuthPrim (S : Setup) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (hst : AuthShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Sum (Bool × AuthShCrState S) (PausedShCrAuthData S)) :=
  OracleComp.construct
    (C := fun _ => AuthShCrState S → ℕ → OracleComp PrimBaseSpec (Sum (Bool × AuthShCrState S)
      (PausedShCrAuthData S)))
    (fun b hst _ => return Sum.inl (b, hst))
    (fun q cont r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return Sum.inl (false, hst)
        | f + 1 => do
          match ← tryPauseAuthQueryPrim S sIdx gq cont hst with
          | some d => return Sum.inr d
          | none =>
            let (out, hst') ← (pqxdhAuthShCrPrimImpl true S gq).run hst
            r out hst' f)
    oa hst fuel

def resumePausedAuthPrim (S : Setup) (fuel : ℕ) (d : PausedShCrAuthData S)
    (ss kemCt : Bytes) : OracleComp PrimBaseSpec (Bool × AuthShCrState S) := do
  let (resp, hst') ← postKemAuthPrim S d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss kemCt
  runWithFuelAuthShCrPrim S (d.cont resp) hst' fuel

abbrev AuthShCrFinishState (S : Setup) :=
  Bytes × Bytes × Bytes × Sum (Bool × AuthShCrState S) (PausedShCrAuthData S)

def choosePkAuthPrimAt (S : Setup) (b : QueryBudget) (bIdx sIdx : ℕ)
    (A : AuthAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (Bytes × AuthShCrFinishState S) := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt : AuthShCrState S := {
    base        := AuthState.empty S secb
    targetBIdx? := some bIdx
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCrFuelAuthPrim S sIdx A.run initSt b.q_total
  let chosenPk := match res with
    | Sum.inl _ => pk
    | Sum.inr d => d.bundle.pqspkB
  return (chosenPk, (pk, sk, chosenPk, res))

def findCollisionAuthPrim (S : Setup) (b : QueryBudget)
    (st : AuthShCrFinishState S) (ss ct : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let (pk, sk, chosenPk, res) := st
  let (_, finalHst) ← match res with
    | Sum.inl done => pure done
    | Sum.inr d    => resumePausedAuthPrim S b.q_total d ss ct
  extractCollidingKemCtPrim b.q_total pk sk chosenPk ct ss finalHst.recvKemRecs

def shcrReductionAuthAt (S : Setup) (b : QueryBudget) (idx : ℕ)
    (A : AuthAdversary S) : KemShCrAdv where
  State := AuthShCrFinishState S
  choosePk := choosePkAuthPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A
  findCollision := findCollisionAuthPrim S b
  q_prim := primQueryBudget S b

def shcrReductionAuthCore (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := AuthShCrFinishState S
  choosePk := fun pk sk => do
    let idx ← embedUnif (sampleIndexRange (S.N_spk_tot * S.N_send_tot))
    choosePkAuthPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk
  findCollision := findCollisionAuthPrim S b
  q_prim := primQueryBudget S b

/-- `KemShCr` reduction adversary for `Auth` pausing at a uniformly sampled bundle and initiator
    session pair. -/
def shcrReductionAuth (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : KemShCrAdv :=
  shcrReductionAuthCore S b A.val

/-! ## `GapDH` simulator -/

structure FgRootEntry where
  rk    : Bytes
  dhPos : FgPoS
  rk1   : Bytes
  ck1_0 : Bytes

def fgRootEntryMatches (rk : Bytes) (dhPos : FgPoS) (e : FgRootEntry) :
    OracleComp GdhSimSpec Bool := do
  if rk != e.rk then return false
  ddhEqGdh dhPos e.dhPos

def fgRootPatch (maxLen : ℕ) (rk : Bytes) (dhPos : FgPoS) (L : List FgRootEntry) :
    OracleComp GdhSimSpec ((Bytes × Bytes) × List FgRootEntry) := do
  match ← findMGdh (fgRootEntryMatches rk dhPos) (L.take maxLen) with
  | some e => return ((e.rk1, e.ck1_0), L)
  | none =>
    let rk1 ← unifGdh sampleBytes32
    let ck1_0 ← unifGdh sampleBytes32
    return ((rk1, ck1_0), { rk := rk, dhPos := dhPos, rk1 := rk1, ck1_0 := ck1_0 } :: L)

structure AuthRespRecord where
  bKey  : Nat × Nat
  ikAPk : Bytes
  ekAPk : Bytes

/-- Simulator state for the `Auth` Fiedler–Günther `GapDH` reduction in `GdhSimSpec`. -/
structure FgAuthSimState (S : Setup) where
  base       : AuthState S
  fgL        : List FgPatchEntry := []
  fgRootL    : List FgRootEntry := []
  rawRoCache : List (Bytes × DRKey) := []
  advRoLog   : List Bytes := []
  respRecs   : List AuthRespRecord := []
  advKeyPows : List (Bytes × Bytes) := []

def FgAuthSimState.empty (S : Setup) (secb : Bool) : FgAuthSimState S :=
  { base := AuthState.empty S secb }

def fgRoQueryAuthGdh {S : Setup} (maxLen : ℕ) (secrets : Bytes)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  let advRoLog' := secrets :: st.advRoLog
  match parseRoSecrets secrets with
  | some (dh1, dh2, dh3, dh4?, ss) =>
    let pos1 ← mkSecretPos dh1
    let pos2 ← mkSecretPos dh2
    let pos3 ← mkSecretPos dh3
    let pos4? ← match dh4? with
      | none => pure none
      | some dh4 => some <$> mkSecretPos dh4
    let (dk, fgL') ← fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL
    return (.drKeyResp dk, { st with fgL := fgL', advRoLog := advRoLog' })
  | none =>
    match st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some (_, dk) =>
      return (.drKeyResp dk, { st with advRoLog := advRoLog' })
    | none =>
      let dk ← unifGdh sampleDRKey96
      return (.drKeyResp dk,
        { st with rawRoCache := (secrets, dk) :: st.rawRoCache, advRoLog := advRoLog' })

def fgRoRootQueryAuthGdh {S : Setup} (maxLen : ℕ) (rk dh : Bytes)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  let pos ← mkSecretPos dh
  let ((rk1, ck1_0), fgRootL') ← fgRootPatch maxLen rk pos st.fgRootL
  return (.rootKdfResp rk1 ck1_0, { st with fgRootL := fgRootL' })

def fgRunSendAuthGdh (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  if m0.length != m1.length then return (.noneResp, st)
  if st.base.usedSendSessions.contains sid then return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let peerPrincipal? ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (FgGapDh.findHonestPrincipalPrim S st.base.principals bundle.ikB)
  let isFreshPeer : Bool := match peerPrincipal? with
    | some (_, pEntry) => !PrincipalEntry.corrupted pEntry
    | none             => false
  if !isFreshPeer && m0 != m1 then return (.noneResp, st)
  let koskOk ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (FgGapDh.koskBundleOkPrim S st.base.principals st.base.spkBundles st.base.opkEntries
      st.advKeyPows bundle)
  if !koskOk then return (.noneResp, st)
  let isTargetEph : Bool := !useDh1 && (initSessionSlotIdx sid == targetIdx)
  let ekASkRaw ← unifGdh sampleScalar32
  let kemCoins ← unifGdh sampleCoins32
  let ephASk ← unifGdh sampleScalar32
  let spqrCoins ← unifGdh sampleCoins32
  let sigPkB ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (FgGapDh.resolveSigPkPrim S st.base.principals bundle.ikB)
  let v1 ← primGdhQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primGdhQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  if !(v1 && v2) then return (.noneResp, st)
  let some (ss, kemCt) ← primGdhQ (.kemEncaps bundle.pqspkB kemCoins)
    | return (.noneResp, st)
  let ekAPkRaw ← primGdhQ (.x25519Base ekASkRaw)
  let ekASk := if isTargetEph then [] else ekASkRaw
  let ekAPk := if isTargetEph then U else ekAPkRaw
  let spkSk ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (lookupSpkSkPrim S st.base.spkBundles st.advKeyPows bundle.spkB)
  let pos1 ← computeTwoSideOrPairPos uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 ← computeTwoSideOrPairPos ekASk [] ekAPk bundle.ikB
  let pos3 ← computeTwoSideOrPairPos ekASk [] ekAPk bundle.spkB
  let pos4? ← computeOptPos ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKey, fgL') ← fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let ephAPk ← primGdhQ (.x25519Base ephASk)
  let dhRatchet ← primGdhQ (.x25519 ephASk bundle.spkB)
  let posRatchet ← mkSecretPos dhRatchet
  let ((rk1, ck1_0), fgRootL') ← fgRootPatch maxLen drKey.rootKey posRatchet st.fgRootL
  let mkSeed ← primGdhQ (.chainKdfSeed ck1_0)
  let ck1_1 ← primGdhQ (.chainKdfNext ck1_0)
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) ← primGdhQ (.spqrInitSend drKey.pqrKey spqrCoins)
    | return (.noneResp, st)
  let deriveMessageKeys ← primGdhQ (.deriveMsgKeys mkSeed spqrSalt?)
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let msgPlain := if isFreshPeer then (if st.base.secb then m1 else m0) else m0
  let aeadCt ← primGdhQ (.aeadEnc deriveMessageKeys ad msgPlain)
  let hdr : HandshakeHdr := {
    ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId
    opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let wireMsg : PreKeyMsg := {
    hdr := hdr, ephAPk := ephAPk, pqRatchetMsg := pqRatchetMsg, aeadCt := aeadCt }
  let (spkHon, opkHon, pqspkHon) :=
    match peerPrincipal? with
    | none => (false, false, false)
    | some (k, _) =>
      (st.base.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
       false,
       st.base.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
  let sessEntry : AuthInitiatorEntry S := {
    sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB
    peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB
    spkHonest := spkHon, opkHonest := opkHon, pqspkHonest := pqspkHon
    ekASk := ekASk, ephASk := ephASk, fresh := isFreshPeer
    challenged := isFreshPeer && (m0 != m1) }
  let base' : AuthState S := { st.base with
    sessions := sessEntry :: st.base.sessions
    usedSendSessions := sid :: st.base.usedSendSessions }
  let st' : FgAuthSimState S := { st with base := base', fgL := fgL', fgRootL := fgRootL' }
  if peerPrincipal?.isSome then
    return (.sendFreshResp wireMsg, st')
  else
    return (.sendUnfreshResp drKey rk1 ck1_1 wireMsg, st')

def fgFinishRecvStep2AuthGdh (S : Setup) (_k : Fin S.N_id) (_j : Fin S.N_recv)
    (msg : PreKeyMsg) (kEntry : PrincipalEntry)
    (drKey : DRKey) (fgL' : List FgPatchEntry)
    (rk1 : Bytes) (ck1_1 : Bytes) (fgRootL' : List FgRootEntry)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes)
    (updBase : AuthState S → AuthState S)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  let deriveMessageKeys ← primGdhQ (.deriveMsgKeys mkSeed spqrSalt?)
  let pt? ← primGdhQ (.aeadDec deriveMessageKeys
    (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt)
  match pt? with
  | none => pure (.noneResp, st)
  | some pt =>
    let senderPrincipal? ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
      (FgGapDh.findHonestPrincipalPrim S st.base.principals msg.hdr.ikAPk)
    let st' : FgAuthSimState S := { st with
      base := updBase st.base, fgL := fgL', fgRootL := fgRootL' }
    match senderPrincipal? with
    | some _ => pure (.recvHonestResp, st')
    | none   => pure (.recvUnfreshResp drKey rk1 ck1_1 pt, st')

def fgFinishRecvAuthGdh (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv)
    (msg : PreKeyMsg) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (ss : Bytes) (pos4? : Option FgPoS)
    (updBase : AuthState S → AuthState S)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  let pos1 ← computeTwoSideOrPairPos [] bEntry.spkSk msg.hdr.ikAPk bEntry.spkPk
  let pos2 ← computeTwoSideOrPairPos [] kEntry.secIKA0 msg.hdr.ekAPk kEntry.ikAPk
  let pos3 ← computeTwoSideOrPairPos [] bEntry.spkSk msg.hdr.ekAPk bEntry.spkPk
  let dkL ← fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let posRatchet ← computeTwoSideOrPairPos [] bEntry.spkSk msg.ephAPk bEntry.spkPk
  let rkOut ← fgRootPatch maxLen dkL.1.rootKey posRatchet st.fgRootL
  let mkSeed ← primGdhQ (.chainKdfSeed rkOut.1.2)
  let ck1_1 ← primGdhQ (.chainKdfNext rkOut.1.2)
  let spqr? ← primGdhQ (.spqrInitRecv dkL.1.pqrKey msg.pqRatchetMsg)
  match spqr? with
  | none => pure (.noneResp, st)
  | some spqr =>
    fgFinishRecvStep2AuthGdh S k j msg kEntry dkL.1 dkL.2 rkOut.1.1 ck1_1
      rkOut.2 mkSeed spqr.2 updBase st

def fgRunRecvOPKAuthGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then return (.noneResp, st)
  let senderOk ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (FgGapDh.koskSenderOkPrim S st.base.principals st.advKeyPows msg.hdr.ikAPk)
  if !senderOk then return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  let canon ← primGdhQ (.isCanonical msg.hdr.ekAPk)
  let canonEph ← primGdhQ (.isCanonical msg.ephAPk)
  if !replayOk || !canon || !canonEph then return (.noneResp, st)
  let some ss ← primGdhQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
    | return (.noneResp, st)
  let pos4 ← computeTwoSideOrPairPos [] oEntry.opkSk msg.hdr.ekAPk oEntry.opkPk
  let opks' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss (some pos4)
    (fun base => { base with
      opkEntries := opks', usedRecvOPK := (k.val, j.val, o.val) :: base.usedRecvOPK
      seenKyberBaseKeys := usedTriples' }) st

def fgRunRecvNoOPKAuthGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) then return (.noneResp, st)
  let senderOk ← FgGapDh.embedPrim (spec := gapDhOracleSpec)
    (FgGapDh.koskSenderOkPrim S st.base.principals st.advKeyPows msg.hdr.ikAPk)
  if !senderOk then return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  let canon ← primGdhQ (.isCanonical msg.hdr.ekAPk)
  let canonEph ← primGdhQ (.isCanonical msg.ephAPk)
  if !replayOk || !canon || !canonEph then return (.noneResp, st)
  let some ss ← primGdhQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
    | return (.noneResp, st)
  fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss none
    (fun base => { base with
      usedRecvNoOPK := (k.val, j.val, l.val) :: base.usedRecvNoOPK
      seenKyberBaseKeys := usedTriples' }) st

def fgAuthStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : AuthQuery S) (st : FgAuthSimState S) :
    OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) := do
  match q with
  | .initPrin u =>
    if st.base.principals.any (fun (idx, _) => idx == u.val) then return (.noneResp, st)
    let isTargetPrin : Bool := useDh1 && (u.val == targetIdx)
    let secIKA0Raw ← unifGdh sampleScalar32
    let ikAPkRaw ← primGdhQ (.x25519Base secIKA0Raw)
    let secIKAsign ← unifGdh sampleScalar32
    let ikSignPk ← primGdhQ (.sigPkGen secIKAsign)
    let entry : PrincipalEntry := {
      secIKA0    := if isTargetPrin then [] else secIKA0Raw
      ikAPk      := if isTargetPrin then U else ikAPkRaw
      secIKAsign := secIKAsign
      ikSignPk   := ikSignPk
      corrupted  := false }
    let base' := { st.base with principals := (u.val, entry) :: st.base.principals }
    return (.initPrinResp entry.ikAPk entry.ikSignPk, { st with base := base' })
  | .corruptIK u =>
    match st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, st)
    | some (_, entry) =>
      let principals' := st.base.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st.base with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign, { st with base := base' })
  | .genSPK u j =>
    if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, st)
    let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    let isTargetSpk : Bool := FgGapDh.spkBundleFlatIdx S u j == targetSpkIdx
    let spkSkRaw ← unifGdh sampleScalar32
    let spkPkRaw ← primGdhQ (.x25519Base spkSkRaw)
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← unifGdh sampleRandom64
    let spkSig ← primGdhQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
    let seedKem ← unifGdh sampleRandom64
    let (pqspkPk, pqspkSk) ← primGdhQ (.kemKeyGen seedKem)
    let rPq ← unifGdh sampleRandom64
    let pqspkSig ← primGdhQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq)
    let bEntry : SpkBundleEntry := {
      spkSk := spkSk, spkPk := spkPk, spkSig := spkSig
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    return (.bundleResp bundleOut, { st with base := base' })
  | .genOPK u j o =>
    if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then return (.noneResp, st)
    let opkSk ← unifGdh sampleScalar32
    let opkPk ← primGdhQ (.x25519Base opkSk)
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    let base' := { st.base with
      opkEntries := ((u.val, j.val, o.val), oEntry) :: st.base.opkEntries }
    return (.pkResp opkPk, { st with base := base' })
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return (.noneResp, st)
    fgRunSendAuthGdh useDh1 targetIdx S maxLen U (.sendOPK u i) u bundle m0 m1 st
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return (.noneResp, st)
    fgRunSendAuthGdh useDh1 targetIdx S maxLen U (.sendNoOPK u i) u bundle m0 m1 st
  | .recvOPK k j o msg =>
    let rRec : AuthRespRecord :=
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk }
    fgRunRecvOPKAuthGdh S maxLen k j o msg { st with respRecs := rRec :: st.respRecs }
  | .recvNoOPK k j l msg =>
    let rRec : AuthRespRecord :=
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk }
    fgRunRecvNoOPKAuthGdh S maxLen k j l msg { st with respRecs := rRec :: st.respRecs }
  | .roQuery secrets => fgRoQueryAuthGdh maxLen secrets st
  | .roRootQuery rk dh => fgRoRootQueryAuthGdh maxLen rk dh st
  | .revealDhSecrets => return (.noneResp, st)
  | .registerKey sk =>
    if sk.length != 32 then return (.noneResp, st)
    let pk ← primGdhQ (.x25519Base sk)
    let powPk ← primGdhQ (.pow8 pk)
    let base' := { st.base with advKeys := (powPk, pk) :: st.base.advKeys }
    return (.pkResp pk, { st with base := base', advKeyPows := (sk, powPk) :: st.advKeyPows })

def isTargetPrinCorrupted {S : Setup} (targetIdx : ℕ) (st : FgAuthSimState S) : Bool :=
  match st.base.principals.find? (fun (idx, _) => idx == targetIdx) with
  | some (_, e) => e.corrupted
  | none        => false

/-- Halting wrapper around `fgAuthStep` that freezes `st` once the target principal is corrupted. -/
def fgAuthStepHalt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuthSimState S) :
    OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S) :=
  if useDh1 && isTargetPrinCorrupted targetIdx st then
    return (.noneResp, st)
  else
    fgAuthStep useDh1 targetIdx targetSpkIdx S maxLen U V q st

def sessionSenderIdx {S : Setup} : SessionId S → Nat
  | .sendOPK u _     => u.val
  | .sendNoOPK u _   => u.val
  | .recvOPK k _ _   => k.val
  | .recvNoOPK k _ _ => k.val

def lookupSenderIkPk (principals : List (Nat × PrincipalEntry)) (uIdx : Nat) : Bytes :=
  match principals.find? (fun (idx, _) => idx == uIdx) with
  | some (_, e) => e.ikAPk
  | none        => []

def lookupAuthSpkSkFromPows (spkPows advKeyPows : List (Bytes × Bytes)) (wSpk : Bytes) : Bytes :=
  match spkPows.find? (fun (sk, wB) => !sk.isEmpty && wB == wSpk) with
  | some (sk, _) => sk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => sk
    | none => []

def initAuthDh1CandWithPowsGdh {S : Setup}
    (principals : List (Nat × PrincipalEntry))
    (spkPows advKeyPows : List (Bytes × Bytes))
    (s : AuthInitiatorEntry S) : OracleComp GdhSimSpec Bytes := do
  let wSpk ← primGdhQ (.pow8 s.peerSpkPk)
  let spkSk := lookupAuthSpkSkFromPows spkPows advKeyPows wSpk
  let ikAPk := lookupSenderIkPk principals (sessionSenderIdx s.sid)
  primGdhQ (.x25519 spkSk ikAPk)

def respAuthCandGdh (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bKey : Nat × Nat) (pk : Bytes) : OracleComp GdhSimSpec Bytes :=
  let spkSk := match (spkBundles.take S.N_dh).find? (fun (idx, _) => idx == bKey) with
    | some (_, b) => b.spkSk
    | none => []
  primGdhQ (.x25519 spkSk pk)

abbrev respAuthDh1CandGdh (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : AuthRespRecord) : OracleComp GdhSimSpec Bytes :=
  respAuthCandGdh S spkBundles r.bKey r.ikAPk
abbrev respAuthDh3CandGdh (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : AuthRespRecord) : OracleComp GdhSimSpec Bytes :=
  respAuthCandGdh S spkBundles r.bKey r.ekAPk

def initAuthDh3CandGdh {S : Setup} (s' : AuthInitiatorEntry S) : OracleComp GdhSimSpec Bytes :=
  if s'.ekASk.isEmpty then pure (List.replicate 32 0)
  else primGdhQ (.x25519 s'.ekASk s'.peerSpkPk)

def extractCdhFromAuthSimState (S : Setup) (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes)
    (st : FgAuthSimState S) : OracleComp GdhSimSpec Bytes :=
  if useDh1 then do
    match ← findMGdh (fun z => ddhGdhQ U V z) ((st.advRoLog.take maxLen).map FgGapDh.extractDh1)
      with
    | some z => return z
    | none =>
      let spkPows ← spkPowsGdh (st.base.spkBundles.take S.N_dh)
      match ← findMapMGdh (initAuthDh1CandWithPowsGdh st.base.principals spkPows st.advKeyPows) U V
          (st.base.sessions.take S.N_dh) with
      | some z => return z
      | none =>
        match ← findMapMGdh (respAuthDh1CandGdh S st.base.spkBundles) U V
            (st.respRecs.take S.N_sess_tot) with
        | some z => return z
        | none   => return List.replicate 32 0
  else do
    match ← findMGdh (fun z => ddhGdhQ U V z) ((st.advRoLog.take maxLen).map FgGapDh.extractDh3)
      with
    | some z => return z
    | none =>
      match ← findMapMGdh initAuthDh3CandGdh U V (st.base.sessions.take S.N_dh) with
      | some z => return z
      | none =>
        match ← findMapMGdh (respAuthDh3CandGdh S st.base.spkBundles) U V
            (st.respRecs.take S.N_sess_tot) with
        | some z => return z
        | none   => return List.replicate 32 0

def fgAuthGapDhRunAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (U V : Bytes) : OracleComp GdhSimSpec Bytes := do
  let secb ← unifGdh ($ᵗ Bool)
  let initSt := FgAuthSimState.empty S secb
  let (_, finalSt) ← runWithGdhStep
    (fgAuthStepHalt useDh1 targetIdx targetSpkIdx S b.q_total U V) A.1.run initSt
  extractCdhFromAuthSimState S useDh1 b.q_total U V finalSt

def fgAuthGapDhAdvAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) : GapDhAdv where
  run U V := fgAuthGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V
  q_ddh := 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_prim := b.q_total * (S.N_dh * 18 + 26) + (S.N_dh * 3 + S.N_sess_tot)

/-- Combined two-case (`DH1` and `DH3`) Fiedler–Günther `GapDH` reduction for `Auth`. -/
def fgAuthGapDhAdv4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapDhAdv where
  run U V := do
    let (flatIdx, bIdx) ← unifGdh (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)
    if flatIdx < S.N_id then
      fgAuthGapDhRunAt true flatIdx bIdx S b A U V
    else
      fgAuthGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V
  q_ddh := 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_prim := b.q_total * (S.N_dh * 18 + 26) + (S.N_dh * 3 + S.N_sess_tot)

end SignalPqxdh.Security
