/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHmac
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake

/-!
# One-key shallow `Auth` reduction simulators

**Checked by Lean.** Defines the one-key `Auth` black-box reduction simulators for `PrfChainKey`,
`PrfMsgKeys`, `AeadIndCpa`, `AeadMuIntCtxt`, `KemShCr`, and `PrfHmac`, adapting the two-key
simulators so `.initPrin` samples a single Curve25519 scalar shared by X25519 and XEdDSA.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open RoKem
open FgGapDh

/-! ## PRF reductions (`G3.6 → G3.8`) -/

namespace AuthSubHops1to3

def stepAuthOtherPrim1Key (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    return (.noneResp, hst)
  else
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, hst)
    else
      let secIKA0 ← embedUnif sampleScalar32
      let ikAPk ← primQ (.x25519Base secIKA0)
      let entry : PrincipalEntry := {
        secIKA0    := secIKA0
        ikAPk      := ikAPk
        secIKAsign := secIKA0
        ikSignPk   := ikAPk
        corrupted  := false
      }
      let base' := { st with principals := (u.val, entry) :: st.principals }
      return (.initPrinResp ikAPk ikAPk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, hst)
    else
      match st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => return (.noneResp, hst)
      | some (_, uEntry) =>
        let spkSk ← embedUnif sampleScalar32
        let spkPk ← primQ (.x25519Base spkSk)
        let rSpk ← embedUnif sampleRandom64
        let spkSig ← primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
        let (pqspkPk, pqspkSk) ← sampleKemKeyGenPrim
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
        let base' := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
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
          { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, hst)
    else
      let opkSk ← embedUnif sampleScalar32
      let opkPk ← primQ (.x25519Base opkSk)
      let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
      let base' := { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
      return (.pkResp opkPk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, hst)
    else
      let pk ← primQ (.x25519Base sk)
      let p8 ← primQ (.pow8 pk)
      let base' := { st with advKeys := (p8, pk) :: st.advKeys }
      return (.pkResp pk,
        { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .roQuery secrets =>
    let (dk, roCache') ← embedUnif (evalHkdfRoPure st.roCache secrets)
    let base' := { st with roCache := roCache' }
    return (.drKeyResp dk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .roRootQuery rk dh =>
    let (out, rootRoCache') ← embedUnif (evalRootKdfRoPure st.rootRoCache rk dh)
    let base' := { st with rootRoCache := rootRoCache' }
    return (.rootKdfResp out.1 out.2,
      { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })
  | .revealDhSecrets =>
    return (.noneResp, hst)
  | .sendOPK _ _ _ _ _ =>
    return (.noneResp, hst)
  | .sendNoOPK _ _ _ _ _ =>
    return (.noneResp, hst)
  | .recvOPK _ _ _ _ =>
    return (.noneResp, hst)
  | .recvNoOPK _ _ _ _ =>
    return (.noneResp, hst)

def authCkStepWithPrim1Key (S : Setup) (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendWithPrim S sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendWithPrim S sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg => do
    let prep? ← prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState
    authCkRecvWithPrim S sampAt msg prep? hst
  | .recvNoOPK k j l msg => do
    let prep? ← prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState
    authCkRecvWithPrim S sampAt msg prep? hst
  | qOther =>
    stepAuthOtherPrim1Key S qOther hst

def authCkPreSampleRunPrim1Key (S : Setup) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : OracleComp PrimBaseSpec Bool := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt := AuthHybridStateFixed.empty S secb
  let (b', finalSt) ←
    runWithPrimStep (authCkStepWithPrim1Key S (sampAtCkPrim idx p)) A.run initSt
  finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState

/-- Black-box `PrfChainKey` reduction for one-key `Auth` (`G3.6 → G3.7`). -/
def prfCkReductionAuthFixed1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfCkAdv where
  dist mkSeedChal ck1_1Chal := do
    let idx ← embedUnif (RoKem.sampleIndexRange (min b.q_total S.N_sess_tot))
    authCkPreSampleRunPrim1Key S idx (mkSeedChal, ck1_1Chal) A.1
  q_prf := 1
  q_prim := b.q_total * (S.N_dh * 26 + 21) + S.N_dh * 5

def authMkStepReduction1Key (S : Setup) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure ((.noneResp, hst), sentChal)
    else authMkSendReduction S idx (.sendOPK u i) u bundle m0 m1 hst sentChal
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure ((.noneResp, hst), sentChal)
    else authMkSendReduction S idx (.sendNoOPK u i) u bundle m0 m1 hst sentChal
  | .recvOPK k j o msg => do
    let prep? ← embedPrimMk (prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState)
    let res ← authMkRecvReduction S idx msg prep? hst sentChal
    return (res, sentChal)
  | .recvNoOPK k j l msg => do
    let prep? ← embedPrimMk (prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState)
    let res ← authMkRecvReduction S idx msg prep? hst sentChal
    return (res, sentChal)
  | qOther => do
    let res ← embedPrimMk (stepAuthOtherPrim1Key S qOther hst)
    return (res, sentChal)

def authMkReductionRun1Key (S : Setup) (idx : Nat) (A : AuthAdversary S) :
    OracleComp PrfMkSimSpec Bool := do
  let secb ← embedUnifMk ($ᵗ Bool)
  let initSt := AuthHybridStateFixed.empty S secb
  let ((b', finalSt), _sentChal) ←
    runWithPrfMkStep (authMkStepReduction1Key S idx) A.run initSt false
  embedPrimMk (finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState)

/-- Black-box `PrfMsgKeys` reduction for one-key `Auth` (`G3.7 → G3.8`). -/
def prfMsgKeysReductionAuthFixed1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfMsgKeysAdv where
  run := do
    let idx ← embedUnifMk (RoKem.sampleIndexRange (min b.q_total S.N_sess_tot))
    authMkReductionRun1Key S idx A.1
  q_prf := S.N_recv_tot + 1
  q_prim := b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5

end AuthSubHops1to3

/-! ## AEAD reductions (`G3.8 → G5`) -/

def stepAuthOtherPrim1Key (useRo : Bool) (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, hst)
    let secIKA0 ← embedUnif sampleScalar32
    let ikAPk ← primQ (.x25519Base secIKA0)
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKA0
      ikSignPk   := ikAPk
      corrupted  := false
    }
    return (.initPrinResp ikAPk ikAPk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with principals := (u.val, entry) :: st.principals } } })
  | .corruptIK u =>
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, entry) =>
      let principals' := st.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      return (.corrResp entry.secIKA0 entry.secIKAsign,
        { hst with toAuthHybridState := { hst.toAuthHybridState with
            base := { st with principals := principals' } } })
  | .genSPK u j =>
    if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, hst)
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, hst)
    | some (_, uEntry) =>
      let spkSk ← embedUnif sampleScalar32
      let spkPk ← primQ (.x25519Base spkSk)
      let rSpk ← embedUnif sampleRandom64
      let spkSig ← primQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
      let (pqspkPk, pqspkSk) ← sampleKemKeyGenPrim
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
        { hst with toAuthHybridState := { hst.toAuthHybridState with
            base := { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles } } })
  | .genOPK u j o =>
    if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, hst)
    let opkSk ← embedUnif sampleScalar32
    let opkPk ← primQ (.x25519Base opkSk)
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    return (.pkResp opkPk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries } } })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, hst)
    let pk ← primQ (.x25519Base sk)
    let p8 ← primQ (.pow8 pk)
    return (.pkResp pk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with advKeys := (p8, pk) :: st.advKeys } } })
  | .roQuery secrets =>
    if !useRo then
      return (.noneResp, hst)
    let (dk, roCache') ← evalHkdfOrRoPrim true st.roCache secrets
    return (.drKeyResp dk,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with roCache := roCache' } } })
  | .roRootQuery rk dh =>
    if !useRo then
      return (.noneResp, hst)
    let (out, rootRoCache') ← embedUnif (evalRootKdfRoPure st.rootRoCache rk dh)
    return (.rootKdfResp out.1 out.2,
      { hst with toAuthHybridState := { hst.toAuthHybridState with
          base := { st with rootRoCache := rootRoCache' } } })
  | .revealDhSecrets =>
    if useRo then
      return (.noneResp, hst)
    let ikDhSks := st.principals.map (fun (_, e) => e.secIKA0)
    let spkSks  := st.spkBundles.map (fun (_, b) => b.spkSk)
    let opkSks  := st.opkEntries.map (fun (_, o) => o.opkSk)
    let ekSks   := (st.sessions.map (fun s => s.ekASk)) ++ (st.sessions.map (fun s => s.ephASk))
    return (.dhSecretsResp ikDhSks spkSks opkSks ekSks, hst)
  | .sendOPK _ _ _ _ _ | .sendNoOPK _ _ _ _ _ | .recvOPK _ _ _ _ | .recvNoOPK _ _ _ _ =>
    return (.noneResp, hst)

def stepAuthCpaNonSendPrim1Key (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  let st := hst.toAuthHybridState.base
  match q with
  | .sendOPK _ _ _ _ _ => return (.noneResp, hst)
  | .sendNoOPK _ _ _ _ _ => return (.noneResp, hst)
  | .recvOPK k j o msg => do
    let recvCount' := hst.recvCount + 1
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return (.noneResp, { hst with recvCount := recvCount' })
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then
      return (.noneResp, { hst with recvCount := recvCount' })
    let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !senderOk then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    if oEntry.consumed then
      return (.noneResp, { hst with recvCount := recvCount' })
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    let isCanEk ← primQ (.isCanonical msg.hdr.ekAPk)
    let isCanEph ← primQ (.isCanonical msg.ephAPk)
    if !replayOk || !isCanEk || !isCanEph then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some ss ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec : AuthHybridStateFixed S :=
      { toAuthHybridState :=
          { hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
        recvCount := hst.recvCount
        mkSaltCache := hst.mkSaltCache }
    let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
    let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
    let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
    let dh4 ← primQ (.x25519 oEntry.opkSk msg.hdr.ekAPk)
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry (some oEntry.opkPk) secrets msg
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
      | return (.noneResp, { hstDec with recvCount := recvCount', mkSaltCache := mkSaltCache' })
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
    let resp : AuthResponse :=
      match senderPrincipal? with
      | some _ => .recvHonestResp
      | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
    return (resp,
      { toAuthHybridState := { hstDec.toAuthHybridState with
          base := { st with
            opkEntries       := opkEntries'
            usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        recvCount := recvCount'
        mkSaltCache := mkSaltCache' })
  | .recvNoOPK k j l msg => do
    let recvCount' := hst.recvCount + 1
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return (.noneResp, { hst with recvCount := recvCount' })
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
      return (.noneResp, { hst with recvCount := recvCount' })
    let senderOk ← koskSenderOkPrim S st.principals st.advKeys msg.hdr.ikAPk
    if !senderOk then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return (.noneResp, { hst with recvCount := recvCount' })
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    let isCanEk ← primQ (.isCanonical msg.hdr.ekAPk)
    let isCanEph ← primQ (.isCanonical msg.ephAPk)
    if !replayOk || !isCanEk || !isCanEph then
      return (.noneResp, { hst with recvCount := recvCount' })
    let some ss ← primQ (.kemDecaps bEntry.pqspkSk msg.hdr.kemCt)
      | return (.noneResp, { hst with recvCount := recvCount' })
    let rRec : RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
    }
    let hstDec : AuthHybridStateFixed S :=
      { toAuthHybridState :=
          { hst.toAuthHybridState with recvKemRecs := rRec :: hst.toAuthHybridState.recvKemRecs }
        recvCount := hst.recvCount
        mkSaltCache := hst.mkSaltCache }
    let dh1 ← primQ (.x25519 bEntry.spkSk msg.hdr.ikAPk)
    let dh2 ← primQ (.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
    let dh3 ← primQ (.x25519 bEntry.spkSk msg.hdr.ekAPk)
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry none secrets msg
    let some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') := res?
      | return (.noneResp, { hstDec with recvCount := recvCount', mkSaltCache := mkSaltCache' })
    let senderPrincipal? ← findHonestPrincipalPrim S st.principals msg.hdr.ikAPk
    let resp : AuthResponse :=
      match senderPrincipal? with
      | some _ => .recvHonestResp
      | none   => .recvUnfreshResp drKey rk1 ck1_1 pt
    return (resp,
      { toAuthHybridState := { hstDec.toAuthHybridState with
          base := { st with
            usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
            seenKyberBaseKeys := usedTriples'
            roCache          := roCache'
            rootRoCache      := rootRoCache' } }
        recvCount := recvCount'
        mkSaltCache := mkSaltCache' })
  | q_other =>
    stepAuthOtherPrim1Key true S q_other hst

def stepAuthCpaCutoffPrim1Key (cut : Nat) (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then
      return (.noneResp, hst)
    else
      runAuthSendCpaCutoffPrim cut S (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then
      return (.noneResp, hst)
    else
      runAuthSendCpaCutoffPrim cut S (.sendNoOPK u i) u bundle m0 m1 hst
  | q_other =>
    stepAuthCpaNonSendPrim1Key S q_other hst

def stepUntilAuthCpaChallengeFixedPrim1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α)
    (mx : OracleComp (unifSpec + authSpec S) α) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec (AuthCpaPauseResult S α) :=
  OracleComp.construct
    (C := fun _ => Nat → AuthHybridStateFixed S → OracleComp PrimBaseSpec (AuthCpaPauseResult S α))
    (fun a _ s => pure (.done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (.done defaultVal s)
        | f' + 1 =>
          match gq with
          | .sendOPK u i bundle m0 m1 =>
            if bundle.opkB?.isNone then
              r .noneResp f' s
            else do
              let stepRes ← tryPauseAuthCpaSendFixedPrim true idx S (.sendOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | .sendNoOPK u i bundle m0 m1 =>
            if bundle.opkB?.isSome then
              r .noneResp f' s
            else do
              let stepRes ←
                tryPauseAuthCpaSendFixedPrim true idx S (.sendNoOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | qOther => do
            let (resp, s') ← stepAuthCpaNonSendPrim1Key S qOther s
            r resp f' s')
    mx fuel hst

def resumeAuthCpaAfterChallengeFixedPrim1Key (idx : Nat) (S : Setup) (fuel : Nat) :
    AuthCpaPauseResult S Bool → Option Bytes → OracleComp PrimBaseSpec Bool
  | .done b' hst, _ =>
    finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState
  | .paused _ _ _ p hst cont, chalCt? => do
    let aeadCt := chalCt?.getD []
    let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
    let (b', finalSt) ←
      runWithPrimStepFuel false (stepAuthCpaCutoffPrim1Key idx S) (cont resp) fuel hst'
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

def aeadCpaReductionAuthFixedAtChoose1Key (idx : Nat) (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × AuthCpaPauseResult S Bool) := do
  let initSt := AuthHybridStateFixed.empty S true
  let res ← stepUntilAuthCpaChallengeFixedPrim1Key idx S false A.run fuel initSt
  match res with
  | .paused ad m0 m1 _ _ _ =>
    if m0.length == m1.length then
      return (ad, m0, m1, res)
    else
      return ([], [0], [0], res)
  | .done _ _ =>
    return ([], [0], [0], res)

def aeadCpaReductionAuthFixedChoose1Key (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × (Nat × AuthCpaPauseResult S Bool)) := do
  let idx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
  let (ad, m0, m1, res) ← aeadCpaReductionAuthFixedAtChoose1Key idx S fuel A
  return (ad, m0, m1, (idx, res))

def aeadCpaReductionAuthFixedDist1Key (S : Setup) (fuel : Nat)
    (st : Nat × AuthCpaPauseResult S Bool) (chalCt? : Option Bytes) :
    OracleComp PrimBaseSpec Bool :=
  resumeAuthCpaAfterChallengeFixedPrim1Key st.1 S fuel st.2 chalCt?

def stepAuthCpaCutoffSlotPrim1Key (cut : Nat) (S : Setup)
    (q : AuthQuery S) (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthCpaSlotState S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then
      return (.noneResp, shst)
    else
      runAuthSendCpaCutoffSlotPrim cut S (.sendOPK u i) u bundle m0 m1 shst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then
      return (.noneResp, shst)
    else
      runAuthSendCpaCutoffSlotPrim cut S (.sendNoOPK u i) u bundle m0 m1 shst
  | q_other => do
    let (resp, hst') ← stepAuthCpaNonSendPrim1Key S q_other shst.2
    return (resp, (shst.1, hst'))

def stepUntilAuthCpaChallengeSlotPrim1Key (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α)
    (mx : OracleComp (unifSpec + authSpec S) α) (fuel : Nat) (shst : AuthCpaSlotState S) :
    OracleComp PrimBaseSpec (AuthCpaSlotPauseResult S α) :=
  OracleComp.construct
    (C := fun _ => Nat → AuthCpaSlotState S → OracleComp PrimBaseSpec (AuthCpaSlotPauseResult S α))
    (fun a _ s => pure (.done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (.done defaultVal s)
        | f' + 1 =>
          match gq with
          | .sendOPK u i bundle m0 m1 =>
            if bundle.opkB?.isNone then
              r .noneResp f' s
            else do
              let stepRes ← tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | .sendNoOPK u i bundle m0 m1 =>
            if bundle.opkB?.isSome then
              r .noneResp f' s
            else do
              let stepRes ←
                tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | qOther => do
            let (resp, hst') ← stepAuthCpaNonSendPrim1Key S qOther s.2
            r resp f' (s.1, hst'))
    mx fuel shst

def resumeAuthCpaAfterChallengeSlotPrim1Key (idx : Nat) (S : Setup) (fuel : Nat) :
    AuthCpaSlotPauseResult S Bool → Option Bytes → OracleComp PrimBaseSpec Bool
  | .done b' (_, hst), _ =>
    finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState
  | .paused _ _ _ p (_, hst) cont, chalCt? => do
    let aeadCt := chalCt?.getD []
    let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
    let (b', (_, finalSt)) ←
      runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim1Key idx S) (cont resp) fuel (idx + 1, hst')
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

def aeadCpaReductionAuthSlotAtChoose1Key (idx : Nat) (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × AuthCpaSlotPauseResult S Bool) := do
  let initSt : AuthCpaSlotState S := (0, AuthHybridStateFixed.empty S true)
  let res ← stepUntilAuthCpaChallengeSlotPrim1Key idx S false A.run fuel initSt
  match res with
  | .paused ad m0 m1 _ _ _ =>
    if m0.length == m1.length then
      return (ad, m0, m1, res)
    else
      return ([], [0], [0], res)
  | .done _ _ =>
    return ([], [0], [0], res)

def aeadCpaReductionAuthSlotChoose1Key (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × (Nat × AuthCpaSlotPauseResult S Bool)) := do
  let idx ← embedUnif (RoKem.sampleIndexRange (min fuel S.N_send_tot))
  let (ad, m0, m1, res) ← aeadCpaReductionAuthSlotAtChoose1Key idx S fuel A
  return (ad, m0, m1, (idx, res))

def aeadCpaReductionAuthSlotDist1Key (S : Setup) (fuel : Nat)
    (st : Nat × AuthCpaSlotPauseResult S Bool) (chalCt? : Option Bytes) :
    OracleComp PrimBaseSpec Bool :=
  resumeAuthCpaAfterChallengeSlotPrim1Key st.1 S fuel st.2 chalCt?

/-- Black-box `AeadIndCpa` reduction for one-key `Auth` (`G3.8 → G5`). -/
def aeadCpaReductionAuthFixed1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : AeadIndCpaAdv where
  State  := Nat × AuthCpaSlotPauseResult S Bool
  choose := aeadCpaReductionAuthSlotChoose1Key S b.q_total A.1
  dist   := aeadCpaReductionAuthSlotDist1Key S b.q_total
  q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5

def stepAuthMuPrim1Key (S : Setup)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp AeadMuIntSimSpec (AuthResponse × AuthHybridStateFixed S) := do
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return (.noneResp, hst)
    else runAuthSendMuPrim S (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return (.noneResp, hst)
    else runAuthSendMuPrim S (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    let some prep ← embedPrimMu (prepareAuthRecvOPKPrim S k j o msg hst.toAuthHybridState)
      | return (.noneResp, { hst with recvCount := hst.recvCount + 1 })
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleMuPrim S prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    let (resp, hst') := prep.finish res?
    return (resp, {
      toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' })
  | .recvNoOPK k j l msg =>
    let some prep ← embedPrimMu (prepareAuthRecvNoOPKPrim S k j l msg hst.toAuthHybridState)
      | return (.noneResp, { hst with recvCount := hst.recvCount + 1 })
    let (res?, mkSaltCache') ←
      evalAuthRecvScheduleMuPrim S prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    let (resp, hst') := prep.finish res?
    return (resp, {
      toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := mkSaltCache' })
  | qOther => embedPrimMu (stepAuthOtherPrim1Key true S qOther hst)

def aeadMuIntReductionAuthRun1Key (S : Setup) (A : AuthAdversary S) :
    OracleComp AeadMuIntSimSpec Unit := do
  let secb ← unifMu ($ᵗ Bool)
  let _ ← runWithMuStep (stepAuthMuPrim1Key S) A.run (AuthHybridStateFixed.empty S secb)
  return ()

/-- Black-box multi-key `AeadMuIntCtxt` reduction for one-key `Auth` (`G3.8 → G5`). -/
def aeadMuIntReductionAuth1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : AeadMuIntCtxtAdv where
  run    := aeadMuIntReductionAuthRun1Key S A.1
  q_enc  := S.N_send_tot
  q_dec  := S.N_recv_tot
  q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5

/-! ## `KemShCr` reduction (`G2 → G3`) -/

def pqxdhAuthSimImplPrim1Key (S : Setup) :
    QueryImpl (authSpec S) (StateT (AuthState S) (OracleComp PrimBaseSpec)) := fun q =>
  match q with
  | .initPrin u => do
    let st ← get
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM (embedUnif sampleScalar32)
    let ikAPk ← liftM (primQ (.x25519Base secIKA0))
    let entry : PrincipalEntry := {
      secIKA0    := secIKA0
      ikAPk      := ikAPk
      secIKAsign := secIKA0
      ikSignPk   := ikAPk
      corrupted  := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikAPk
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

def runAuthShCrAcceptPrim1Key (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (gq : AuthQuery S) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := do
  let out ← liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S gq)
  recordAcceptKemGenericPrim AuthState.spkBundles isNoneAuthShCrResp k j hdr out

def runAuthShCrGenSPKPrim1Key (embedTarget : Bool) (S : Setup)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (AuthShCrState S) (OracleComp PrimBaseSpec) AuthResponse := fun hst =>
  if !embedTarget then
    (liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S (.genSPK u j))).run hst
  else
    match hst.targetBIdx? with
    | none => (liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S (.genSPK u j))).run hst
    | some bIdx =>
      if RoKem.spkBundleFlatIdx S u j == bIdx then
        (genSpkTargetAuthPrim S u j).run hst
      else
        (liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S (.genSPK u j))).run hst

def pqxdhAuthShCrPrimImpl1Key (embedTarget : Bool) (S : Setup) :
    QueryImpl (authSpec S) (StateT (AuthShCrState S) (OracleComp PrimBaseSpec))
  | .genSPK u j => runAuthShCrGenSPKPrim1Key embedTarget S u j
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure .noneResp
    else runAuthShCrSendPrim S (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure .noneResp
    else runAuthShCrSendPrim S (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg =>
    runAuthShCrAcceptPrim1Key S k j msg.hdr (.recvOPK k j o msg)
  | .recvNoOPK k j l msg =>
    runAuthShCrAcceptPrim1Key S k j msg.hdr (.recvNoOPK k j l msg)
  | q_other => liftShCrBasePrim (pqxdhAuthSimImplPrim1Key S q_other)

def runWithFuelAuthShCrPrim1Key (S : Setup)
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
          let (out, hst') ← (pqxdhAuthShCrPrimImpl1Key true S gq).run hst
          r out hst' f)
    oa hst fuel

def stepUntilShCrFuelAuthPrim1Key (S : Setup) (sIdx : ℕ)
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
            let (out, hst') ← (pqxdhAuthShCrPrimImpl1Key true S gq).run hst
            r out hst' f)
    oa hst fuel

def resumePausedAuthPrim1Key (S : Setup) (fuel : ℕ) (d : PausedShCrAuthData S)
    (ss kemCt : Bytes) : OracleComp PrimBaseSpec (Bool × AuthShCrState S) := do
  let (resp, hst') ← postKemAuthPrim S d.sid d.bundle d.m0 d.m1 d.uInfo d.hst ss kemCt
  runWithFuelAuthShCrPrim1Key S (d.cont resp) hst' fuel

def choosePkAuthPrimAt1Key (S : Setup) (b : QueryBudget) (bIdx sIdx : ℕ)
    (A : AuthAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (Bytes × AuthShCrFinishState S) := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt : AuthShCrState S := {
    base        := AuthState.empty S secb
    targetBIdx? := some bIdx
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCrFuelAuthPrim1Key S sIdx A.run initSt b.q_total
  let chosenPk := match res with
    | Sum.inl _ => pk
    | Sum.inr d => d.bundle.pqspkB
  return (chosenPk, (pk, sk, chosenPk, res))

def findCollisionAuthPrim1Key (S : Setup) (b : QueryBudget)
    (st : AuthShCrFinishState S) (ss ct : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let (pk, sk, chosenPk, res) := st
  let (_, finalHst) ← match res with
    | Sum.inl done => pure done
    | Sum.inr d    => resumePausedAuthPrim1Key S b.q_total d ss ct
  extractCollidingKemCtPrim b.q_total pk sk chosenPk ct ss finalHst.recvKemRecs

def shcrReductionAuthCore1Key (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := AuthShCrFinishState S
  choosePk := fun pk sk => do
    let idx ← embedUnif (FgGapDh.sampleIndexRange (S.N_spk_tot * S.N_send_tot))
    choosePkAuthPrimAt1Key S b (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk
  findCollision := findCollisionAuthPrim1Key S b
  q_prim := primQueryBudget S b

/-- Black-box `KemShCr` reduction for one-key `Auth` (`G2 → G3`). -/
def shcrReductionAuth1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : KemShCrAdv :=
  shcrReductionAuthCore1Key S b A.val

/-! ## HMAC reduction (`G3.8 → G5`) -/

/-- Black-box `PrfHmac` reduction for one-key `Auth` (`G3.8 → G5`). -/
def prfHmacReductionAuth1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfHmacAdv :=
  prfHmacOfMu (aeadMuIntReductionAuth1Key S b A)

end SignalPqxdh.Security
