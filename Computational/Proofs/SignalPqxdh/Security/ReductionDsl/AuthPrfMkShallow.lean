/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval

/-!
# Shallow Pre/Post Decomposition of the `PrfMsgKeys` Step

Splits each `authMkStepReduction` game step into a `PrimBaseSpec` pre-step (`mkPre`), at most one
`.deriveMk` challenger query, and a `PrimBaseSpec` post-step (`MkCont.post`), matching the
structure of `prfMsgKeysRedProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl
open SignalPqxdh SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

/-! ## Continuations -/

/-- Continuation of a step that requested a `.deriveMk` challenge. -/
inductive MkCont (S : Setup) where
  /-- Ideal initiator send at the target slot. -/
  | send (hst : AuthHybridStateFixed S) (sid : SessionId S) (uEntry : PrincipalEntry)
      (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
      (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 ck1_1 : Bytes)
      (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
  /-- Ideal receiver at the target slot; `ci?` is the optional salt-cache key to record. -/
  | recv (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
      (recvCount' : Nat) (cache : AuthMkSaltCache S) (slots : AuthSlotState)
      (ci? : Option ((SessionId S × Option Bytes) × Nat))

def mkFreshPeer (peerPrincipal? : Option (Nat × PrincipalEntry)) : Bool :=
  match peerPrincipal? with
  | some (_, pEntry) => !pEntry.corrupted
  | none             => false

def MkCont.isSend {S : Setup} : MkCont S → Bool
  | .send .. => true
  | .recv .. => false

def MkCont.post {S : Setup} (c : MkCont S) (mk : MessageKeys) :
    OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S) :=
  match c with
  | .send hst sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1
      ck1_1 spqrSalt? pqRatchetMsg msgPlain =>
    finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk
      ephAPk drKey rk1 [] ck1_1 spqrSalt? pqRatchetMsg msgPlain hst mk
  | .recv msg prep drKey rk1 ck1_1 recvCount' cache slots ci? =>
    finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount'
      (match ci? with
       | none => cache
       | some (key, rc) => (key, (rc, mk)) :: cache) slots mk

def mkCacheToVal {S : Setup} (cache : AuthMkSaltCache S) : authMkSaltCacheTy.denote :=
  cache.map (fun ((sid, salt?), (rc, mk)) => ((sessionIdToVal sid, salt?), (rc, msgKeysToVal mk)))

def MkCont.toVal {S : Setup} (secb : Bool) (idx : Nat) (sc : Bool) :
    MkCont S → prfMkChalContTy.denote
  | .send hst sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1
      ck1_1 spqrSalt? pqRatchetMsg msgPlain =>
    .inl (secb, (idx, (authHybridStateFixedToVal hst, (sessionIdToVal sid,
      (principalEntryToVal uEntry, (peerPrincipal?.map (Prod.map id principalEntryToVal),
        (mkFreshPeer peerPrincipal?, (preKeyBundleToVal bundle, ((m0, m1),
          ((ekASk, (ekAPk, (ss, (kemCt, (ephASk, ephAPk))))),
            (drKeyToVal drKey, (rk1, (ck1_1, (spqrSalt?, (pqRatchetMsg, msgPlain)))))))))))))))
  | .recv msg prep drKey rk1 ck1_1 recvCount' cache slots ci? =>
    .inr (secb, (idx, (sc, (preKeyMsgToVal msg, (preparedAuthRecvToVal prep,
      (drKeyToVal drKey, (rk1, (ck1_1, (recvCount', (mkCacheToVal cache,
        (authSlotStateToVal slots,
          ci?.map (fun ((sid, salt?), rc) => ((sessionIdToVal sid, salt?), rc)))))))))))))

def mkCoreToVal {S : Setup} (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S) :
    prfMkCoreTy.denote :=
  (secb, (idx, (sc, authHybridStateFixedToVal hst)))

abbrev MkPre (S : Setup) := (AuthResponse × AuthHybridStateFixed S) ⊕ (Option Bytes × MkCont S)

def mkPreToVal {S : Setup} (secb : Bool) (idx : Nat) (sc : Bool) :
    MkPre S → prfMkStepPreTy.denote
  | .inl (r, hst') => .inl (authRespToVal r, mkCoreToVal secb idx sc hst')
  | .inr (salt?, c) => .inr (salt?, c.toVal secb idx sc)

/-! ## Pre-Steps -/

def mkSendPre (S : Setup) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) := do
  match ← prepareAuthSendMkPrim S sid u bundle m0 m1 hst with
  | .done resp hst' => return .inl (resp, hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    let (sIdx, slots') := hst.slots.allocSend sid
    let hst' := { hst with slots := slots' }
    if !sentChal && (sIdx == idx) then
      let ck1_1 ← embedUnif sampleBytes32
      return .inr (spqrSalt?, .send hst' sid uEntry peerPrincipal? bundle m0 m1 ekASk ekAPk ss kemCt
        ephASk ephAPk drKey rk1 ck1_1 spqrSalt? pqRatchetMsg msgPlain)
    else if decide (sIdx < idx) then
      let ck1_1 ← embedUnif sampleBytes32
      let deriveMessageKeys ← embedUnif sampleMessageKeys80
      let res ← finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys
      return .inl res
    else
      let mkSeed ← embedUnif sampleBytes32
      let ck1_1 ← embedUnif sampleBytes32
      let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
      let res ← finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst' deriveMessageKeys
      return .inl res

def mkUnmatchedSlotsPre (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat) (cache : AuthMkSaltCache S)
    (slots' : AuthSlotState) (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) := do
  if rSlot == idx then
    let ck1_1 ← embedUnif sampleBytes32
    if !sentChal then
      return .inr (spqrSalt?, .recv msg prep drKey rk1 ck1_1 recvCount' cache slots' none)
    else
      let deriveMessageKeys ← embedUnif sampleMessageKeys80
      let res ← finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' cache slots'
        deriveMessageKeys
      return .inl res
  else if decide (rSlot < idx) then
    let ck1_1 ← embedUnif sampleBytes32
    let deriveMessageKeys ← embedUnif sampleMessageKeys80
    let res ← finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' cache slots'
      deriveMessageKeys
    return .inl res
  else
    let mkSeed ← embedUnif sampleBytes32
    let ck1_1 ← embedUnif sampleBytes32
    let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
    let res ← finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' cache slots'
      deriveMessageKeys
    return .inl res

def mkUnmatchedPre (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat) (cache : AuthMkSaltCache S)
    (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) :=
  mkUnmatchedSlotsPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache {} sentChal

def mkMatchedSameEphSlotsPre (S : Setup) (idx : Nat) (msg : PreKeyMsg)
    (prep : PreparedAuthRecvPrim S) (s : IdealAuthSession S) (sIdx : Nat)
    (spqrSalt? : Option Bytes) (recvCount : Nat) (cache : AuthMkSaltCache S)
    (slots : AuthSlotState) : OracleComp PrimBaseSpec (MkPre S) := do
  if sIdx == idx then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache
        slots s.deriveMessageKeys
      return .inl res
    else
      match cache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) =>
        let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache
          slots mk
        return .inl res
      | none =>
        return .inr (spqrSalt?, .recv msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache slots
          (some ((s.sid, spqrSalt?), recvCount)))
  else if decide (sIdx < idx) then
    if sameSaltKey spqrSalt? s.spqrSalt? then
      let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache
        slots s.deriveMessageKeys
      return .inl res
    else
      match cache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
      | some (_, (_, mk)) =>
        let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache
          slots mk
        return .inl res
      | none =>
        let mk ← embedUnif sampleMessageKeys80
        let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1)
          (((s.sid, spqrSalt?), (recvCount, mk)) :: cache) slots mk
        return .inl res
  else
    let mk ← primQ (.deriveMsgKeys s.mkSeed spqrSalt?)
    let res ← finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1) cache
      slots mk
    return .inl res

def mkMatchedSameEphPre (S : Setup) (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (cache : AuthMkSaltCache S) : OracleComp PrimBaseSpec (MkPre S) :=
  mkMatchedSameEphSlotsPre S idx msg prep s (sessionSlotIndex s.sid) spqrSalt? recvCount cache {}

def mkRecvPre (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => return .inl (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match ← primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg) with
          | none =>
            let (resp, hst') ← prep.finishTag.runPrim S true none
            return .inl (resp, { toAuthHybridState := hst', recvCount := recvCount',
                                 mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let sIdx := hst.slots.lookupSendOrZero s.sid
            mkMatchedSameEphSlotsPre S idx msg prep s sIdx spqrSalt? hst.recvCount hst.mkSaltCache
              hst.slots
        else
          let rk1 ← embedUnif sampleBytes32
          match ← primQ (.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg) with
          | none =>
            let (resp, hst') ← prep.finishTag.runPrim S true none
            return .inl (resp, { toAuthHybridState := hst', recvCount := recvCount',
                                 mkSaltCache := hst.mkSaltCache, slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            mkUnmatchedSlotsPre S idx msg prep s.drKey rk1 spqrSalt? rSlot recvCount'
              hst.mkSaltCache slots' sentChal
      | none =>
        let drKey ← embedUnif sampleDRKey96
        let rk1 ← embedUnif sampleBytes32
        match ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg) with
        | none =>
          let (resp, hst') ← prep.finishTag.runPrim S true none
          return .inl (resp, { toAuthHybridState := hst', recvCount := recvCount',
                               mkSaltCache := hst.mkSaltCache, slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          mkUnmatchedSlotsPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
            hst.mkSaltCache slots' sentChal
    else
      let (drKey, roCache') ← embedUnif (evalHkdfRoPure st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ← embedUnif (evalRootKdfRoPure st.rootRoCache drKey.rootKey
                                                     prep.dhRatchet)
      let mkSeed ← primQ (.chainKdfSeed ck1_0)
      let ck1_1 ← primQ (.chainKdfNext ck1_0)
      match ← primQ (.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg) with
      | none =>
        let (resp, hst') ← prep.finishTag.runPrim S true none
        return .inl (resp, { toAuthHybridState := hst', recvCount := recvCount',
                             mkSaltCache := hst.mkSaltCache, slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys ← primQ (.deriveMsgKeys mkSeed spqrSalt?)
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let pt? ← primQ (.aeadDec deriveMessageKeys ad msg.aeadCt)
        let res? := pt?.map (fun pt => (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') ← prep.finishTag.runPrim S true res?
        return .inl (resp, { toAuthHybridState := hst', recvCount := recvCount',
                             mkSaltCache := hst.mkSaltCache, slots := hst.slots })

/-- Pre-oracle `PrimBaseSpec` stage of a `PrfMsgKeys` game step. -/
def mkPre (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.inl (.noneResp, hst))
    else mkSendPre S idx (.sendOPK u i) u bundle m0 m1 hst sentChal
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.inl (.noneResp, hst))
    else mkSendPre S idx (.sendNoOPK u i) u bundle m0 m1 hst sentChal
  | .recvOPK k j o msg => do
    let prep? ← prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState
    mkRecvPre S idx msg prep? hst sentChal
  | .recvNoOPK k j l msg => do
    let prep? ← prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState
    mkRecvPre S idx msg prep? hst sentChal
  | qOther => .inl <$> AuthSubHops1to3.stepAuthOtherPrim S qOther hst

/-- List-length invariant on a continuation produced from a state bounded by `n`. -/
def MkCont.Bounded {S : Setup} (n : Nat) : MkCont S → Prop
  | .send hst .. => AuthListsBounded n hst
  | .recv _ prep _ _ _ _ cache _ _ => PreparedRecvBounded n prep ∧ cache.length ≤ n

/-! ## Combined Step -/

def prfMkRunPre {S : Setup} (pre : OracleComp PrimBaseSpec (MkPre S)) (sentChal : Bool) :
    OracleComp PrfMkSimSpec ((AuthResponse × AuthHybridStateFixed S) × Nat × Bool) := do
  match ← embedPrimMk pre with
  | .inl (r, hst') => return ((r, hst'), 0, sentChal)
  | .inr (salt?, c) =>
    let mk ← deriveMkQ salt?
    let res ← embedPrimMk (c.post mk)
    return (res, 1, sentChal || c.isSend)

/-- Combined shallow `PrfMsgKeys` step tracking challenger query count and updated `sentChal`. -/
def prfMkStepC (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (sentChal : Bool) :
    OracleComp PrfMkSimSpec ((AuthResponse × AuthHybridStateFixed S) × Nat × Bool) :=
  prfMkRunPre (mkPre S idx q hst sentChal) sentChal

end SignalPqxdh.Security.ReductionDsl.AuthPrf
