/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.PqxdhTables
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf

/-!
# `ReductionDsl` Programs for `Auth` Key-Schedule PRF Simulators

Defines `prfCkRedProg` and `prfMsgKeysRedProg`, the `ReductionDsl` witnesses for
`prfCkReductionAuthFixed` and `prfMsgKeysReductionAuthFixed`, along with shared
`AuthHybridStateFixed` types, combinators, and finalization helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open OracleSpec OracleComp

abbrev PT : Type := Ty pqSig

/-! ## Value Type Aliases and Encodings -/

abbrev preKeyBundleTy : PT := bundleT
@[simp] def preKeyBundleToVal (b : PreKeyBundleInput) : preKeyBundleTy.denote := bundleV b

abbrev handshakeHdrTy : PT := hdrT
@[simp] def handshakeHdrToVal (h : HandshakeHdr) : handshakeHdrTy.denote := hdrV h

abbrev preKeyMsgTy : PT := preKeyMsgT
@[simp] def preKeyMsgToVal (m : PreKeyMsg) : preKeyMsgTy.denote := preKeyMsgV m

abbrev sessionIdTy : PT := sidT
@[simp] def sessionIdToVal {S : Setup} (s : SessionId S) : sessionIdTy.denote := sidV s

abbrev drKeyTy : PT := drKeyT
@[simp] def drKeyToVal (k : DRKey) : drKeyTy.denote := drKeyV k

abbrev msgKeysTy : PT := msgKeysT
@[simp] def msgKeysToVal (k : MessageKeys) : msgKeysTy.denote := msgKeysV k
@[simp] def valToMsgKeys (v : msgKeysTy.denote) : MessageKeys := msgKeysOfV v

abbrev authQueryTy : PT := authQT
@[simp] def authQueryToVal {S : Setup} (q : AuthQuery S) : authQueryTy.denote := authQenc q

abbrev authRespTy : PT := authRT
@[simp] def authRespToVal (r : AuthResponse) : authRespTy.denote := authRenc r
@[simp] def valToAuthResp (v : authRespTy.denote) : AuthResponse := authRdec v

@[simp] theorem valToAuthResp_authRespToVal (r : AuthResponse) :
    valToAuthResp (authRespToVal r) = r :=
  authRdec_authRenc r

abbrev principalEntryTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32) .bool)))
@[simp] def principalEntryToVal (e : PrincipalEntry) : principalEntryTy.denote :=
  (e.secIKA0, (e.ikAPk, (e.secIKAsign, (e.ikSignPk, e.corrupted))))

abbrev spkBundleEntryTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 64)
    (.prod (B 3168) (.prod (B 1568) (.prod (B 64) .bool)))))
@[simp] def spkBundleEntryToVal (b : SpkBundleEntry) : spkBundleEntryTy.denote :=
  (b.spkSk, (b.spkPk, (b.spkSig, (b.pqspkSk, (b.pqspkPk, (b.pqspkSig, b.revealed))))))

abbrev opkEntryTy : PT := .prod (B 32) (.prod (B 32) .bool)
@[simp] def opkEntryToVal (o : OpkEntry) : opkEntryTy.denote :=
  (o.opkSk, (o.opkPk, o.consumed))

abbrev sentOPKEventTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (.prod (B 32) .bool)))))))
@[simp] def sentOPKEventToVal (e : SentOPKEvent) : sentOPKEventTy.denote :=
  (e.a0, (e.b0, (e.sb, (e.ob, (e.a1, (e.pk1, (e.ct, (e.m, e.matched))))))))

abbrev sentNoOPKEventTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (.prod (B 32) .bool))))))
@[simp] def sentNoOPKEventToVal (e : SentNoOPKEvent) : sentNoOPKEventTy.denote :=
  (e.a0, (e.b0, (e.sb, (e.a1, (e.pk1, (e.ct, (e.m, e.matched)))))))

abbrev recvdOPKEventTy : PT :=
  .prod .bool (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (B 32))))))))
@[simp] def recvdOPKEventToVal (e : RecvdOPKEvent) : recvdOPKEventTy.denote :=
  (e.bCorr, (e.a0, (e.b0, (e.sb, (e.ob, (e.a1, (e.pk1, (e.ct, e.m))))))))

abbrev recvdNoOPKEventTy : PT :=
  .prod .bool (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (B 32)))))))
@[simp] def recvdNoOPKEventToVal (e : RecvdNoOPKEvent) : recvdNoOPKEventTy.denote :=
  (e.bCorr, (e.a0, (e.b0, (e.sb, (e.a1, (e.pk1, (e.ct, e.m)))))))

abbrev authSessionEntryTy : PT :=
  .prod sessionIdTy (.prod (B 32) (.prod (B 32) (.prod (.opt (B 32)) (.prod (B 1568)
    (.prod .bool (.prod .bool (.prod .bool
      (.prod (B 32) (.prod (B 32) (.prod .bool .bool))))))))))
@[simp] def authSessionEntryToVal {S : Setup} (s : AuthInitiatorEntry S) :
    authSessionEntryTy.denote :=
  (sessionIdToVal s.sid, (s.peerIkPk, (s.peerSpkPk, (s.peerOpkPk?, (s.peerPqspkPk,
    (s.spkHonest, (s.opkHonest, (s.pqspkHonest,
      (s.ekASk, (s.ephASk, (s.fresh, s.challenged)))))))))))

abbrev initKemRecordTy : PT :=
  .prod sessionIdTy (.prod (B 1568) (.prod (B 1568) (B 32)))
@[simp] def initKemRecordToVal {S : Setup}
    (r : _root_.SignalPqxdh.Security.InitKemRecord S) : initKemRecordTy.denote :=
  (sessionIdToVal r.sid, (r.pqspkPk, (r.kemCt, r.kemSs)))

abbrev recvKemRecordTy : PT :=
  .prod .nat (.prod .nat (.prod (B 1568) (.prod (B 3168) (.prod (B 1568) (B 32)))))
@[simp] def recvKemRecordToVal
    (r : _root_.SignalPqxdh.Security.RecvKemRecord) : recvKemRecordTy.denote :=
  (r.k, (r.j, (r.pqspkPk, (r.pqspkSk, (r.kemCt, r.kemSs)))))

abbrev idealAuthSessionTy : PT :=
  .prod sessionIdTy (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (.opt (B 32))
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (.prod (B 32) (.prod (.opt (B 32))
      (.prod (B 32) (.prod (B 158) (.prod (B 32) (.prod (B 32) (.prod drKeyTy
        (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32) msgKeysTy))))))))))))))))))
@[simp] def idealAuthSessionToVal {S : Setup} (s : IdealAuthSession S) :
    idealAuthSessionTy.denote :=
  (sessionIdToVal s.sid, (s.ikAPk, (s.peerIkPk, (s.peerSpkPk, (s.peerOpkPk?,
    (s.ekAPk, (s.peerPqspkPk, (s.kemCt, (s.ephAPk, (s.spqrSalt?,
      (s.pqRatchetMsg, (s.ad, (s.aeadCt, (s.msgPlain, (drKeyToVal s.drKey,
        (s.rk1, (s.ck1_0, (s.mkSeed, (s.ck1_1, msgKeysToVal s.deriveMessageKeys)))))))))))))))))))

abbrev authStateTy : PT :=
  .prod .bool (.prod .bool
    (.prod (.list (.prod .nat principalEntryTy))
      (.prod (.list (.prod (.prod .nat .nat) spkBundleEntryTy))
        (.prod (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy))
          (.prod (.list authSessionEntryTy)
            (.prod (.list sessionIdTy)
              (.prod (.list (.prod .nat (.prod .nat .nat)))
                (.prod (.list (.prod .nat (.prod .nat .nat)))
                  (.prod (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))
                    (.prod (.list sentOPKEventTy)
                      (.prod (.list sentNoOPKEventTy)
                        (.prod (.list recvdOPKEventTy)
                          (.prod (.list recvdNoOPKEventTy)
                            (.prod (.list (.prod (B 192) drKeyTy))
                              (.prod (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
                                (.list (.prod (B 32) (B 32))))))))))))))))))

@[simp] def authStateToVal {S : Setup} (st : AuthState S) : authStateTy.denote :=
  (st.secb, (st.hasWonAuth,
    (st.principals.map (Prod.map id principalEntryToVal),
    (st.spkBundles.map (Prod.map id spkBundleEntryToVal),
    (st.opkEntries.map (Prod.map (fun (k, j, o) => (k, (j, o))) opkEntryToVal),
    (st.sessions.map authSessionEntryToVal,
    (st.usedSendSessions.map sessionIdToVal,
    (st.usedRecvOPK.map (fun (k, j, o) => (k, (j, o))),
    (st.usedRecvNoOPK.map (fun (k, j, l) => (k, (j, l))),
    (st.seenKyberBaseKeys.map (fun (k, p, s, e) => (k, (p, (s, e)))),
    (st.sentOPKEvents.map sentOPKEventToVal,
    (st.sentNoOPKEvents.map sentNoOPKEventToVal,
    (st.recvdOPKEvents.map recvdOPKEventToVal,
    (st.recvdNoOPKEvents.map recvdNoOPKEventToVal,
    (st.roCache.map (Prod.map id drKeyToVal),
    (st.rootRoCache, st.advKeys))))))))))))))))

abbrev authHybridStateTy : PT :=
  .prod authStateTy
    (.prod (.list initKemRecordTy)
      (.prod (.list recvKemRecordTy) (.list idealAuthSessionTy)))

@[simp] def authHybridStateToVal {S : Setup} (hst : AuthHybridState S) :
    authHybridStateTy.denote :=
  (authStateToVal hst.base, (hst.initKemRecs.map initKemRecordToVal,
    (hst.recvKemRecs.map recvKemRecordToVal, hst.idealSessions.map idealAuthSessionToVal)))

abbrev authMkSaltCacheTy : PT :=
  .list (.prod (.prod sessionIdTy (.opt (B 32))) (.prod .nat msgKeysTy))

abbrev sendSlotTblTy : PT := .tbl (.tbl (.opt .nat))
abbrev recvSlotTblTy : PT := .tbl (.opt .nat)
abbrev authSlotStateTy : PT :=
  .prod .nat (.prod sendSlotTblTy (.prod sendSlotTblTy recvSlotTblTy))

@[simp] def authSlotStateToVal (ss : AuthSlotState) : authSlotStateTy.denote :=
  (ss.nextSlot, (ss.sendOpkTbl, (ss.sendNoOpkTbl, ss.recvTbl)))

abbrev authHybridStateFixedTy : PT :=
  .prod authHybridStateTy (.prod .nat (.prod authMkSaltCacheTy authSlotStateTy))

@[simp] def authHybridStateFixedWithSlotsToVal {S : Setup}
    (hst : AuthHybridStateFixed S) (ss : AuthSlotState) :
    authHybridStateFixedTy.denote :=
  (authHybridStateToVal hst.toAuthHybridState, (hst.recvCount,
    (hst.mkSaltCache.map (fun ((sid, salt?), (rc, mk)) =>
      ((sessionIdToVal sid, salt?), (rc, msgKeysToVal mk))),
     authSlotStateToVal ss)))

@[simp] def authHybridStateFixedToVal {S : Setup} (hst : AuthHybridStateFixed S) :
    authHybridStateFixedTy.denote :=
  authHybridStateFixedWithSlotsToVal hst hst.slots

/-! ## Combinators, Binders, and Operation Helpers -/

/-- Context extension `Ext Γ Δ`: `Δ` extends `Γ` by finitely many innermost binders. -/
class Ext (Γ Δ : List PT) where
  wk : {τ : PT} → Var Γ τ → Var Δ τ

instance (priority := high) Ext.refl {Γ : List PT} : Ext Γ Γ := ⟨fun x => x⟩
instance Ext.step {Γ Δ : List PT} {σ : PT} [h : Ext Γ Δ] : Ext Γ (σ :: Δ) :=
  ⟨fun x => .succ (h.wk x)⟩

def v {Γ Δ : List PT} {τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) : Expr pqxdhOps Δ τ := .var (h.wk x)

def boolOr {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool :=
  .ite a (.bool true) b

def boolBeq {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool :=
  .ite a b (.not b)

def Comp.letC {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {a b : PT}
    (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b) : Comp pqxdhOps I Γ b :=
  .bind (.ret e) k

/-- Lifts a primitive-only `Comp` into `pqChalIface C` by routing all queries to `.inl`. -/
def liftPrimComp {C : ChallengerOracle} :
    {Γ : List PT} → {t : PT} → Comp pqxdhOps pqPrimIface Γ t → Comp pqxdhOps (pqChalIface C) Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind m k => .bind (liftPrimComp m) (liftPrimComp k)
  | _, _, .ite c t e => .ite c (liftPrimComp t) (liftPrimComp e)
  | _, _, .caseOpt e n s => .caseOpt e (liftPrimComp n) (liftPrimComp s)
  | _, _, .caseSum e l r => .caseSum e (liftPrimComp l) (liftPrimComp r)
  | _, _, .sample sc e => Comp.sample (I := pqChalIface C) sc e
  | _, _, .query g e => Comp.query (I := pqChalIface C) (Sum.inl g) e
  | _, _, .iter n init body => .iter n init (liftPrimComp body)
  | _, _, .findM K l p => .findM K l (liftPrimComp p)
  | _, _, .anyM K l p => .anyM K l (liftPrimComp p)
  | _, _, .mapM K l f => .mapM K l (liftPrimComp f)
  | _, _, .consumeFirstM K l p mk => .consumeFirstM K l (liftPrimComp p) mk
  | _, _, .foldM K l init step => .foldM K l init (liftPrimComp step)

def bindV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  .bind m (k .zero)

def letV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  Comp.letC e (k .zero)

def caseOptV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  .caseOpt o kn (ks .zero)

def caseSumV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ τ : PT}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) : Comp pqxdhOps I Γ τ :=
  .caseSum s (kl .zero) (kr .zero)

def findMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ (.opt τ) :=
  .findM K xs (p .zero)

def anyMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ .bool :=
  .anyM K xs (p .zero)

def consumeFirstMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ : PT}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool)
    (mark : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) τ) : Comp pqxdhOps I Γ (.prod .bool (.list τ)) :=
  .consumeFirstM K xs (p .zero) (mark .zero)

def eLet {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ τ₂ := .letE e (k .zero)

def eLet2 {Γ : List PT} {τ₁ τ₂ τ : PT} (a : Expr pqxdhOps Γ τ₁) (b : Expr pqxdhOps Γ τ₂)
    (k : Var (τ₁ :: .prod τ₁ τ₂ :: Γ) τ₁ → Var (τ₂ :: τ₁ :: .prod τ₁ τ₂ :: Γ) τ₂ →
      Expr pqxdhOps (τ₂ :: τ₁ :: .prod τ₁ τ₂ :: Γ) τ) :
    Expr pqxdhOps Γ τ :=
  eLet (.pair a b) fun p => eLet (.fst (v p)) fun x => eLet (.snd (v p)) fun y => k x y

def eCaseOpt {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ τ₂ := .caseOpt o kn (ks .zero)

def eCaseSum {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) : Expr pqxdhOps Γ τ :=
  .caseSum s (kl .zero) (kr .zero)

def eFind {Γ : List PT} {τ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ (.opt τ) := .findB K xs (p .zero)

def eAny {Γ : List PT} {τ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ .bool := .anyB K xs (p .zero)

def eMap {Γ : List PT} {τ₁ τ₂ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ (.list τ₂) :=
  .mapB K xs (f .zero)

def litB {Γ : List PT} (w : ℕ+) (bs : Bytes) : Expr pqxdhOps Γ (B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.lit w bs)) .unit

def catB {Γ : List PT} (m n : ℕ+) (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    Expr pqxdhOps Γ (B (m + n)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.cat m n)) (.pair a b)

def bytesCons {Γ : List PT} (b : UInt8) (w : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    Expr pqxdhOps Γ (B (w + 1)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.cons b w)) x

def widenB {Γ : List PT} (w d : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    Expr pqxdhOps Γ (B (w + d)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.widen w d)) x

def takeKB {Γ : List PT} (w k : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    Expr pqxdhOps Γ (B k) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.takeK w k)) x

def bytesLen {Γ : List PT} (w : ℕ+) (x : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ .nat :=
  Expr.op (O := pqxdhOps) (Sum.inl (.len w)) x

def bytesBeq {Γ : List PT} (w : ℕ+) (a b : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inl (.eq w w)) (.pair a b)

def bytesVarint {Γ : List PT} (n : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ (B 10) :=
  Expr.op (O := pqxdhOps) (Sum.inl .varint) n

def u32OfNat {Γ : List PT} (n : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ U32 :=
  Expr.op (O := pqxdhOps) (Sum.inr .ofNat) n

def u32Beq {Γ : List PT} (a b : Expr pqxdhOps Γ U32) : Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inr .eq) (.pair a b)

def samplePrim {Γ : List PT} (s : PSamp) : Comp pqxdhOps pqPrimIface Γ s.ty :=
  Comp.sample (I := pqPrimIface) s .unit

def sampleChal {C : ChallengerOracle} {Γ : List PT} (s : PSamp) : Comp pqxdhOps (pqChalIface C) Γ s.ty :=
  Comp.sample (I := pqChalIface C) s .unit

def queryPrim {Γ : List PT} (g : PTag) (e : Expr pqxdhOps Γ g.dom) : Comp pqxdhOps pqPrimIface Γ g.cod :=
  Comp.query (I := pqPrimIface) g e

def queryDeriveMk {Γ : List PT} (e : Expr pqxdhOps Γ (.opt (B 32))) :
    Comp pqxdhOps pqPrfMkIface Γ msgKeysTy :=
  Comp.query (I := pqPrfMkIface) (Sum.inr (32 : ℕ+)) e

/-! ## Field Projections and Constructors -/

def peSecIKA0 {Γ} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) := .fst e
def peIkAPk {Γ} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def peSecIKAsign {Γ} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
def peIkSignPk {Γ} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
def peCorrupted {Γ} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd e)))

def sbSpkSk {Γ} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 32) := .fst e
def sbSpkPk {Γ} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def sbPqspkSk {Γ} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 3168) :=
  .fst (.snd (.snd (.snd e)))
def sbPqspkPk {Γ} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd e))))

def oeOpkSk {Γ} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ (B 32) := .fst e
def oeOpkPk {Γ} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def oeConsumed {Γ} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ .bool := .snd (.snd e)

def pkbIkB {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (B 32) := .fst b
def pkbSpkId {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ U32 := .fst (.snd b)
def pkbSpkB {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd b))
def pkbSpkSig {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (B 64) :=
  .fst (.snd (.snd (.snd b)))
def pkbOpkB? {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (.opt (.prod U32 (B 32))) :=
  .fst (.snd (.snd (.snd (.snd b))))
def pkbPqspkId {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ U32 :=
  .fst (.snd (.snd (.snd (.snd (.snd b)))))
def pkbPqspkB {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd b))))))
def pkbPqspkSig {Γ} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ (B 64) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))

def hdrIkAPk {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ (B 32) := .fst h
def hdrEkAPk {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd h)
def hdrSpkId {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ U32 := .fst (.snd (.snd h))
def hdrOpkId? {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ (.opt U32) :=
  .fst (.snd (.snd (.snd h)))
def hdrPqspkId {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ U32 :=
  .fst (.snd (.snd (.snd (.snd h))))
def hdrKemCt {Γ} (h : Expr pqxdhOps Γ handshakeHdrTy) : Expr pqxdhOps Γ (B 1568) :=
  .snd (.snd (.snd (.snd (.snd h))))

def pkmHdr {Γ} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ handshakeHdrTy := .fst m
def pkmEphAPk {Γ} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd m)
def pkmPqRatchetMsg {Γ} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd m))
def pkmAeadCt {Γ} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ (B 32) := .snd (.snd (.snd m))

def soA0 {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst e
def soB0 {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def soSb {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
def soOb {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
def soA1 {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd e))))
def soPk1 {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def soCt {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def soM {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
def soMatched {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
def soMarkMatched {Γ} (e : Expr pqxdhOps Γ sentOPKEventTy) : Expr pqxdhOps Γ sentOPKEventTy :=
  .pair (soA0 e) (.pair (soB0 e) (.pair (soSb e) (.pair (soOb e)
    (.pair (soA1 e) (.pair (soPk1 e) (.pair (soCt e) (.pair (soM e) (.bool true))))))))

def snoA0 {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst e
def snoB0 {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def snoSb {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
def snoA1 {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
def snoPk1 {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd e))))
def snoCt {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def snoM {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def snoMatched {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def snoMarkMatched {Γ} (e : Expr pqxdhOps Γ sentNoOPKEventTy) : Expr pqxdhOps Γ sentNoOPKEventTy :=
  .pair (snoA0 e) (.pair (snoB0 e) (.pair (snoSb e)
    (.pair (snoA1 e) (.pair (snoPk1 e) (.pair (snoCt e) (.pair (snoM e) (.bool true)))))))

def roBCorr {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ .bool := .fst e
def roA0 {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def roB0 {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
def roSb {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
def roOb {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd e))))
def roA1 {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def roPk1 {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def roCt {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
def roM {Γ} (e : Expr pqxdhOps Γ recvdOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))

def rnoBCorr {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ .bool := .fst e
def rnoA0 {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def rnoB0 {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
def rnoSb {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
def rnoA1 {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd e))))
def rnoPk1 {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
def rnoCt {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
def rnoM {Γ} (e : Expr pqxdhOps Γ recvdNoOPKEventTy) : Expr pqxdhOps Γ (B 32) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))

def aseSpkHonest {Γ} (s : Expr pqxdhOps Γ authSessionEntryTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def asePqspkHonest {Γ} (s : Expr pqxdhOps Γ authSessionEntryTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def aseEkASk {Γ} (s : Expr pqxdhOps Γ authSessionEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def aseFresh {Γ} (s : Expr pqxdhOps Γ authSessionEntryTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))
def aseChallenged {Γ} (s : Expr pqxdhOps Γ authSessionEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def ikrPqspkPk {Γ} (r : Expr pqxdhOps Γ initKemRecordTy) : Expr pqxdhOps Γ (B 1568) := .fst (.snd r)
def ikrKemCt {Γ} (r : Expr pqxdhOps Γ initKemRecordTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd r))
def ikrKemSs {Γ} (r : Expr pqxdhOps Γ initKemRecordTy) : Expr pqxdhOps Γ (B 32) :=
  .snd (.snd (.snd r))

def rkrPqspkPk {Γ} (r : Expr pqxdhOps Γ recvKemRecordTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd r))
def rkrKemCt {Γ} (r : Expr pqxdhOps Γ recvKemRecordTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd r))))
def rkrKemSs {Γ} (r : Expr pqxdhOps Γ recvKemRecordTy) : Expr pqxdhOps Γ (B 32) :=
  .snd (.snd (.snd (.snd (.snd r))))

def iasSid {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ sessionIdTy := .fst s
def iasIkAPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd s)
def iasPeerIkPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd s))
def iasPeerSpkPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd s)))
def iasPeerOpkPk? {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (.opt (B 32)) :=
  .fst (.snd (.snd (.snd (.snd s))))
def iasEkAPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def iasPeerPqspkPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def iasKemCt {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def iasEphAPk {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def iasSpqrSalt? {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (.opt (B 32)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def iasDrKey {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ drKeyTy :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))))))
def iasRk1 {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))))))))
def iasMkSeed {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))))))))))
def iasCk1_1 {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))))))))))
def iasMsgKeys {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ msgKeysTy :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))))))))))

def asSecb {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ .bool := .fst st
def asHasWonAuth {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ .bool := .fst (.snd st)
def asPrincipals {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) :=
  .fst (.snd (.snd st))
def asSpkBundles {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) :=
  .fst (.snd (.snd (.snd st)))
def asOpkEntries {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) :=
  .fst (.snd (.snd (.snd (.snd st))))
def asSessions {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ (.list authSessionEntryTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd st)))))
def asUsedSendSessions {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ (.list sessionIdTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd st))))))
def asUsedRecvOPK {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))
def asUsedRecvNoOPK {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st))))))))
def asUsedKyberTriples {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))
def asSentOPKEvents {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ (.list sentOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st))))))))))
def asSentNoOPKEvents {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list sentNoOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))))
def asRecvdOPKEvents {Γ} (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ (.list recvdOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st))))))))))))
def asRecvdNoOPKEvents {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list recvdNoOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))))))
def asRoCache {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd st))))))))))))))
def asRootRoCache {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))))))))
def asAdvKeys {Γ} (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd st)))))))))))))))

def ahsBase {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy) : Expr pqxdhOps Γ authStateTy := .fst hst
def ahsInitKemRecs {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy) :
    Expr pqxdhOps Γ (.list initKemRecordTy) :=
  .fst (.snd hst)
def ahsRecvKemRecs {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy) :
    Expr pqxdhOps Γ (.list recvKemRecordTy) :=
  .fst (.snd (.snd hst))
def ahsIdealSessions {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy) :
    Expr pqxdhOps Γ (.list idealAuthSessionTy) :=
  .snd (.snd (.snd hst))

def ahsfHybrid {Γ} (hst : Expr pqxdhOps Γ authHybridStateFixedTy) :
    Expr pqxdhOps Γ authHybridStateTy := .fst hst
def ahsfRecvCount {Γ} (hst : Expr pqxdhOps Γ authHybridStateFixedTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd hst)
def ahsfMkSaltCache {Γ} (hst : Expr pqxdhOps Γ authHybridStateFixedTy) :
    Expr pqxdhOps Γ authMkSaltCacheTy := .fst (.snd (.snd hst))
@[reducible] def ahsfSlots {Γ} (hst : Expr pqxdhOps Γ authHybridStateFixedTy) :
    Expr pqxdhOps Γ authSlotStateTy := .snd (.snd (.snd hst))

def natEq {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool := .eqN a b
def natLt {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool := .lt a b
def nat2Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat .nat)) : Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b)) (natEq (.snd a) (.snd b))
def nat3Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat (.prod .nat .nat))) : Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b)) (nat2Eq (.snd a) (.snd b))
def bytes2Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod (B 32) (B 32))) : Expr pqxdhOps Γ .bool :=
  .and (bytesBeq 32 (.fst a) (.fst b)) (bytesBeq 32 (.snd a) (.snd b))

def optU32Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt U32)) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseOpt (v a)
    (eCaseOpt (v b) (.bool true) fun _ => .bool false)
    fun x => eCaseOpt (v b) (.bool false) fun y => u32Beq (v x) (v y)

def sidEq {Γ : List PT} (a b : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseSum (v a)
    (fun x => eCaseSum (v b) (fun y => nat2Eq (v x) (v y)) fun _ => .bool false)
    fun a1 => eCaseSum (v a1)
      (fun x => eCaseSum (v b) (fun _ => .bool false) fun b1 =>
        eCaseSum (v b1) (fun y => nat2Eq (v x) (v y)) fun _ => .bool false)
      fun a2 => eCaseSum (v a2)
        (fun x => eCaseSum (v b) (fun _ => .bool false) fun b1 =>
          eCaseSum (v b1) (fun _ => .bool false) fun b2 =>
            eCaseSum (v b2) (fun y => nat3Eq (v x) (v y)) fun _ => .bool false)
        fun x => eCaseSum (v b) (fun _ => .bool false) fun b1 =>
          eCaseSum (v b1) (fun _ => .bool false) fun b2 =>
            eCaseSum (v b2) (fun _ => .bool false) fun y => nat3Eq (v x) (v y)

def saltBytesE {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ (B 32) :=
  eCaseOpt o (litB 32 (List.replicate 32 0)) fun s =>
    takeKB 64 32 (catB 32 32 (v s) (litB 32 (List.replicate 32 0)))

def sameSaltKeyE {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ .bool :=
  bytesBeq 32 (saltBytesE a) (saltBytesE b)

def kyberEq {Γ : List PT}
    (a b : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) : Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b))
    (.and (u32Beq (.fst (.snd a)) (.fst (.snd b)))
      (.and (u32Beq (.fst (.snd (.snd a))) (.fst (.snd (.snd b))))
        (bytesBeq 32 (.snd (.snd (.snd a))) (.snd (.snd (.snd b))))))

def isSomeE {Γ : List PT} {τ : PT} (o : Expr pqxdhOps Γ (.opt τ)) : Expr pqxdhOps Γ .bool :=
  .caseOpt o (.bool false) (.bool true)

def optFst {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) :
    Expr pqxdhOps Γ (.opt τ₁) :=
  eCaseOpt o .none fun p => .some (.fst (v p))

def optSnd {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) :
    Expr pqxdhOps Γ (.opt τ₂) :=
  eCaseOpt o .none fun p => .some (.snd (v p))

def encEC {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 33) :=
  bytesCons TAG_EC_DJB 32 pk

def encKEM {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) : Expr pqxdhOps Γ (B 1569) :=
  bytesCons TAG_KYBER_1024 1568 pk

def firstMsgADE {Γ : List PT} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 158) :=
  catB 115 43
    (catB 111 4
      (catB 67 44
        (catB 66 1 (catB 33 33 (encEC ikA) (encEC ikB)) (litB 1 [0x44]))
        (bytesCons ((8 * 1 + 2 : Nat).toUInt8) 43
          (.letE (encEC eph) (catB 10 33 (bytesVarint (bytesLen 33 (.var .zero))) (.var .zero)))))
      (litB 4 [0x10, 0x00, 0x18, 0x00]))
    (.ite (natEq (bytesLen 32 pq) (.nat 0)) (litB 43 [])
      (bytesCons ((8 * 5 + 2 : Nat).toUInt8) 42
        (catB 10 32 (bytesVarint (bytesLen 32 pq)) pq)))

def buildSecretsE {Γ : List PT} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 192) :=
  eLet2 (.pair dh1 (.pair dh2 (.pair dh3 ss))) dh4? fun p d =>
    eCaseOpt (v d)
      (widenB 160 32
        (catB 128 32
          (catB 96 32
            (catB 64 32
              (catB 32 32 (litB 32 F_X25519) (.fst (v p)))
              (.fst (.snd (v p))))
            (.fst (.snd (.snd (v p)))))
          (.snd (.snd (.snd (v p))))))
      fun dh4 =>
        catB 160 32
          (catB 128 32
            (catB 96 32
              (catB 64 32
                (catB 32 32 (litB 32 F_X25519) (.fst (v p)))
                (.fst (.snd (v p))))
              (.fst (.snd (.snd (v p)))))
            (v dh4))
          (.snd (.snd (.snd (v p))))

def kyberCheckE {Γ : List PT} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    Expr pqxdhOps Γ (.prod .bool (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))) :=
  eLet2 used entry fun u e =>
    .ite (eAny K (v u) fun t => kyberEq (v e) (v t))
      (.pair (.bool false) (v u))
      (.pair (.bool true) (.cons (v e) (v u)))

def sessionSlotIndexE (S : Setup) {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .nat :=
  eCaseSum sid
    (fun ui => .add (.mulK (if S.N_id = 0 then 0 else S.N_send_opk) (.fst (v ui))) (.snd (v ui)))
    fun r1 => eCaseSum (v r1)
      (fun ui => .add (.nat S.N_send_opk_tot)
        (.add (.mulK (if S.N_id = 0 then 0 else S.N_send_no_opk) (.fst (v ui))) (.snd (v ui))))
      fun _ => .nat 0

@[reducible] def assNext {Γ} (ss : Expr pqxdhOps Γ authSlotStateTy) : Expr pqxdhOps Γ .nat := .fst ss
@[reducible] def assSendOpk {Γ} (ss : Expr pqxdhOps Γ authSlotStateTy) :
    Expr pqxdhOps Γ sendSlotTblTy := .fst (.snd ss)
@[reducible] def assSendNoOpk {Γ} (ss : Expr pqxdhOps Γ authSlotStateTy) :
    Expr pqxdhOps Γ sendSlotTblTy := .fst (.snd (.snd ss))
@[reducible] def assRecv {Γ} (ss : Expr pqxdhOps Γ authSlotStateTy) :
    Expr pqxdhOps Γ recvSlotTblTy := .snd (.snd (.snd ss))
@[reducible] def assMk {Γ} (next : Expr pqxdhOps Γ .nat)
    (opkT noOpkT : Expr pqxdhOps Γ sendSlotTblTy) (recvT : Expr pqxdhOps Γ recvSlotTblTy) :
    Expr pqxdhOps Γ authSlotStateTy :=
  .pair next (.pair opkT (.pair noOpkT recvT))

@[reducible] def emptyAuthSlotStE {Γ} : Expr pqxdhOps Γ authSlotStateTy :=
  assMk (.nat 0) (.tconst (.tconst .none)) (.tconst (.tconst .none)) (.tconst .none)

@[reducible] def lookupSendSlotE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ (.opt .nat) :=
  eLet2 ss sid fun s sidV =>
    eCaseSum (v sidV)
      (fun ui => .tget (.tget (assSendOpk (v s)) (.fst (v ui))) (.snd (v ui)))
      fun r1 => eCaseSum (v r1)
        (fun ui => .tget (.tget (assSendNoOpk (v s)) (.fst (v ui))) (.snd (v ui)))
        fun _ => .none

@[reducible] def lookupSendSlotOrZeroE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .nat :=
  eCaseOpt (lookupSendSlotE ss sid) (.nat 0) fun k => v k

@[reducible] def allocSendSlotE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ (.prod .nat authSlotStateTy) :=
  eLet2 ss sid fun s sidV =>
    eCaseSum (v sidV)
      (fun ui =>
        eLet (.tget (assSendOpk (v s)) (.fst (v ui))) fun row =>
          eCaseOpt (.tget (v row) (.snd (v ui)))
            (eLet (assNext (v s)) fun k =>
              .pair (v k)
                (assMk (.add (v k) (.nat 1))
                  (.tset (assSendOpk (v s)) (.fst (v ui))
                    (.tset (v row) (.snd (v ui)) (.some (v k))))
                  (assSendNoOpk (v s))
                  (assRecv (v s))))
            fun k => .pair (v k) (v s))
      fun r1 => eCaseSum (v r1)
        (fun ui =>
          eLet (.tget (assSendNoOpk (v s)) (.fst (v ui))) fun row =>
            eCaseOpt (.tget (v row) (.snd (v ui)))
              (eLet (assNext (v s)) fun k =>
                .pair (v k)
                  (assMk (.add (v k) (.nat 1))
                    (assSendOpk (v s))
                    (.tset (assSendNoOpk (v s)) (.fst (v ui))
                      (.tset (v row) (.snd (v ui)) (.some (v k))))
                    (assRecv (v s))))
              fun k => .pair (v k) (v s))
        fun _ => .pair (.nat 0) (v s)

@[reducible] def lookupRecvSlotE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (rc : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ (.opt .nat) :=
  .tget (assRecv ss) rc

@[reducible] def lookupRecvSlotOrZeroE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (rc : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .nat :=
  eCaseOpt (lookupRecvSlotE ss rc) (.nat 0) fun k => v k

@[reducible] def allocRecvSlotE {Γ : List PT} (ss : Expr pqxdhOps Γ authSlotStateTy)
    (rc : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ (.prod .nat authSlotStateTy) :=
  eLet2 ss rc fun s rcV =>
    eCaseOpt (.tget (assRecv (v s)) (v rcV))
      (eLet (assNext (v s)) fun k =>
        .pair (v k)
          (assMk (.add (v k) (.nat 1))
            (assSendOpk (v s))
            (assSendNoOpk (v s))
            (.tset (assRecv (v s)) (v rcV) (.some (v k)))))
      fun k => .pair (v k) (v s)

@[reducible] def peMk {Γ} (s0 ik s1 sp : Expr pqxdhOps Γ (B 32)) (c : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ principalEntryTy :=
  .pair s0 (.pair ik (.pair s1 (.pair sp c)))

@[reducible] def peUpd {Γ} (e : Expr pqxdhOps Γ principalEntryTy)
    (corrupted : Expr pqxdhOps Γ .bool := peCorrupted e) : Expr pqxdhOps Γ principalEntryTy :=
  peMk (peSecIKA0 e) (peIkAPk e) (peSecIKAsign e) (peIkSignPk e) corrupted

@[reducible] def sbMk {Γ} (sk pk : Expr pqxdhOps Γ (B 32)) (sig : Expr pqxdhOps Γ (B 64))
    (pqsk : Expr pqxdhOps Γ (B 3168)) (pqpk : Expr pqxdhOps Γ (B 1568))
    (pqsig : Expr pqxdhOps Γ (B 64)) (rev : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ spkBundleEntryTy :=
  .pair sk (.pair pk (.pair sig (.pair pqsk (.pair pqpk (.pair pqsig rev)))))

@[reducible] def oeMk {Γ} (sk pk : Expr pqxdhOps Γ (B 32)) (cons : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ opkEntryTy :=
  .pair sk (.pair pk cons)

@[reducible] def oeUpd {Γ} (e : Expr pqxdhOps Γ opkEntryTy)
    (consumed : Expr pqxdhOps Γ .bool := oeConsumed e) : Expr pqxdhOps Γ opkEntryTy :=
  oeMk (oeOpkSk e) (oeOpkPk e) consumed

@[reducible] def buMk {Γ} (ikB : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ U32)
    (spkB : Expr pqxdhOps Γ (B 32)) (spkSig : Expr pqxdhOps Γ (B 64))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) (pqspkId : Expr pqxdhOps Γ U32)
    (pqspkB : Expr pqxdhOps Γ (B 1568)) (pqspkSig : Expr pqxdhOps Γ (B 64)) :
    Expr pqxdhOps Γ preKeyBundleTy :=
  .pair ikB (.pair spkId (.pair spkB (.pair spkSig
    (.pair opkB? (.pair pqspkId (.pair pqspkB pqspkSig))))))

@[reducible] def hdMk {Γ} (ikA ekA : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ U32)
    (opkId? : Expr pqxdhOps Γ (.opt U32)) (pqspkId : Expr pqxdhOps Γ U32)
    (kemCt : Expr pqxdhOps Γ (B 1568)) : Expr pqxdhOps Γ handshakeHdrTy :=
  .pair ikA (.pair ekA (.pair spkId (.pair opkId? (.pair pqspkId kemCt))))

@[reducible] def pmMk {Γ} (hdr : Expr pqxdhOps Γ handshakeHdrTy)
    (eph pq ct : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ preKeyMsgTy :=
  .pair hdr (.pair eph (.pair pq ct))

@[reducible] def seMk {Γ} (sid : Expr pqxdhOps Γ sessionIdTy)
    (peerIk peerSpk : Expr pqxdhOps Γ (B 32)) (peerOpk? : Expr pqxdhOps Γ (.opt (B 32)))
    (peerPqspk : Expr pqxdhOps Γ (B 1568)) (spkHon opkHon pqspkHon : Expr pqxdhOps Γ .bool)
    (ekASk ephASk : Expr pqxdhOps Γ (B 32)) (fresh chal : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ authSessionEntryTy :=
  .pair sid (.pair peerIk (.pair peerSpk (.pair peerOpk? (.pair peerPqspk
    (.pair spkHon (.pair opkHon (.pair pqspkHon
      (.pair ekASk (.pair ephASk (.pair fresh chal))))))))))

@[reducible] def iasMk {Γ} (sid : Expr pqxdhOps Γ sessionIdTy)
    (ikA peerIk peerSpk : Expr pqxdhOps Γ (B 32)) (peerOpk? : Expr pqxdhOps Γ (.opt (B 32)))
    (ekA : Expr pqxdhOps Γ (B 32)) (peerPqspk kemCt : Expr pqxdhOps Γ (B 1568))
    (ephA : Expr pqxdhOps Γ (B 32)) (spqrSalt? : Expr pqxdhOps Γ (.opt (B 32)))
    (pqMsg : Expr pqxdhOps Γ (B 32)) (ad : Expr pqxdhOps Γ (B 158))
    (aeadCt msgPlain : Expr pqxdhOps Γ (B 32)) (drKey : Expr pqxdhOps Γ drKeyTy)
    (rk1 ck1_0 mkSeed ck1_1 : Expr pqxdhOps Γ (B 32)) (deriveMessageKeys : Expr pqxdhOps Γ msgKeysTy) :
    Expr pqxdhOps Γ idealAuthSessionTy :=
  .pair sid (.pair ikA (.pair peerIk (.pair peerSpk (.pair peerOpk?
    (.pair ekA (.pair peerPqspk (.pair kemCt (.pair ephA (.pair spqrSalt?
      (.pair pqMsg (.pair ad (.pair aeadCt (.pair msgPlain (.pair drKey
        (.pair rk1 (.pair ck1_0 (.pair mkSeed (.pair ck1_1 deriveMessageKeys))))))))))))))))))

@[reducible] def soMk {Γ} (a0 b0 sb ob a1 : Expr pqxdhOps Γ (B 32))
    (pk1 ct : Expr pqxdhOps Γ (B 1568)) (m : Expr pqxdhOps Γ (B 32)) (matched : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ sentOPKEventTy :=
  .pair a0 (.pair b0 (.pair sb (.pair ob (.pair a1 (.pair pk1 (.pair ct (.pair m matched)))))))

@[reducible] def snoMk {Γ} (a0 b0 sb a1 : Expr pqxdhOps Γ (B 32))
    (pk1 ct : Expr pqxdhOps Γ (B 1568)) (m : Expr pqxdhOps Γ (B 32)) (matched : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ sentNoOPKEventTy :=
  .pair a0 (.pair b0 (.pair sb (.pair a1 (.pair pk1 (.pair ct (.pair m matched))))))

@[reducible] def roMk {Γ} (bCorr : Expr pqxdhOps Γ .bool) (a0 b0 sb ob a1 : Expr pqxdhOps Γ (B 32))
    (pk1 ct : Expr pqxdhOps Γ (B 1568)) (m : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ recvdOPKEventTy :=
  .pair bCorr (.pair a0 (.pair b0 (.pair sb (.pair ob (.pair a1 (.pair pk1 (.pair ct m)))))))

@[reducible] def rnoMk {Γ} (bCorr : Expr pqxdhOps Γ .bool) (a0 b0 sb a1 : Expr pqxdhOps Γ (B 32))
    (pk1 ct : Expr pqxdhOps Γ (B 1568)) (m : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ recvdNoOPKEventTy :=
  .pair bCorr (.pair a0 (.pair b0 (.pair sb (.pair a1 (.pair pk1 (.pair ct m))))))

@[reducible] def ikrMk {Γ} (sid : Expr pqxdhOps Γ sessionIdTy)
    (pqPk ct : Expr pqxdhOps Γ (B 1568)) (ss : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ initKemRecordTy :=
  .pair sid (.pair pqPk (.pair ct ss))

@[reducible] def rkrMk {Γ} (k j : Expr pqxdhOps Γ .nat) (pqPk : Expr pqxdhOps Γ (B 1568))
    (pqSk : Expr pqxdhOps Γ (B 3168)) (ct : Expr pqxdhOps Γ (B 1568)) (ss : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ recvKemRecordTy :=
  .pair k (.pair j (.pair pqPk (.pair pqSk (.pair ct ss))))

@[reducible] def stMk {Γ} (secb hasWon : Expr pqxdhOps Γ .bool)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)))
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (sess : Expr pqxdhOps Γ (.list authSessionEntryTy))
    (usedS : Expr pqxdhOps Γ (.list sessionIdTy))
    (usedO usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))))
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sOE : Expr pqxdhOps Γ (.list sentOPKEventTy))
    (sNE : Expr pqxdhOps Γ (.list sentNoOPKEventTy))
    (rOE : Expr pqxdhOps Γ (.list recvdOPKEventTy))
    (rNE : Expr pqxdhOps Γ (.list recvdNoOPKEventTy))
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)))
    (root : Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))))
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) : Expr pqxdhOps Γ authStateTy :=
  .pair secb (.pair hasWon (.pair prin (.pair spks (.pair opks (.pair sess (.pair usedS
    (.pair usedO (.pair usedN (.pair kyb (.pair sOE (.pair sNE (.pair rOE (.pair rNE
      (.pair ro (.pair root adv)))))))))))))))

@[reducible] def stUpd {Γ} (e : Expr pqxdhOps Γ authStateTy)
    (secb : Expr pqxdhOps Γ .bool := asSecb e)
    (hasWon : Expr pqxdhOps Γ .bool := asHasWonAuth e)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) := asPrincipals e)
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) := asSpkBundles e)
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) :=
      asOpkEntries e)
    (sess : Expr pqxdhOps Γ (.list authSessionEntryTy) := asSessions e)
    (usedS : Expr pqxdhOps Γ (.list sessionIdTy) := asUsedSendSessions e)
    (usedO : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := asUsedRecvOPK e)
    (usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := asUsedRecvNoOPK e)
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))) :=
      asUsedKyberTriples e)
    (sOE : Expr pqxdhOps Γ (.list sentOPKEventTy) := asSentOPKEvents e)
    (sNE : Expr pqxdhOps Γ (.list sentNoOPKEventTy) := asSentNoOPKEvents e)
    (rOE : Expr pqxdhOps Γ (.list recvdOPKEventTy) := asRecvdOPKEvents e)
    (rNE : Expr pqxdhOps Γ (.list recvdNoOPKEventTy) := asRecvdNoOPKEvents e)
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := asRoCache e)
    (root : Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))) :=
      asRootRoCache e)
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := asAdvKeys e) : Expr pqxdhOps Γ authStateTy :=
  stMk secb hasWon prin spks opks sess usedS usedO usedN kyb sOE sNE rOE rNE ro root adv

@[reducible] def ahsMk {Γ} (base : Expr pqxdhOps Γ authStateTy)
    (initR : Expr pqxdhOps Γ (.list initKemRecordTy))
    (recvR : Expr pqxdhOps Γ (.list recvKemRecordTy))
    (idealS : Expr pqxdhOps Γ (.list idealAuthSessionTy)) : Expr pqxdhOps Γ authHybridStateTy :=
  .pair base (.pair initR (.pair recvR idealS))

@[reducible] def ahsUpd {Γ} (e : Expr pqxdhOps Γ authHybridStateTy)
    (base : Expr pqxdhOps Γ authStateTy := ahsBase e)
    (initR : Expr pqxdhOps Γ (.list initKemRecordTy) := ahsInitKemRecs e)
    (recvR : Expr pqxdhOps Γ (.list recvKemRecordTy) := ahsRecvKemRecs e)
    (idealS : Expr pqxdhOps Γ (.list idealAuthSessionTy) := ahsIdealSessions e) :
    Expr pqxdhOps Γ authHybridStateTy :=
  ahsMk base initR recvR idealS

@[reducible] def ahsfMkSlots {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy)
    (rc : Expr pqxdhOps Γ .nat) (cache : Expr pqxdhOps Γ authMkSaltCacheTy)
    (slots : Expr pqxdhOps Γ authSlotStateTy) :
    Expr pqxdhOps Γ authHybridStateFixedTy :=
  .pair hst (.pair rc (.pair cache slots))

@[reducible] def ahsfMk {Γ} (hst : Expr pqxdhOps Γ authHybridStateTy) (rc : Expr pqxdhOps Γ .nat)
    (cache : Expr pqxdhOps Γ authMkSaltCacheTy) : Expr pqxdhOps Γ authHybridStateFixedTy :=
  ahsfMkSlots hst rc cache emptyAuthSlotStE

@[reducible] def ahsfUpdSlots {Γ} (e : Expr pqxdhOps Γ authHybridStateFixedTy)
    (hst : Expr pqxdhOps Γ authHybridStateTy := ahsfHybrid e)
    (rc : Expr pqxdhOps Γ .nat := ahsfRecvCount e)
    (cache : Expr pqxdhOps Γ authMkSaltCacheTy := ahsfMkSaltCache e)
    (slots : Expr pqxdhOps Γ authSlotStateTy := ahsfSlots e) :
    Expr pqxdhOps Γ authHybridStateFixedTy :=
  ahsfMkSlots hst rc cache slots

@[reducible] def ahsfUpd {Γ} (e : Expr pqxdhOps Γ authHybridStateFixedTy)
    (hst : Expr pqxdhOps Γ authHybridStateTy := ahsfHybrid e)
    (rc : Expr pqxdhOps Γ .nat := ahsfRecvCount e)
    (cache : Expr pqxdhOps Γ authMkSaltCacheTy := ahsfMkSaltCache e) :
    Expr pqxdhOps Γ authHybridStateFixedTy :=
  ahsfMkSlots hst rc cache (ahsfSlots e)

def emptyAuthStE {Γ} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ authStateTy :=
  stMk secb (.bool false) .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil

def emptyAuthHybridStE {Γ} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ authHybridStateTy :=
  ahsMk (emptyAuthStE secb) .nil .nil .nil

def emptyAuthHybridStFixedE {Γ} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ authHybridStateFixedTy :=
  ahsfMk (emptyAuthHybridStE secb) (.nat 0) .nil

def aNone {Γ : List PT} : Expr pqxdhOps Γ authRespTy := .inl .unit
def aInitPrin {Γ : List PT} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inl (.pair ik s))
def aPk {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inl pk))
def aCorr {Γ : List PT} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inl (.pair ik s))))
def aBundle {Γ : List PT} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inl b))))
def aSendFresh {Γ : List PT} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inl m)))))
def aSendUnfresh {Γ : List PT} (dk : Expr pqxdhOps Γ drKeyTy) (rk ck : Expr pqxdhOps Γ (B 32))
    (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk (.pair rk (.pair ck m)))))))))
def aRecvHonest {Γ : List PT} : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl .unit)))))))
def aRecvUnfresh {Γ : List PT} (dk : Expr pqxdhOps Γ drKeyTy) (rk ck pt : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk (.pair rk (.pair ck pt)))))))))))
def aDrKey {Γ : List PT} (dk : Expr pqxdhOps Γ drKeyTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk)))))))))
def aRootKdf {Γ : List PT} (rk ck : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair rk ck)))))))))))

abbrev sendQTy : PT :=
  .prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32))))
abbrev recvQTy : PT := .prod .nat (.prod .nat (.prod .nat preKeyMsgTy))
abbrev RSF : PT := .prod authRespTy authHybridStateFixedTy
abbrev RSH : PT := .prod authRespTy authHybridStateTy

def sendGuardE {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy) : Expr pqxdhOps Γ .bool :=
  if opk then .not (isSomeE (pkbOpkB? (.fst (.snd (.snd x)))))
  else isSomeE (pkbOpkB? (.fst (.snd (.snd x))))

/-! ## Finalization Predicates -/

@[reducible] def allHonestEcPksAuthDslK (S : Setup) (K : Nat) {Γ : List PT} :
    Comp pqxdhOps pqPrimIface (authStateTy :: Γ) (.list (B 32)) :=
  .bind
    (.mapM (min K S.N_dh) (asPrincipals (.var .zero))
      (queryPrim .pow8 (peIkAPk (.snd (.var .zero)))))
    (.bind
      (.mapM (min K S.N_dh) (asSpkBundles (.var (.succ .zero)))
        (queryPrim .pow8 (sbSpkPk (.snd (.var .zero)))))
      (.bind
        (.mapM (min K S.N_dh) (asOpkEntries (.var (.succ (.succ .zero))))
          (queryPrim .pow8 (oeOpkPk (.snd (.var .zero)))))
        (.bind
          (.mapM (min K S.N_dh) (asSessions (.var (.succ (.succ (.succ .zero)))))
            (.bind (queryPrim .x25519Base (aseEkASk (.var .zero)))
              (queryPrim .pow8 (.var .zero))))
          (.ret
            (.appendL (4 * min K S.N_dh)
              (.appendL (4 * min K S.N_dh)
                (.appendL (4 * min K S.N_dh)
                  (.var (.succ (.succ (.succ .zero))))
                  (.var (.succ (.succ .zero))))
                (.var (.succ .zero)))
              (.var .zero))))))

def allHonestEcPksAuthDsl (S : Setup) {Γ : List PT} :
    Comp pqxdhOps pqPrimIface (authStateTy :: Γ) (.list (B 32)) :=
  .bind
    (.mapM S.N_dh (asPrincipals (.var .zero))
      (queryPrim .pow8 (peIkAPk (.snd (.var .zero)))))
    (.bind
      (.mapM S.N_dh (asSpkBundles (.var (.succ .zero)))
        (queryPrim .pow8 (sbSpkPk (.snd (.var .zero)))))
      (.bind
        (.mapM S.N_dh (asOpkEntries (.var (.succ (.succ .zero))))
          (queryPrim .pow8 (oeOpkPk (.snd (.var .zero)))))
        (.bind
          (.mapM S.N_dh (asSessions (.var (.succ (.succ (.succ .zero)))))
            (.bind (queryPrim .x25519Base (aseEkASk (.var .zero)))
              (queryPrim .pow8 (.var .zero))))
          (.ret
            (.appendL (4 * S.N_dh)
              (.appendL (4 * S.N_dh)
                (.appendL (4 * S.N_dh)
                  (.var (.succ (.succ (.succ .zero))))
                  (.var (.succ (.succ .zero))))
                (.var (.succ .zero)))
              (.var .zero))))))

def hasDuplicateBytesDsl (w : ℕ+) (K : Nat) {Γ : List PT}
    (xs : Expr pqxdhOps Γ (.list (B w))) : Expr pqxdhOps Γ .bool :=
  .fst (.foldrB K xs (.pair (.bool false) .nil)
    (.pair
      (boolOr
        (.anyB K (.snd (.var (.succ .zero))) (bytesBeq w (.var (.succ .zero)) (.var .zero)))
        (.fst (.var (.succ .zero))))
      (.cons (.var .zero) (.snd (.var (.succ .zero))))))

def hasBadSigAuthDsl (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) : Expr pqxdhOps Γ .bool :=
  .anyB K (asSessions (ahsBase hst))
    (.and (aseFresh (.var .zero))
      (boolOr (.not (aseSpkHonest (.var .zero))) (.not (asePqspkHonest (.var .zero)))))

def hasKemPkCollisionAuthDsl (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) : Expr pqxdhOps Γ .bool :=
  hasDuplicateBytesDsl 1568 K
    (.mapB K (asSpkBundles (ahsBase hst)) (sbPqspkPk (.snd (.var .zero))))

def hasBadKemShCrRecordsDsl (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) : Expr pqxdhOps Γ .bool :=
  eLet hst fun h =>
    eAny K (ahsInitKemRecs (v h)) fun iRec =>
      eAny K (ahsRecvKemRecs (v h)) fun rRec =>
        .and
          (bytesBeq 32 (rkrKemSs (v rRec)) (ikrKemSs (v iRec)))
          (boolOr
            (.not (bytesBeq 1568 (rkrKemCt (v rRec)) (ikrKemCt (v iRec))))
            (.not (bytesBeq 1568 (ikrPqspkPk (v iRec)) (rkrPqspkPk (v rRec)))))

def notAllChallengedCleanDsl (K : Nat) {Γ : List PT}
    (st : Expr pqxdhOps Γ authStateTy) : Expr pqxdhOps Γ .bool :=
  .not
    (.not
      (.anyB K (asSessions st)
        (.not
          (boolOr (.not (aseChallenged (.var .zero)))
            (.and (aseFresh (.var .zero)) (asePqspkHonest (.var .zero)))))))

def finalizeAuthFixedBodyDsl (S : Setup) (K : Nat) {Γ : List PT} :
    Comp pqxdhOps pqPrimIface
      (.list (B 32) :: authStateTy :: authHybridStateTy :: .bool :: .bool :: Γ) .bool :=
  .ite
    (boolOr
      (boolOr
        (boolOr
          (hasDuplicateBytesDsl 32 (4 * min K S.N_dh) (.var .zero))
          (hasBadSigAuthDsl K (.var (.succ (.succ .zero)))))
        (hasKemPkCollisionAuthDsl K (.var (.succ (.succ .zero)))))
      (hasBadKemShCrRecordsDsl K (.var (.succ (.succ .zero)))))
    (samplePrim .bool)
    (.ite (asHasWonAuth (.var (.succ .zero)))
      (.ret (.bool true))
      (.ite (notAllChallengedCleanDsl K (.var (.succ .zero)))
        (samplePrim .bool)
        (.ret (boolBeq
          (.var (.succ (.succ (.succ .zero))))
          (.var (.succ (.succ (.succ (.succ .zero)))))))))

/-- Evaluates `finalizeAuthFixedPrim` in `ReductionDsl` with list bound `K`. -/
def finalizeAuthFixedDsl (S : Setup) (K : Nat) {Γ : List PT} :
    Comp pqxdhOps pqPrimIface (authHybridStateTy :: .bool :: .bool :: Γ) .bool :=
  Comp.letC (ahsBase (.var .zero))
    (.bind (allHonestEcPksAuthDslK S K)
      (finalizeAuthFixedBodyDsl S K))

/-! ## Shared `AuthHybridStateFixed` Step Helpers -/

section SharedAuthStepHelpers

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}

def findHonestC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod .nat principalEntryTy)) :=
  letV ik fun ik =>
    findMV (min K S.N_dh) (asPrincipals (v st)) fun e =>
      bindV (queryPrim .pow8 (v ik)) fun p1 =>
        bindV (queryPrim .pow8 (peIkAPk (.snd (v e)))) fun p2 =>
          .ret (bytesBeq 32 (v p1) (v p2))

def isAdvRegC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (queryPrim .pow8 pk) fun p =>
    .ret (eAny K (asAdvKeys (v st)) fun e => bytesBeq 32 (v p) (.fst (v e)))

def isGameSpkC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (asSpkBundles (v st)) fun e =>
      bindV (queryPrim .pow8 (sbSpkPk (.snd (v e)))) fun p1 =>
        bindV (queryPrim .pow8 (v pk)) fun p2 => .ret (bytesBeq 32 (v p1) (v p2))

def isGameOpkC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (asOpkEntries (v st)) fun e =>
      bindV (queryPrim .pow8 (oeOpkPk (.snd (v e)))) fun p1 =>
        bindV (queryPrim .pow8 (v pk)) fun p2 => .ret (bytesBeq 32 (v p1) (v p2))

def koskBundleOkC (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (findHonestC S K st (pkbIkB (v bu))) fun f =>
  bindV (isAdvRegC K st (pkbIkB (v bu))) fun idA =>
  bindV (isGameSpkC S K st (pkbSpkB (v bu))) fun spkG =>
  bindV (isAdvRegC K st (pkbSpkB (v bu))) fun spkA =>
  caseOptV (pkbOpkB? (v bu))
    (.ret (.and (.and (boolOr (isSomeE (v f)) (v idA)) (boolOr (v spkG) (v spkA)))
      (.bool true)))
    fun o =>
      bindV (isGameOpkC S K st (.snd (v o))) fun opkG =>
      bindV (isAdvRegC K st (.snd (v o))) fun opkA =>
      .ret (.and (.and (boolOr (isSomeE (v f)) (v idA)) (boolOr (v spkG) (v spkA)))
        (boolOr (v opkG) (v opkA)))

def koskSenderOkC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  bindV (isAdvRegC K st (v ik)) fun idA =>
  .ret (boolOr (isSomeE (v f)) (v idA))

def resolveSigPkC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (B 32) :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  .ret (eCaseOpt (v f) (v ik) fun e => peIkSignPk (.snd (v e)))

def hkdfRoC (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    Comp pqxdhOps pqPrimIface Δ (.prod drKeyTy (.list (.prod (B 192) drKeyTy))) :=
  letV sec fun sec =>
  caseOptV (eFind K (asRoCache (v st)) fun e => bytesBeq 192 (.fst (v e)) (v sec))
    (bindV (samplePrim .drKey96) fun dk =>
      .ret (.pair (v dk) (.cons (.pair (v sec) (v dk)) (asRoCache (v st)))))
    fun e => .ret (.pair (.snd (v e)) (asRoCache (v st)))

def rootRoC (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ
      (.prod (.prod (B 32) (B 32)) (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))) :=
  letV (.pair rk dh) fun inp =>
  caseOptV (eFind K (asRootRoCache (v st)) fun e => bytes2Eq (.fst (v e)) (v inp))
    (bindV (samplePrim .bytes32) fun rk1 => bindV (samplePrim .bytes32) fun ck1 =>
      .ret (.pair (.pair (v rk1) (v ck1)) (.cons (.pair (v inp) (.pair (v rk1) (v ck1)))
        (asRootRoCache (v st)))))
    fun e => .ret (.pair (.snd (v e)) (asRootRoCache (v st)))

def checkBundleProvenanceExactC (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.prod .bool (.prod .bool .bool)) :=
  bindV (findHonestC S K st (pkbIkB (v bu))) fun f =>
  caseOptV (v f) (.ret (.pair (.bool false) (.pair (.bool false) (.bool false)))) fun p =>
  letV (.fst (v p)) fun k =>
  letV (eAny K (asSpkBundles (v st)) fun b =>
    .and (natEq (.fst (.fst (v b))) (v k))
      (bytesBeq 32 (sbSpkPk (.snd (v b))) (pkbSpkB (v bu)))) fun spkH =>
  letV (eAny K (asSpkBundles (v st)) fun b =>
    .and (natEq (.fst (.fst (v b))) (v k))
      (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkH =>
  bindV (caseOptV (pkbOpkB? (v bu)) (.ret (.bool false)) fun o =>
    anyMV (min K S.N_dh) (asOpkEntries (v st)) fun e =>
      bindV (queryPrim .pow8 (oeOpkPk (.snd (v e)))) fun p1 =>
      bindV (queryPrim .pow8 (.snd (v o))) fun p2 =>
      .ret (.and (natEq (.fst (.fst (v e))) (v k)) (bytesBeq 32 (v p1) (v p2)))) fun opkH =>
  .ret (.pair (v spkH) (.pair (v opkH) (v pqspkH)))

def checkBundleSpkHonIdealC (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (findHonestC S K st (pkbIkB (v bu))) fun f =>
  caseOptV (v f) (.ret (.bool false)) fun p =>
  letV (.fst (v p)) fun k =>
  letV (.snd (v p)) fun pE =>
  anyMV (min K S.N_dh) (asSpkBundles (v st)) fun b =>
    bindV (queryPrim .pow8 (sbSpkPk (.snd (v b)))) fun p1 =>
    bindV (queryPrim .pow8 (pkbSpkB (v bu))) fun p2 =>
    .ret (.and (natEq (.fst (.fst (v b))) (v k))
      (boolOr
        (.and (peCorrupted (v pE)) (bytesBeq 32 (v p1) (v p2)))
        (bytesBeq 32 (sbSpkPk (.snd (v b))) (pkbSpkB (v bu)))))

def matchSentOPKC (r : Var Γ₁ recvdOPKEventTy) (s : Var Γ₂ sentOPKEventTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (queryPrim .pow8 (roA0 (v r))) fun pa0r =>
  bindV (queryPrim .pow8 (soA0 (v s))) fun pa0s =>
  bindV (queryPrim .pow8 (roB0 (v r))) fun pb0r =>
  bindV (queryPrim .pow8 (soB0 (v s))) fun pb0s =>
  bindV (queryPrim .pow8 (roOb (v r))) fun pobr =>
  bindV (queryPrim .pow8 (soOb (v s))) fun pobs =>
  bindV (queryPrim .pow8 (roA1 (v r))) fun pa1r =>
  bindV (queryPrim .pow8 (soA1 (v s))) fun pa1s =>
  bindV (queryPrim .pow8 (roSb (v r))) fun psbr =>
  bindV (queryPrim .pow8 (soSb (v s))) fun psbs =>
  .ret (.and
    (.and
      (.and
        (.and
          (.and
            (.and
              (.and
                (.and
                  (.and
                    (.not (soMatched (v s)))
                    (bytesBeq 32 (v pa0r) (v pa0s)))
                  (bytesBeq 32 (v pb0r) (v pb0s)))
                (bytesBeq 32 (v pobr) (v pobs)))
              (bytesBeq 32 (v pa1r) (v pa1s)))
            (bytesBeq 32 (v psbr) (v psbs)))
          (boolOr (roBCorr (v r)) (bytesBeq 32 (roSb (v r)) (soSb (v s)))))
        (bytesBeq 1568 (roPk1 (v r)) (soPk1 (v s))))
      (bytesBeq 1568 (roCt (v r)) (soCt (v s))))
    (bytesBeq 32 (roM (v r)) (soM (v s))))

def matchSentNoOPKC (r : Var Γ₁ recvdNoOPKEventTy) (s : Var Γ₂ sentNoOPKEventTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (queryPrim .pow8 (rnoA0 (v r))) fun pa0r =>
  bindV (queryPrim .pow8 (snoA0 (v s))) fun pa0s =>
  bindV (queryPrim .pow8 (rnoB0 (v r))) fun pb0r =>
  bindV (queryPrim .pow8 (snoB0 (v s))) fun pb0s =>
  bindV (queryPrim .pow8 (rnoA1 (v r))) fun pa1r =>
  bindV (queryPrim .pow8 (snoA1 (v s))) fun pa1s =>
  bindV (queryPrim .pow8 (rnoSb (v r))) fun psbr =>
  bindV (queryPrim .pow8 (snoSb (v s))) fun psbs =>
  .ret (.and
    (.and
      (.and
        (.and
          (.and
            (.and
              (.and
                (.and
                  (.not (snoMatched (v s)))
                  (bytesBeq 32 (v pa0r) (v pa0s)))
                (bytesBeq 32 (v pb0r) (v pb0s)))
              (bytesBeq 32 (v pa1r) (v pa1s)))
            (bytesBeq 32 (v psbr) (v psbs)))
          (boolOr (rnoBCorr (v r)) (bytesBeq 32 (rnoSb (v r)) (snoSb (v s)))))
        (bytesBeq 1568 (rnoPk1 (v r)) (snoPk1 (v s))))
      (bytesBeq 1568 (rnoCt (v r)) (snoCt (v s))))
    (bytesBeq 32 (rnoM (v r)) (snoM (v s))))

def matchIdealAuthHandshakeC {Γ₆ : List PT}
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (queryPrim .pow8 (hdrIkAPk (v hdr))) fun pIk1 =>
  bindV (queryPrim .pow8 (iasIkAPk (v s))) fun pIk2 =>
  bindV (queryPrim .pow8 (v ikB)) fun pPeerIk1 =>
  bindV (queryPrim .pow8 (iasPeerIkPk (v s))) fun pPeerIk2 =>
  bindV (queryPrim .pow8 (v spkB)) fun pSpk1 =>
  bindV (queryPrim .pow8 (iasPeerSpkPk (v s))) fun pSpk2 =>
  bindV (caseOptV (v opkB?)
    (caseOptV (iasPeerOpkPk? (v s)) (.ret (.bool true)) fun _ => .ret (.bool false))
    fun pk1 => caseOptV (iasPeerOpkPk? (v s)) (.ret (.bool false)) fun pk2 =>
      bindV (queryPrim .pow8 (v pk1)) fun q1 =>
      bindV (queryPrim .pow8 (v pk2)) fun q2 =>
      .ret (bytesBeq 32 (v q1) (v q2))) fun opkOk =>
  bindV (queryPrim .pow8 (hdrEkAPk (v hdr))) fun pEk1 =>
  bindV (queryPrim .pow8 (iasEkAPk (v s))) fun pEk2 =>
  .ret (.and
    (.and
      (.and
        (.and
          (.and
            (.and
              (bytesBeq 32 (v pIk1) (v pIk2))
              (bytesBeq 32 (v pPeerIk1) (v pPeerIk2)))
            (bytesBeq 32 (v pSpk1) (v pSpk2)))
          (v opkOk))
        (bytesBeq 32 (v pEk1) (v pEk2)))
      (bytesBeq 1568 (v pqspkB) (iasPeerPqspkPk (v s))))
    (bytesBeq 1568 (hdrKemCt (v hdr)) (iasKemCt (v s))))

abbrev kyberTripleListTy : PT :=
  .list (.prod .nat (.prod U32 (.prod U32 (B 32))))
abbrev recvFinishOpkTagTy : PT :=
  .prod (.prod .nat (.prod .nat .nat))
    (.prod principalEntryTy (.prod spkBundleEntryTy
      (.prod opkEntryTy (.prod kyberTripleListTy (.prod preKeyMsgTy authHybridStateTy)))))
abbrev recvFinishNoOpkTagTy : PT :=
  .prod (.prod .nat (.prod .nat .nat))
    (.prod principalEntryTy (.prod spkBundleEntryTy
      (.prod kyberTripleListTy (.prod preKeyMsgTy authHybridStateTy))))
abbrev recvFinishTagTy : PT := .sum recvFinishOpkTagTy recvFinishNoOpkTagTy
abbrev recvFinishResTy : PT :=
  .opt (.prod drKeyTy (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (.list (.prod (B 192) drKeyTy))
      (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))))))))

def recvFinishTagRunC (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy)
    [Ext Γ₁ Δ] : Comp pqxdhOps pqPrimIface Δ RSH :=
  letV res? fun res? =>
  caseSumV (v tag)
    (fun opkT =>
      letV (.fst (v opkT)) fun kjo =>
      letV (.fst (.snd (v opkT))) fun kE =>
      letV (.fst (.snd (.snd (v opkT)))) fun bE =>
      letV (.fst (.snd (.snd (.snd (v opkT))))) fun oE =>
      letV (.fst (.snd (.snd (.snd (.snd (v opkT)))))) fun usedT =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (v opkT))))))) fun msg =>
      letV (.snd (.snd (.snd (.snd (.snd (.snd (v opkT))))))) fun hstDec =>
      letV (ahsBase (v hstDec)) fun st =>
      caseOptV (v res?) (.ret (.pair aNone (v hstDec))) fun res =>
      letV (.fst (v res)) fun drKey =>
      letV (.fst (.snd (v res))) fun rk1 =>
      letV (.fst (.snd (.snd (v res)))) fun ck11 =>
      letV (.fst (.snd (.snd (.snd (v res))))) fun pt =>
      letV (.fst (.snd (.snd (.snd (.snd (v res)))))) fun roC =>
      letV (.snd (.snd (.snd (.snd (.snd (v res)))))) fun rootC =>
      letV (eMap K (asOpkEntries (v st)) fun e =>
        .ite (nat3Eq (.fst (v e)) (v kjo))
          (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e)) fun opks' =>
      bindV (findHonestC S K st (hdrIkAPk (pkmHdr (v msg)))) fun snd? =>
      caseOptV (v snd?)
        (.ret (.pair (aRecvUnfresh (v drKey) (v rk1) (v ck11) (v pt))
          (ahsUpd (v hstDec) (base := stUpd (v st) (opks := v opks')
            (usedO := .cons (v kjo) (asUsedRecvOPK (v st)))
            (kyb := v usedT) (ro := v roC) (root := v rootC)))))
        fun sndP =>
          .ite (.not (peCorrupted (.snd (v sndP))))
            (letV (roMk (peCorrupted (v kE)) (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (v kE))
                (sbSpkPk (v bE)) (oeOpkPk (v oE)) (hdrEkAPk (pkmHdr (v msg)))
                (sbPqspkPk (v bE)) (hdrKemCt (pkmHdr (v msg))) (v pt)) fun recvEv =>
             bindV (consumeFirstMV (min K S.N_dh) (asSentOPKEvents (v st))
               (fun s => matchSentOPKC recvEv s) (fun s => soMarkMatched (v s))) fun mOut =>
             letV (boolOr (asHasWonAuth (v st)) (.not (.fst (v mOut)))) fun won' =>
             .ret (.pair aRecvHonest (ahsUpd (v hstDec) (base := stUpd (v st)
               (hasWon := v won') (opks := v opks')
               (usedO := .cons (v kjo) (asUsedRecvOPK (v st)))
               (kyb := v usedT) (sOE := .snd (v mOut))
               (rOE := .cons (v recvEv) (asRecvdOPKEvents (v st)))
               (ro := v roC) (root := v rootC)))))
            (.ret (.pair aRecvHonest (ahsUpd (v hstDec) (base := stUpd (v st)
              (opks := v opks') (usedO := .cons (v kjo) (asUsedRecvOPK (v st)))
              (kyb := v usedT) (ro := v roC) (root := v rootC))))))
    (fun noOpkT =>
      letV (.fst (v noOpkT)) fun kjl =>
      letV (.fst (.snd (v noOpkT))) fun kE =>
      letV (.fst (.snd (.snd (v noOpkT)))) fun bE =>
      letV (.fst (.snd (.snd (.snd (v noOpkT))))) fun usedT =>
      letV (.fst (.snd (.snd (.snd (.snd (v noOpkT)))))) fun msg =>
      letV (.snd (.snd (.snd (.snd (.snd (v noOpkT)))))) fun hstDec =>
      letV (ahsBase (v hstDec)) fun st =>
      caseOptV (v res?) (.ret (.pair aNone (v hstDec))) fun res =>
      letV (.fst (v res)) fun drKey =>
      letV (.fst (.snd (v res))) fun rk1 =>
      letV (.fst (.snd (.snd (v res)))) fun ck11 =>
      letV (.fst (.snd (.snd (.snd (v res))))) fun pt =>
      letV (.fst (.snd (.snd (.snd (.snd (v res)))))) fun roC =>
      letV (.snd (.snd (.snd (.snd (.snd (v res)))))) fun rootC =>
      bindV (findHonestC S K st (hdrIkAPk (pkmHdr (v msg)))) fun snd? =>
      caseOptV (v snd?)
        (.ret (.pair (aRecvUnfresh (v drKey) (v rk1) (v ck11) (v pt))
          (ahsUpd (v hstDec) (base := stUpd (v st)
            (usedN := .cons (v kjl) (asUsedRecvNoOPK (v st)))
            (kyb := v usedT) (ro := v roC) (root := v rootC)))))
        fun sndP =>
          .ite (.not (peCorrupted (.snd (v sndP))))
            (letV (rnoMk (peCorrupted (v kE)) (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (v kE))
                (sbSpkPk (v bE)) (hdrEkAPk (pkmHdr (v msg)))
                (sbPqspkPk (v bE)) (hdrKemCt (pkmHdr (v msg))) (v pt)) fun recvEv =>
             bindV (consumeFirstMV (min K S.N_dh) (asSentNoOPKEvents (v st))
               (fun s => matchSentNoOPKC recvEv s) (fun s => snoMarkMatched (v s))) fun mOut =>
             letV (boolOr (asHasWonAuth (v st)) (.not (.fst (v mOut)))) fun won' =>
             .ret (.pair aRecvHonest (ahsUpd (v hstDec) (base := stUpd (v st)
               (hasWon := v won')
               (usedN := .cons (v kjl) (asUsedRecvNoOPK (v st)))
               (kyb := v usedT) (sNE := .snd (v mOut))
               (rNE := .cons (v recvEv) (asRecvdNoOPKEvents (v st)))
               (ro := v roC) (root := v rootC)))))
            (.ret (.pair aRecvHonest (ahsUpd (v hstDec) (base := stUpd (v st)
              (usedN := .cons (v kjl) (asUsedRecvNoOPK (v st)))
              (kyb := v usedT) (ro := v roC) (root := v rootC))))))

abbrev preparedAuthRecvTy : PT :=
  .prod principalEntryTy (.prod spkBundleEntryTy (.prod (.opt (B 32))
    (.prod (B 192) (.prod (B 32) (.prod .bool
      (.prod (.opt idealAuthSessionTy) (.prod .bool
        (.prod authHybridStateTy recvFinishTagTy))))))))

@[reducible] def parKEntry {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ principalEntryTy := .fst p
@[reducible] def parSecrets {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ (B 192) := .fst (.snd (.snd (.snd p)))
@[reducible] def parDhRatchet {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd (.snd p))))
@[reducible] def parIsUncorrSender {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd p)))))
@[reducible] def parMatchedSess? {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ (.opt idealAuthSessionTy) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
@[reducible] def parSameEph {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
@[reducible] def parHstDec {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ authHybridStateTy := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))
@[reducible] def parFinishTag {Γ} (p : Expr pqxdhOps Γ preparedAuthRecvTy) :
    Expr pqxdhOps Γ recvFinishTagTy := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))

def prepareAuthHybridRecvC (opk : Bool) (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy) :=
  letV (ahsBase (v hst)) fun st =>
  .ite (asHasWonAuth (v st)) (.ret .none) <|
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pkmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .ite (.not (.and (.and (.and (.and (.and
      (u32Beq (hdrSpkId (v hdr)) (u32OfNat (.fst (.snd (v x)))))
      (u32Beq (hdrPqspkId (v hdr)) (u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdrOpkId? (v hdr))
        (if opk then .some (u32OfNat (.fst (.snd (.snd (v x))))) else .none)))
      (natEq (bytesLen 32 (hdrIkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (hdrEkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (pkmEphAPk (v msg))) (.nat 32))))
    (.ret .none) <|
  .ite (eAny K (if opk then asUsedRecvOPK (v st) else asUsedRecvNoOPK (v st))
      fun e => nat3Eq (v e) (v kjo))
    (.ret .none) <|
  bindV (koskSenderOkC S K st (hdrIkAPk (v hdr))) fun koskOk =>
  .ite (.not (v koskOk)) (.ret .none) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret .none) fun kPair =>
  caseOptV (eFind K (asSpkBundles (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret .none) fun bPair =>
  letV (.snd (v kPair)) fun kE =>
  letV (.snd (v bPair)) fun bE =>
  letV (kyberCheckE K (asUsedKyberTriples (v st)) (.pair (.fst (v x)) (.pair (hdrPqspkId (v hdr))
      (.pair (hdrSpkId (v hdr)) (hdrEkAPk (v hdr)))))) fun kc =>
  if opk then
    caseOptV (eFind K (asOpkEntries (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
      (.ret .none) fun oPair =>
    letV (.snd (v oPair)) fun oE =>
    .ite (oeConsumed (v oE)) (.ret .none) <|
    bindV (queryPrim .isCanonical (hdrEkAPk (v hdr))) fun can =>
    bindV (queryPrim .isCanonical (pkmEphAPk (v msg))) fun canE =>
    .ite (boolOr (boolOr (.not (.fst (v kc))) (.not (v can))) (.not (v canE)))
      (.ret .none) <|
    bindV (queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdrKemCt (v hdr)))) fun ss? =>
    caseOptV (v ss?) (.ret .none) fun ss =>
    letV (rkrMk (.fst (v x)) (.fst (.snd (v x))) (sbPqspkPk (v bE)) (sbPqspkSk (v bE))
        (hdrKemCt (v hdr)) (v ss)) fun rRec =>
    letV (ahsUpd (v hst) (recvR := .cons (v rRec) (ahsRecvKemRecs (v hst)))) fun hstDec =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrIkAPk (v hdr)))) fun dh1 =>
    bindV (queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdrEkAPk (v hdr)))) fun dh2 =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrEkAPk (v hdr)))) fun dh3 =>
    bindV (queryPrim .x25519 (.pair (oeOpkSk (v oE)) (hdrEkAPk (v hdr)))) fun dh4 =>
    letV (buildSecretsE (v dh1) (v dh2) (v dh3) (.some (v dh4)) (v ss)) fun secrets =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
    bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd? =>
    letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
      fun isUncorr =>
    letV (peIkAPk (v kE)) fun ikBPk =>
    letV (sbSpkPk (v bE)) fun spkBPk =>
    letV (.some (oeOpkPk (v oE)) : Expr pqxdhOps _ (.opt (B 32))) fun opkBPk? =>
    letV (sbPqspkPk (v bE)) fun pqspkBPk =>
    bindV (findMV (min K S.N_dh) (ahsIdealSessions (v hstDec)) fun s =>
        matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
    bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
        bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
        bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
        .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
    letV (.inl (.pair (v kjo) (.pair (v kE) (.pair (v bE) (.pair (v oE)
        (.pair (.snd (v kc)) (.pair (v msg) (v hstDec))))))) : Expr pqxdhOps _ recvFinishTagTy)
      fun fTag =>
    .ret (.some (.pair (v kE) (.pair (v bE) (.pair (v opkBPk?)
      (.pair (v secrets) (.pair (v dhR) (.pair (v isUncorr)
        (.pair (v matched?) (.pair (v sameEph) (.pair (v hstDec) (v fTag)))))))))))
  else
    bindV (queryPrim .isCanonical (hdrEkAPk (v hdr))) fun can =>
    bindV (queryPrim .isCanonical (pkmEphAPk (v msg))) fun canE =>
    .ite (boolOr (boolOr (.not (.fst (v kc))) (.not (v can))) (.not (v canE)))
      (.ret .none) <|
    bindV (queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdrKemCt (v hdr)))) fun ss? =>
    caseOptV (v ss?) (.ret .none) fun ss =>
    letV (rkrMk (.fst (v x)) (.fst (.snd (v x))) (sbPqspkPk (v bE)) (sbPqspkSk (v bE))
        (hdrKemCt (v hdr)) (v ss)) fun rRec =>
    letV (ahsUpd (v hst) (recvR := .cons (v rRec) (ahsRecvKemRecs (v hst)))) fun hstDec =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrIkAPk (v hdr)))) fun dh1 =>
    bindV (queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdrEkAPk (v hdr)))) fun dh2 =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrEkAPk (v hdr)))) fun dh3 =>
    letV (buildSecretsE (v dh1) (v dh2) (v dh3) .none (v ss)) fun secrets =>
    bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
    bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd? =>
    letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
      fun isUncorr =>
    letV (peIkAPk (v kE)) fun ikBPk =>
    letV (sbSpkPk (v bE)) fun spkBPk =>
    letV (.none : Expr pqxdhOps _ (.opt (B 32))) fun opkBPk? =>
    letV (sbPqspkPk (v bE)) fun pqspkBPk =>
    bindV (findMV (min K S.N_dh) (ahsIdealSessions (v hstDec)) fun s =>
        matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
    bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
        bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
        bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
        .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
    letV (.inr (.pair (v kjo) (.pair (v kE) (.pair (v bE)
        (.pair (.snd (v kc)) (.pair (v msg) (v hstDec)))))) : Expr pqxdhOps _ recvFinishTagTy)
      fun fTag =>
    .ret (.some (.pair (v kE) (.pair (v bE) (.pair (v opkBPk?)
      (.pair (v secrets) (.pair (v dhR) (.pair (v isUncorr)
        (.pair (v matched?) (.pair (v sameEph) (.pair (v hstDec) (v fTag)))))))))))

abbrev keys6Ty : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 1568) (.prod (B 32) (B 32)))))

abbrev finishSendArgsTy : PT :=
  .prod sessionIdTy (.prod principalEntryTy (.prod (.opt (.prod .nat principalEntryTy))
    (.prod .bool (.prod preKeyBundleTy (.prod (.prod (B 32) (B 32))
      (.prod keys6Ty
        (.prod drKeyTy (.prod (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))
          (.prod (.opt (B 32)) (.prod (B 32) (.prod msgKeysTy
            (.prod (B 158) (.prod (B 32) (.prod (B 32)
              (.prod (.list (.prod (B 192) drKeyTy))
                (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))))))))))))))))))

def finishAuthHybridSendC (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy)
    [Ext Γ₁ Δ] : Comp pqxdhOps pqPrimIface Δ RSH :=
  letV args fun a =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (v a)) fun sid =>
  letV (.fst (.snd (v a))) fun uE =>
  letV (.fst (.snd (.snd (v a)))) fun pp =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun isFresh =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun bu =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v a))))))) fun m01 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))) fun keys6 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))) fun drKey =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))))) fun rks4 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))) fun spqrSalt? =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (v a)))))))))))) fun pqMsg =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (v a))))))))))))) fun mks =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))))))))) fun ad =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))))))) fun aeadCt =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))))))))))) fun msgPlain =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))))))))) fun roC =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))))))))) fun rootC =>
  letV (.fst (v keys6)) fun ekASk =>
  letV (.fst (.snd (v keys6))) fun ekAPk =>
  letV (.fst (.snd (.snd (v keys6)))) fun ss =>
  letV (.fst (.snd (.snd (.snd (v keys6))))) fun kemCt =>
  letV (.fst (.snd (.snd (.snd (.snd (v keys6)))))) fun ephASk =>
  letV (.snd (.snd (.snd (.snd (.snd (v keys6)))))) fun ephAPk =>
  letV (.fst (v rks4)) fun rk1 =>
  letV (.fst (.snd (v rks4))) fun ck1_0 =>
  letV (.fst (.snd (.snd (v rks4)))) fun mkSeed =>
  letV (.snd (.snd (.snd (v rks4)))) fun ck1_1 =>
  letV (hdMk (peIkAPk (v uE)) (v ekAPk) (pkbSpkId (v bu)) (optFst (pkbOpkB? (v bu)))
      (pkbPqspkId (v bu)) (v kemCt)) fun hdr =>
  letV (pmMk (v hdr) (v ephAPk) (v pqMsg) (v aeadCt)) fun wireMsg =>
  bindV (checkBundleProvenanceExactC S K st bu) fun prov =>
  bindV (checkBundleSpkHonIdealC S K st bu) fun spkHonIdeal =>
  letV (.fst (v prov)) fun spkHon =>
  letV (.fst (.snd (v prov))) fun opkHon =>
  letV (.snd (.snd (v prov))) fun pqspkHon =>
  letV (seMk (v sid) (pkbIkB (v bu)) (pkbSpkB (v bu)) (optSnd (pkbOpkB? (v bu)))
      (pkbPqspkB (v bu)) (v spkHon) (v opkHon) (v pqspkHon) (v ekASk) (v ephASk)
      (v isFresh) (.and (v isFresh) (.not (bytesBeq 32 (.fst (v m01)) (.snd (v m01))))))
    fun sessE =>
  letV (eCaseOpt (v pp) (.pair (asSentOPKEvents (v st)) (asSentNoOPKEvents (v st))) fun pP =>
      eCaseOpt (pkbOpkB? (v bu))
        (.pair (asSentOPKEvents (v st))
          (.cons (snoMk (peIkAPk (v uE)) (peIkAPk (.snd (v pP))) (pkbSpkB (v bu))
            (v ekAPk) (pkbPqspkB (v bu)) (v kemCt) (v msgPlain) (.bool false))
            (asSentNoOPKEvents (v st))))
        fun oP =>
          .pair
            (.cons (soMk (peIkAPk (v uE)) (peIkAPk (.snd (v pP))) (pkbSpkB (v bu))
              (.snd (v oP)) (v ekAPk) (pkbPqspkB (v bu)) (v kemCt) (v msgPlain) (.bool false))
              (asSentOPKEvents (v st)))
            (asSentNoOPKEvents (v st))) fun sentEvs =>
  letV (ikrMk (v sid) (pkbPqspkB (v bu)) (v kemCt) (v ss)) fun initRec =>
  letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
    fun isIdealSend =>
  letV (.ite (v isIdealSend)
      (.cons (iasMk (v sid) (peIkAPk (v uE)) (pkbIkB (v bu)) (pkbSpkB (v bu))
        (optSnd (pkbOpkB? (v bu))) (v ekAPk) (pkbPqspkB (v bu)) (v kemCt) (v ephAPk)
        (v spqrSalt?) (v pqMsg) (v ad) (v aeadCt) (v msgPlain) (v drKey)
        (v rk1) (v ck1_0) (v mkSeed) (v ck1_1) (v mks)) (ahsIdealSessions (v hst)))
      (ahsIdealSessions (v hst))) fun idealS' =>
  letV (ahsUpd (v hst)
      (base := stUpd (v st)
        (sess := .cons (v sessE) (asSessions (v st)))
        (usedS := .cons (v sid) (asUsedSendSessions (v st)))
        (sOE := .fst (v sentEvs)) (sNE := .snd (v sentEvs))
        (ro := v roC) (root := v rootC))
      (initR := .cons (v initRec) (ahsInitKemRecs (v hst)))
      (idealS := v idealS')) fun hst' =>
  letV (.ite (isSomeE (v pp)) (aSendFresh (v wireMsg))
      (aSendUnfresh (v drKey) (v rk1) (v ck1_1) (v wireMsg))) fun resp =>
  .ret (.pair (v resp) (v hst'))

def fhstSetBase {Γ} (fhst : Expr pqxdhOps Γ authHybridStateFixedTy) (base' : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ authHybridStateFixedTy :=
  ahsfUpd fhst (hst := ahsUpd (ahsfHybrid fhst) (base := base'))

def initPrinFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  .ite (eAny K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair aNone (v fhst))) <|
  bindV (samplePrim .bytes32) fun s0 => bindV (queryPrim .x25519Base (v s0)) fun ik =>
  bindV (samplePrim .bytes32) fun s1 => bindV (queryPrim .sigPkGen (v s1)) fun sp =>
  .ret (.pair (aInitPrin (v ik) (v sp))
    (fhstSetBase (v fhst) (stUpd (v st) (prin := .cons
      (.pair (v u) (peMk (v s0) (v ik) (v s1) (v sp) (.bool false))) (asPrincipals (v st))))))

def corruptFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair aNone (v fhst))) fun e =>
  .ret (.pair (aCorr (peSecIKA0 (.snd (v e))) (peSecIKAsign (.snd (v e))))
    (fhstSetBase (v fhst) (stUpd (v st) (prin := eMap K (asPrincipals (v st)) fun x =>
      .ite (natEq (.fst (v x)) (v u))
        (.pair (.fst (v x)) (peUpd (.snd (v x)) (corrupted := .bool true))) (v x)))))

def genSpkFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  .ite (eAny K (asSpkBundles (v st)) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair aNone (v fhst))) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v fhst))) fun uE =>
  bindV (samplePrim .bytes32) fun spkSk =>
  bindV (queryPrim .x25519Base (v spkSk)) fun spkPk =>
  bindV (samplePrim .random64) fun r1 =>
  bindV (queryPrim (.sigSign 33)
    (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1)))) fun sig1 =>
  bindV (samplePrim .random64) fun seed =>
  bindV (queryPrim .kemKeyGen (v seed)) fun kp =>
  bindV (samplePrim .random64) fun r2 =>
  bindV (queryPrim (.sigSign 1569) (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (.pair
    (aBundle (buMk (peIkAPk (.snd (v uE))) (u32OfNat (.snd (v x))) (v spkPk) (v sig1) .none
      (u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (fhstSetBase (v fhst) (stUpd (v st) (spks := .cons (.pair (v x)
      (sbMk (v spkSk) (v spkPk) (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.bool false)))
      (asSpkBundles (v st))))))

def genOpkFixedB (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  .ite (eAny K (asOpkEntries (v st)) fun e => nat3Eq (.fst (v e)) (v x))
    (.ret (.pair aNone (v fhst))) <|
  bindV (samplePrim .bytes32) fun sk => bindV (queryPrim .x25519Base (v sk)) fun pk =>
  .ret (.pair (aPk (v pk))
    (fhstSetBase (v fhst) (stUpd (v st) (opks := .cons
      (.pair (v x) (oeMk (v sk) (v pk) (.bool false))) (asOpkEntries (v st))))))

def roFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  bindV (hkdfRoC K st (v sec)) fun r =>
  .ret (.pair (aDrKey (.fst (v r))) (fhstSetBase (v fhst) (stUpd (v st) (ro := .snd (v r)))))

def roRootFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod (B 32) (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  bindV (rootRoC K st (.fst (v x)) (.snd (v x))) fun r =>
  .ret (.pair (aRootKdf (.fst (.fst (v r))) (.snd (.fst (v r))))
    (fhstSetBase (v fhst) (stUpd (v st) (root := .snd (v r)))))

def registerFixedB (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsBase (ahsfHybrid (v fhst))) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (.pair aNone (v fhst))) <|
  .ite (.not (natEq (bytesLen 32 (v sk)) (.nat 32))) (.ret (.pair aNone (v fhst))) <|
  bindV (queryPrim .x25519Base (v sk)) fun pk =>
  bindV (queryPrim .pow8 (v pk)) fun p8 =>
  .ret (.pair (aPk (v pk))
    (fhstSetBase (v fhst) (stUpd (v st) (adv := .cons (.pair (v p8) (v pk)) (asAdvKeys (v st))))))

end SharedAuthStepHelpers

/-! ## `PrfChainKey` Reduction Program -/

/-- State `(secb, (idx, ((mkSeedChal, ck1_1Chal), fhst)))` of `prfCkRedProg`. -/
abbrev prfCkStTy : PT :=
  .prod .bool (.prod .nat (.prod (.prod (B 32) (B 32)) authHybridStateFixedTy))

@[reducible] def ckSecb {Γ} (s : Expr pqxdhOps Γ prfCkStTy) : Expr pqxdhOps Γ .bool := .fst s
@[reducible] def ckIdx {Γ} (s : Expr pqxdhOps Γ prfCkStTy) : Expr pqxdhOps Γ .nat := .fst (.snd s)
@[reducible] def ckChal {Γ} (s : Expr pqxdhOps Γ prfCkStTy) : Expr pqxdhOps Γ (.prod (B 32) (B 32)) :=
  .fst (.snd (.snd s))
@[reducible] def ckFhst {Γ} (s : Expr pqxdhOps Γ prfCkStTy) : Expr pqxdhOps Γ authHybridStateFixedTy :=
  .snd (.snd (.snd s))

section PrfCkBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

def sampCkPairC (ideal : Expr pqxdhOps Δ .bool) : Comp pqxdhOps pqPrimIface Δ (.prod (B 32) (B 32)) :=
  letV ideal fun ideal =>
  bindV (samplePrim .bytes32) fun ck =>
  .ite (v ideal)
    (bindV (samplePrim .bytes32) fun r1 =>
     bindV (samplePrim .bytes32) fun r2 => .ret (.pair (v r1) (v r2)))
    (bindV (queryPrim .chainKdfSeed (v ck)) fun m =>
     bindV (queryPrim .chainKdfNext (v ck)) fun c => .ret (.pair (v m) (v c)))

def sampAtCkC (idx : Expr pqxdhOps Δ .nat) (chalP : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (s : Expr pqxdhOps Δ .nat) : Comp pqxdhOps pqPrimIface Δ (.prod (B 32) (B 32)) :=
  letV (.pair idx (.pair chalP s)) fun a =>
  .ite (natEq (.snd (.snd (v a))) (.fst (v a)))
    (.ret (.fst (.snd (v a))))
    (sampCkPairC (natLt (.snd (.snd (v a))) (.fst (v a))))

def authCkSendB (opk : Bool) (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair aNone (v fhst) : Expr pqxdhOps _ RSF) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (ahsBase (v hst)) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (v noneDone)) <|
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid))
    (.ret (v noneDone)) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  bindV (resolveSigPkC S K st (pkbIkB (v bu))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
    (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu))))) fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
    (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu))))) fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
  letV (.fst (v sc)) fun ssKem =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (checkBundleSpkHonIdealC S K st bu) fun spkHonIdeal =>
  letV (eCaseOpt (v pp) (.bool false) fun p =>
    eAny K (asSpkBundles (v st)) fun b =>
      .and (natEq (.fst (.fst (v b))) (.fst (v p)))
        (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkHon =>
  letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
    fun isIdealSend =>
  letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ssKem) (.pair (v kemCt)
      (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
  .ite (v isIdealSend)
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v ss) (v sid)) fun sa =>
     bindV (sampAtCkC (v idx) (v chalP) (.fst (v sa))) fun p =>
     letV (.fst (v p)) fun mkSeed =>
     letV (.snd (v p)) fun ck1_1 =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (litB 32 [])
             (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (asRoCache (v st)) (asRootRoCache (v st))))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (.snd (v sa)))))
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
     bindV (hkdfRoC K st (v secrets)) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
     bindV (rootRoC K st (.fst (v drKey)) (v dhR)) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (v ss))))

def finishAuthRecvCkC (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rc' : Expr pqxdhOps Δ .nat)
    (p : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair drKey (.pair rk1 (.pair spqrSalt? (.pair rc' p)))) fun args =>
  letV (.fst (v args)) fun drKey =>
  letV (.fst (.snd (v args))) fun rk1 =>
  letV (.fst (.snd (.snd (v args)))) fun spqrSalt? =>
  letV (.fst (.snd (.snd (.snd (v args))))) fun rc' =>
  letV (.fst (.snd (.snd (.snd (.snd (v args)))))) fun mkSeed =>
  letV (.snd (.snd (.snd (.snd (.snd (v args)))))) fun ck1_1 =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
  letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
      (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
  bindV (queryPrim (.aeadDec 158 32 32)
    (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
  letV (eCaseOpt (v pt?) .none fun pt =>
    .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
      (.pair (v pt) (.pair (asRoCache (v st)) (asRootRoCache (v st)))))))) fun res? =>
  bindV (recvFinishTagRunC S K fTag (v res?)) fun out =>
  .ret (.pair (.fst (v out)) (ahsfMk (.snd (v out)) (v rc') .nil))

def authCkRecvB (opk : Bool) (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.add (v rc) (.nat 1)) fun rc' =>
  bindV (prepareAuthHybridRecvC S K opk hst x) fun prep? =>
  caseOptV (v prep?) (.ret (.pair aNone (ahsfUpd (v fhst) (rc := v rc')))) fun prep =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  letV (boolOr (isSomeE (parMatchedSess? (v prep))) (parIsUncorrSender (v prep))) fun useIdeal =>
  .ite (v useIdeal)
    (caseOptV (parMatchedSess? (v prep))
      (bindV (samplePrim .drKey96) fun drKey =>
       bindV (samplePrim .bytes32) fun rk1 =>
       bindV (queryPrim (.spqrInitRecv 32 32)
         (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
       caseOptV (v sp?)
         (bindV (recvFinishTagRunC S K fTag .none) fun out =>
          .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
         fun sp =>
           letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
           bindV (sampAtCkC (v idx) (v chalP) (.fst (v ra))) fun p =>
           bindV (finishAuthRecvCkC S K msg prep (v drKey) (v rk1) (.snd (v sp)) (v rc') (v p)) fun res =>
           .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := .snd (v ra)))))
      fun s =>
        .ite (parSameEph (v prep))
          (bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K fTag .none) fun out =>
              .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
             fun sp =>
               bindV (finishAuthRecvCkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s)) (.snd (v sp))
                 (v rc') (.pair (iasMkSeed (v s)) (iasCk1_1 (v s)))) fun res =>
               .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))
          (bindV (samplePrim .bytes32) fun rk1 =>
           bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K fTag .none) fun out =>
              .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
             fun sp =>
               letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
               bindV (sampAtCkC (v idx) (v chalP) (.fst (v ra))) fun p =>
               bindV (finishAuthRecvCkC S K msg prep (iasDrKey (v s)) (v rk1) (.snd (v sp))
                 (v rc') (v p)) fun res =>
               .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := .snd (v ra))))))
    (bindV (hkdfRoC K st (parSecrets (v prep))) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (rootRoC K st (.fst (v drKey)) (parDhRatchet (v prep))) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitRecv 32 32)
       (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
     caseOptV (v sp?)
       (bindV (recvFinishTagRunC S K fTag .none) fun out =>
        .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
       fun sp =>
         bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mks =>
         letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
             (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
         bindV (queryPrim (.aeadDec 158 32 32)
           (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
         letV (eCaseOpt (v pt?) .none fun pt =>
           .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
             (.pair (v pt) (.pair (v roC') (v rootC'))))))) fun res? =>
         bindV (recvFinishTagRunC S K fTag (v res?)) fun out =>
         .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))

def authCkStepC (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  caseSumV (v q) (fun u => initPrinFixedB K fhst u) fun q =>
  caseSumV (v q) (fun u => corruptFixedB K fhst u) fun q =>
  caseSumV (v q) (fun x => genSpkFixedB K fhst x) fun q =>
  caseSumV (v q) (fun x => genOpkFixedB K fhst x) fun q =>
  caseSumV (v q) (fun x => authCkSendB S K true idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkSendB S K false idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkRecvB S K true idx chalP fhst x) fun q =>
  caseSumV (v q) (fun x => authCkRecvB S K false idx chalP fhst x) fun q =>
  caseSumV (v q) (fun sec => roFixedB K fhst sec) fun q =>
  caseSumV (v q) (fun x => roRootFixedB K fhst x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v fhst))) fun sk =>
  registerFixedB fhst sk

end PrfCkBranches

@[reducible] def prfCkInitDslK (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrimIface [.prod (B 32) (B 32)] (.prod .unit prfCkStTy) :=
  bindV (samplePrim (.index (min K S.N_sess_tot))) fun idx =>
  bindV (samplePrim .bool) fun secb =>
  .ret (.pair .unit
    (.pair (v secb) (.pair (v idx)
      (.pair (.var (.succ (.succ .zero))) (emptyAuthHybridStFixedE (v secb))))))

def prfCkInitDsl (S : Setup) :
    Comp pqxdhOps pqPrimIface [.prod (B 32) (B 32)] (.prod .unit prfCkStTy) :=
  bindV (samplePrim (.index S.N_sess_tot)) fun idx =>
  bindV (samplePrim .bool) fun secb =>
  .ret (.pair .unit
    (.pair (v secb) (.pair (v idx)
      (.pair (.var (.succ (.succ .zero))) (emptyAuthHybridStFixedE (v secb))))))

def prfCkHandleDsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrimIface [prfCkStTy, authQueryTy] (.prod authRespTy prfCkStTy) :=
  letV (.var .zero : Expr pqxdhOps [prfCkStTy, authQueryTy] prfCkStTy) fun s =>
  letV (ckSecb (v s)) fun secb =>
  letV (ckIdx (v s)) fun idx =>
  letV (ckChal (v s)) fun chalP =>
  letV (ckFhst (v s)) fun fhst =>
  bindV (authCkStepC S K idx chalP fhst
    (.succ .zero : Var [prfCkStTy, authQueryTy] authQueryTy)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v secb) (.pair (v idx) (.pair (v chalP) (.snd (v r))))))

def prfCkFinishDsl (S : Setup) (K : Nat) : Comp pqxdhOps pqPrimIface [prfCkStTy, .bool] .bool :=
  letV (ckSecb (.var .zero)) fun _secb =>
  letV (.var (.succ (.succ .zero)) : Expr pqxdhOps [.bool, prfCkStTy, .bool] .bool) fun _b' =>
  letV (ahsfHybrid (ckFhst (.var (.succ (.succ .zero))))) fun _finalSt =>
  finalizeAuthFixedDsl S K

/-- `ReductionDsl` witness for `prfCkReductionAuthFixed` with list-traversal bound `K`. -/
def prfCkRedProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      (.prod (B 32) (B 32)) .unit .bool .bool where
  σ      := prfCkStTy
  init   := prfCkInitDslK S K
  handle := prfCkHandleDsl S K
  finish := prfCkFinishDsl S K

/-! ## `PrfMsgKeys` Reduction Program -/

abbrev prfMkCoreTy : PT :=
  .prod .bool (.prod .nat (.prod .bool authHybridStateFixedTy))

/-- Full state `(bud, core)` of `prfMsgKeysRedProg`, pairing remaining challenger budget with `prfMkCoreTy`. -/
abbrev prfMkStTy : PT := .prod .nat prfMkCoreTy

@[reducible] def mkcSecb {Γ} (c : Expr pqxdhOps Γ prfMkCoreTy) : Expr pqxdhOps Γ .bool := .fst c
@[reducible] def mkcIdx {Γ} (c : Expr pqxdhOps Γ prfMkCoreTy) : Expr pqxdhOps Γ .nat := .fst (.snd c)
@[reducible] def mkcSentChal {Γ} (c : Expr pqxdhOps Γ prfMkCoreTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd c))
@[reducible] def mkcFhst {Γ} (c : Expr pqxdhOps Γ prfMkCoreTy) :
    Expr pqxdhOps Γ authHybridStateFixedTy :=
  .snd (.snd (.snd c))
@[reducible] def mkcMk {Γ} (secb : Expr pqxdhOps Γ .bool) (idx : Expr pqxdhOps Γ .nat)
    (sc : Expr pqxdhOps Γ .bool) (fhst : Expr pqxdhOps Γ authHybridStateFixedTy) :
    Expr pqxdhOps Γ prfMkCoreTy :=
  .pair secb (.pair idx (.pair sc fhst))

abbrev prfMkSendContTy : PT :=
  .prod .bool (.prod .nat (.prod authHybridStateFixedTy
    (.prod sessionIdTy (.prod principalEntryTy (.prod (.opt (.prod .nat principalEntryTy))
      (.prod .bool (.prod preKeyBundleTy (.prod (.prod (B 32) (B 32))
        (.prod keys6Ty
          (.prod drKeyTy (.prod (B 32) (.prod (B 32)
            (.prod (.opt (B 32)) (.prod (B 32) (B 32)))))))))))))))

abbrev prfMkRecvContTy : PT :=
  .prod .bool (.prod .nat (.prod .bool
    (.prod preKeyMsgTy (.prod preparedAuthRecvTy
      (.prod drKeyTy (.prod (B 32) (.prod (B 32)
        (.prod .nat (.prod authMkSaltCacheTy
          (.prod authSlotStateTy
            (.opt (.prod (.prod sessionIdTy (.opt (B 32))) .nat))))))))))))

abbrev prfMkChalContTy : PT := .sum prfMkSendContTy prfMkRecvContTy
abbrev prfMkStepPreTy : PT :=
  .sum (.prod authRespTy prfMkCoreTy) (.prod (.opt (B 32)) prfMkChalContTy)

section PrfMsgKeysBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

def wrapMkBase (core : Var Γ₁ prfMkCoreTy) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF) :
    Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  bindV m fun r =>
  .ret (.inl (.pair (.fst (v r))
    (mkcMk (mkcSecb (v core)) (mkcIdx (v core)) (mkcSentChal (v core)) (.snd (v r)))))

def finishAuthSendMkC (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty) (drKey : Expr pqxdhOps Δ drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32)) (mks : Expr pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair sid (.pair uE (.pair pp (.pair isFresh (.pair bu (.pair m01
    (.pair keys6 (.pair drKey (.pair rk1 (.pair mkSeed (.pair ck1_1
      (.pair spqrSalt? (.pair pqMsg (.pair msgPlain mks)))))))))))))) fun a =>
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (v a)) fun sid =>
  letV (.fst (.snd (v a))) fun uE =>
  letV (.fst (.snd (.snd (v a)))) fun pp =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun isFresh =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun bu =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v a))))))) fun m01 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))) fun keys6 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))) fun drKey =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))))) fun rk1 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))) fun mkSeed =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (v a)))))))))))) fun ck1_1 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (v a))))))))))))) fun spqrSalt? =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (v a)))))))))))))) fun pqMsg =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))))))) fun msgPlain =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))))))))))) fun mks =>
  letV (.snd (.snd (.snd (.snd (.snd (v keys6)))))) fun ephAPk =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  bindV (queryPrim (.aeadEnc 158 32 32)
    (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
  bindV (finishAuthHybridSendC S K hst
    (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
      (.pair (v m01) (.pair (v keys6)
        (.pair (v drKey) (.pair (.pair (v rk1) (.pair (litB 32 []) (.pair (v mkSeed) (v ck1_1))))
          (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
            (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
              (.pair (asRoCache (v st)) (asRootRoCache (v st))))))))))))))))))) fun out =>
  .ret (.pair (.fst (v out)) (ahsfUpd (v fhst) (hst := .snd (v out))))

def finishAuthRecvMkC (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair drKey (.pair rk1 (.pair ck1_1 (.pair rc' (.pair cache' mks))))) fun a =>
  letV (.fst (v a)) fun drKey =>
  letV (.fst (.snd (v a))) fun rk1 =>
  letV (.fst (.snd (.snd (v a)))) fun ck1_1 =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun rc' =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun cache' =>
  letV (.snd (.snd (.snd (.snd (.snd (v a)))))) fun mks =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
      (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
  bindV (queryPrim (.aeadDec 158 32 32)
    (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
  letV (eCaseOpt (v pt?) .none fun pt =>
    .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
      (.pair (v pt) (.pair (asRoCache (v st)) (asRootRoCache (v st)))))))) fun res? =>
  bindV (recvFinishTagRunC S K fTag (v res?)) fun out =>
  .ret (.pair (.fst (v out)) (ahsfMk (.snd (v out)) (v rc') (v cache')))

def authMkSendPreB (opk : Bool) (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcSecb (v core)) fun secb =>
  letV (mkcIdx (v core)) fun idx =>
  letV (mkcSentChal (v core)) fun sentChal =>
  letV (mkcFhst (v core)) fun fhst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (.inl (.pair aNone (v core)) : Expr pqxdhOps _ prfMkStepPreTy) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (v noneDone)) <|
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret (v noneDone)) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  bindV (resolveSigPkC S K st (pkbIkB (v bu))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
    (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu))))) fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
    (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu))))) fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
  letV (.fst (v sc)) fun ssKem =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (checkBundleSpkHonIdealC S K st bu) fun spkHonIdeal =>
  letV (eCaseOpt (v pp) (.bool false) fun p =>
    eAny K (asSpkBundles (v st)) fun b =>
      .and (natEq (.fst (.fst (v b))) (.fst (v p)))
        (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkHon =>
  letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
    fun isIdealSend =>
  letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ssKem) (.pair (v kemCt)
      (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
  .ite (v isIdealSend)
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v ss) (v sid)) fun sa =>
     letV (.fst (v sa)) fun sIdx =>
     letV (ahsfUpdSlots (v fhst) (slots := .snd (v sa))) fun fhst' =>
     .ite (.and (.not (v sentChal)) (natEq (v sIdx) (v idx)))
       (bindV (samplePrim .bytes32) fun ck1_1 =>
        .ret (.inr (.pair (v spqrSalt?)
          (.inl (.pair (v secb) (.pair (v idx) (.pair (v fhst')
            (.pair (v sid) (.pair (v uE) (.pair (v pp)
              (.pair (v isFresh) (.pair (v bu) (.pair (.pair (v m0) (v m1))
                (.pair (v keys6) (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                  (.pair (v spqrSalt?) (.pair (v pqMsg) (v msgPlain))))))))))))))))))))
       (.ite (natLt (v sIdx) (v idx))
         (bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (samplePrim .msgKeys80) fun mks =>
          bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))
         (bindV (samplePrim .bytes32) fun mkSeed =>
          bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
          bindV (finishAuthSendMkC S K fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (v mkSeed) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))))
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
     bindV (hkdfRoC K st (v secrets)) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
     bindV (rootRoC K st (.fst (v drKey)) (v dhR)) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.inl (.pair (.fst (v out))
       (mkcMk (v secb) (v idx) (v sentChal)
         (ahsfUpd (v fhst) (hst := .snd (v out)))))))

def finishRecvUnmatchedMkPreC (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (.pair drKey (.pair rk1 (.pair spqrSalt? (.pair rSlot rc')))) fun a =>
  letV (.fst (v a)) fun drKey =>
  letV (.fst (.snd (v a))) fun rk1 =>
  letV (.fst (.snd (.snd (v a)))) fun spqrSalt? =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun rSlot =>
  letV (.snd (.snd (.snd (.snd (v a))))) fun rc' =>
  letV (mkcSecb (v core)) fun secb =>
  letV (mkcIdx (v core)) fun idx =>
  letV (mkcSentChal (v core)) fun sentChal =>
  letV (ahsfMkSaltCache (mkcFhst (v core))) fun cache =>
  letV (ahsfSlots (mkcFhst (v core))) fun ssV =>
  .ite (natEq (v rSlot) (v idx))
    (bindV (samplePrim .bytes32) fun ck1_1 =>
     .ite (.not (v sentChal))
       (.ret (.inr (.pair (v spqrSalt?)
         (.inr (.pair (v secb) (.pair (v idx) (.pair (v sentChal)
           (.pair (v msg) (.pair (v prep)
             (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
               (.pair (v rc') (.pair (v cache) (.pair (v ssV) .none)))))))))))))))
       (bindV (samplePrim .msgKeys80) fun mks =>
        bindV (finishAuthRecvMkC S K msg prep (v drKey) (v rk1) (v ck1_1) (v rc')
          (v cache) (v mks)) fun res =>
        .ret (.inl (.pair (.fst (v res))
          (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ssV)))))))
    (.ite (natLt (v rSlot) (v idx))
      (bindV (samplePrim .bytes32) fun ck1_1 =>
       bindV (samplePrim .msgKeys80) fun mks =>
       bindV (finishAuthRecvMkC S K msg prep (v drKey) (v rk1) (v ck1_1) (v rc')
         (v cache) (v mks)) fun res =>
       .ret (.inl (.pair (.fst (v res))
         (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ssV))))))
      (bindV (samplePrim .bytes32) fun mkSeed =>
       bindV (samplePrim .bytes32) fun ck1_1 =>
       bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
       bindV (finishAuthRecvMkC S K msg prep (v drKey) (v rk1) (v ck1_1) (v rc')
         (v cache) (v mks)) fun res =>
       .ret (.inl (.pair (.fst (v res))
         (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ssV)))))))

def authMkRecvPreB (opk : Bool) (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcSecb (v core)) fun secb =>
  letV (mkcIdx (v core)) fun idx =>
  letV (mkcSentChal (v core)) fun sentChal =>
  letV (mkcFhst (v core)) fun fhst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  letV (ahsfMkSaltCache (v fhst)) fun cache =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.add (v rc) (.nat 1)) fun rc' =>
  bindV (prepareAuthHybridRecvC S K opk hst x) fun prep? =>
  caseOptV (v prep?)
    (.ret (.inl (.pair aNone
      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpd (v fhst) (rc := v rc'))))))
    fun prep =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  letV (boolOr (isSomeE (parMatchedSess? (v prep))) (parIsUncorrSender (v prep))) fun useIdeal =>
  .ite (v useIdeal)
    (caseOptV (parMatchedSess? (v prep))
      (bindV (samplePrim .drKey96) fun drKey =>
       bindV (samplePrim .bytes32) fun rk1 =>
       bindV (queryPrim (.spqrInitRecv 32 32)
         (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
       caseOptV (v sp?)
         (bindV (recvFinishTagRunC S K fTag .none) fun out =>
          .ret (.inl (.pair (.fst (v out))
            (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
         fun sp =>
           letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
           letV (mkcMk (v secb) (v idx) (v sentChal)
             (ahsfUpdSlots (v fhst) (slots := .snd (v ra)))) fun core' =>
           finishRecvUnmatchedMkPreC S K core' msg prep (v drKey) (v rk1) (.snd (v sp))
             (.fst (v ra)) (v rc'))
      fun s =>
        .ite (parSameEph (v prep))
          (bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K fTag .none) fun out =>
              .ret (.inl (.pair (.fst (v out))
                (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
             fun sp =>
               letV (.snd (v sp)) fun spqrSalt? =>
               letV (lookupSendSlotOrZeroE (v ss) (iasSid (v s))) fun sIdx =>
               letV (.pair (iasSid (v s)) (v spqrSalt?)) fun cKey =>
               .ite (natEq (v sIdx) (v idx))
                 (.ite (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))
                   (bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                       (iasCk1_1 (v s)) (v rc') (v cache) (iasMsgKeys (v s))) fun res =>
                    .ret (.inl (.pair (.fst (v res))
                      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                   (caseOptV (eFind K (v cache) fun e =>
                       .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                         (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
                     (.ret (.inr (.pair (v spqrSalt?)
                       (.inr (.pair (v secb) (.pair (v idx) (.pair (v sentChal)
                         (.pair (v msg) (.pair (v prep)
                           (.pair (iasDrKey (v s)) (.pair (iasRk1 (v s)) (.pair (iasCk1_1 (v s))
                             (.pair (v rc') (.pair (v cache)
                               (.pair (v ss) (.some (.pair (v cKey) (v rc))))))))))))))))))
                     fun cEntry =>
                       bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                         (iasCk1_1 (v s)) (v rc') (v cache) (.snd (.snd (v cEntry)))) fun res =>
                       .ret (.inl (.pair (.fst (v res))
                         (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss)))))))
                 (.ite (natLt (v sIdx) (v idx))
                   (.ite (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))
                     (bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                         (iasCk1_1 (v s)) (v rc') (v cache) (iasMsgKeys (v s))) fun res =>
                      .ret (.inl (.pair (.fst (v res))
                        (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                     (caseOptV (eFind K (v cache) fun e =>
                       .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                         (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
                       (bindV (samplePrim .msgKeys80) fun mk =>
                        letV (.cons (.pair (v cKey) (.pair (v rc) (v mk))) (v cache))
                          fun cache' =>
                        bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                          (iasCk1_1 (v s)) (v rc') (v cache') (v mk)) fun res =>
                        .ret (.inl (.pair (.fst (v res))
                          (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                       fun cEntry =>
                         bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                           (iasCk1_1 (v s)) (v rc') (v cache) (.snd (.snd (v cEntry)))) fun res =>
                         .ret (.inl (.pair (.fst (v res))
                           (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss)))))))
                   (bindV (queryPrim (.deriveMsgKeys 32) (.pair (iasMkSeed (v s)) (v spqrSalt?)))
                      fun mk =>
                    bindV (finishAuthRecvMkC S K msg prep (iasDrKey (v s)) (iasRk1 (v s))
                      (iasCk1_1 (v s)) (v rc') (v cache) (v mk)) fun res =>
                    .ret (.inl (.pair (.fst (v res))
                      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))))
          (bindV (samplePrim .bytes32) fun rk1 =>
           bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K fTag .none) fun out =>
              .ret (.inl (.pair (.fst (v out))
                (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
             fun sp =>
               letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
               letV (mkcMk (v secb) (v idx) (v sentChal)
                 (ahsfUpdSlots (v fhst) (slots := .snd (v ra)))) fun core' =>
               finishRecvUnmatchedMkPreC S K core' msg prep (iasDrKey (v s)) (v rk1) (.snd (v sp))
                 (.fst (v ra)) (v rc')))
    (bindV (hkdfRoC K st (parSecrets (v prep))) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (rootRoC K st (.fst (v drKey)) (parDhRatchet (v prep))) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitRecv 32 32)
       (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
     caseOptV (v sp?)
       (bindV (recvFinishTagRunC S K fTag .none) fun out =>
        .ret (.inl (.pair (.fst (v out))
          (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
       fun sp =>
         bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mks =>
         letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
             (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
         bindV (queryPrim (.aeadDec 158 32 32)
           (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
         letV (eCaseOpt (v pt?) .none fun pt =>
           .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
             (.pair (v pt) (.pair (v roC') (v rootC'))))))) fun res? =>
         bindV (recvFinishTagRunC S K fTag (v res?)) fun out =>
         .ret (.inl (.pair (.fst (v out))
           (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))

def prfMkStepPreC (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcFhst (v core)) fun fhst =>
  caseSumV (v q) (fun u => wrapMkBase core (initPrinFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun u => wrapMkBase core (corruptFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (genSpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (genOpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => authMkSendPreB S K true core x) fun q =>
  caseSumV (v q) (fun x => authMkSendPreB S K false core x) fun q =>
  caseSumV (v q) (fun x => authMkRecvPreB S K true core x) fun q =>
  caseSumV (v q) (fun x => authMkRecvPreB S K false core x) fun q =>
  caseSumV (v q) (fun sec => wrapMkBase core (roFixedB K fhst sec)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (roRootFixedB K fhst x) ) fun q =>
  caseSumV (v q) (fun _ => .ret (.inl (.pair aNone (v core)))) fun sk =>
  wrapMkBase core (registerFixedB fhst sk)

def prfMkStepPostC (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.prod authRespTy prfMkCoreTy) :=
  caseSumV (v cont)
    (fun sCont =>
      letV (.fst (v sCont)) fun secb =>
      letV (.fst (.snd (v sCont))) fun idx =>
      letV (.fst (.snd (.snd (v sCont)))) fun fhst =>
      letV (.fst (.snd (.snd (.snd (v sCont))))) fun sid =>
      letV (.fst (.snd (.snd (.snd (.snd (v sCont)))))) fun uE =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (v sCont))))))) fun pp =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v sCont)))))))) fun isFresh =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sCont))))))))) fun bu =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sCont)))))))))) fun m01 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (v sCont))))))))))) fun keys6 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (v sCont)))))))))))) fun drKey =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (.snd (v sCont))))))))))))) fun rk1 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (.snd (.snd (v sCont)))))))))))))) fun ck1_1 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sCont))))))))))))))) fun spqrSalt? =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sCont)))))))))))))))) fun pqMsg =>
      letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sCont)))))))))))))))) fun msgPlain =>
      bindV (finishAuthSendMkC S K fhst (v sid) (v uE) (v pp) (v isFresh) (v bu) (v m01)
        (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1) (v spqrSalt?) (v pqMsg)
        (v msgPlain) (v mk)) fun res =>
      .ret (.pair (.fst (v res)) (mkcMk (v secb) (v idx) (.bool true) (.snd (v res)))))
    (fun rCont =>
      letV (.fst (v rCont)) fun secb =>
      letV (.fst (.snd (v rCont))) fun idx =>
      letV (.fst (.snd (.snd (v rCont)))) fun sentChal =>
      letV (.fst (.snd (.snd (.snd (v rCont))))) fun msg =>
      letV (.fst (.snd (.snd (.snd (.snd (v rCont)))))) fun prep =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (v rCont))))))) fun drKey =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v rCont)))))))) fun rk1 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v rCont))))))))) fun ck1_1 =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v rCont)))))))))) fun rc' =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (v rCont))))))))))) fun cache =>
      letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (v rCont)))))))))))) fun ss' =>
      letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd
        (.snd (.snd (.snd (.snd (v rCont)))))))))))) fun ci? =>
      letV (eCaseOpt (v ci?) (v cache) fun ci =>
        .cons (.pair (.fst (v ci)) (.pair (.snd (v ci)) (v mk))) (v cache)) fun cache' =>
      bindV (finishAuthRecvMkC S K msg prep (v drKey) (v rk1) (v ck1_1) (v rc')
        (v cache') (v mk)) fun res =>
      .ret (.pair (.fst (v res))
        (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss')))))

end PrfMsgKeysBranches

@[reducible] def prfMsgKeysInitDslK (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrfMkIface [.unit] (.prod .unit prfMkStTy) :=
  bindV (sampleChal (.index (min K S.N_sess_tot))) fun idx =>
  bindV (sampleChal .bool) fun secb =>
  .ret (.pair .unit
    (.pair (.nat (min K S.N_recv_tot + 1))
      (mkcMk (v secb) (v idx) (.bool false) (emptyAuthHybridStFixedE (v secb)))))

def prfMsgKeysInitDsl (S : Setup) :
    Comp pqxdhOps pqPrfMkIface [.unit] (.prod .unit prfMkStTy) :=
  bindV (sampleChal (.index S.N_sess_tot)) fun idx =>
  bindV (sampleChal .bool) fun secb =>
  .ret (.pair .unit
    (.pair (.nat (S.N_recv_tot + 1))
      (mkcMk (v secb) (v idx) (.bool false) (emptyAuthHybridStFixedE (v secb)))))

def prfMsgKeysHandleDsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrfMkIface [prfMkStTy, authQueryTy] (.prod authRespTy prfMkStTy) :=
  letV (.var .zero : Expr pqxdhOps [prfMkStTy, authQueryTy] prfMkStTy) fun s =>
  letV (.fst (v s)) fun bud =>
  letV (.snd (v s)) fun core =>
  bindV (liftPrimComp
    (prfMkStepPreC S K core (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy))) fun pre =>
  caseSumV (v pre)
    (fun d => .ret (.pair (.fst (v d)) (.pair (v bud) (.snd (v d)))))
    fun req =>
      .ite (natEq (v bud) (.nat 0))
        (.ret (.pair aNone (.pair (.nat 0) (v core))))
        (letV (.fst (v req)) fun salt? =>
         letV (.snd (v req)) fun cont =>
         bindV (queryDeriveMk (v salt?)) fun mk =>
         bindV (liftPrimComp (prfMkStepPostC S K cont mk)) fun post =>
         .ret (.pair (.fst (v post))
           (.pair (.sub (v bud) (.nat 1)) (.snd (v post)))))

def prfMsgKeysFinishDsl (S : Setup) (K : Nat) : Comp pqxdhOps pqPrfMkIface [prfMkStTy, .bool] .bool :=
  liftPrimComp
    (letV (.snd (.var .zero)) fun core =>
     letV (mkcSecb (v core)) fun _secb =>
     letV (.var (.succ (.succ (.succ .zero))) :
       Expr pqxdhOps [.bool, prfMkCoreTy, prfMkStTy, .bool] .bool) fun _b' =>
     letV (ahsfHybrid (mkcFhst (v core))) fun _finalSt =>
     finalizeAuthFixedDsl S K)

/-- `ReductionDsl` witness for `prfMsgKeysReductionAuthFixed` with list-traversal bound `K`. -/
def prfMsgKeysRedProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool where
  σ      := prfMkStTy
  init   := prfMsgKeysInitDslK S K
  handle := prfMsgKeysHandleDsl S K
  finish := prfMsgKeysFinishDsl S K

end SignalPqxdh.Security.ReductionDsl.AuthPrf
