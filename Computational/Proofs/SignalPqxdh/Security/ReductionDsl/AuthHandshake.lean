/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.PqxdhTables
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.CostUB
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
import VCVio.EvalDist.Monad.Basic

/-!
# Shared Types, Combinators, and Bridges for `ReductionDsl` `Auth` Reductions

Defines `Ty pqSig` encodings, named-variable `Ext` combinators, bounded monadic list bridges,
and shared PQXDH `Auth` simulator handler branches for `ReductionDsl` reductions.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open SignalPqxdh.LegacyCosted

@[reducible] def Ty.u32 : Ty pqSig := SignalPqxdh.LegacyCosted.U32
@[reducible] def Var.vz {S : Sig} {Γ : List (Ty S)} {t : Ty S} :
    Var (t :: Γ) t := .zero
@[reducible] def Var.vs {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (v : Var Γ t) : Var (u :: Γ) t := .succ v

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

/-- Retraction/isomorphism between a host type `α` and a `Ty pqSig` representation `τ`. -/
structure ValIso (α : Type) (τ : Ty pqSig) where
  toVal       : α → τ.denote
  ofVal       : τ.denote → α
  ofVal_toVal : ∀ x, ofVal (toVal x) = x

/-! ## Protocol and Game Value Encodings -/

abbrev drKeyTy : Ty pqSig := drKeyT
@[simp] abbrev drKeyToVal : DRKey → drKeyTy.denote := drKeyV
@[simp] abbrev valToDrKey : drKeyTy.denote → DRKey := drKeyOfV
@[simp] theorem valToDrKey_drKeyToVal (k : DRKey) : valToDrKey (drKeyToVal k) = k := rfl

abbrev msgKeysTy : Ty pqSig := msgKeysT
@[simp] abbrev msgKeysToVal : MessageKeys → msgKeysTy.denote := msgKeysV
@[simp] abbrev valToMsgKeys : msgKeysTy.denote → MessageKeys := msgKeysOfV

abbrev preKeyBundleTy : Ty pqSig := bundleT
@[simp] abbrev preKeyBundleToVal : PreKeyBundleInput → preKeyBundleTy.denote := bundleV
@[simp] abbrev valToPreKeyBundle : preKeyBundleTy.denote → PreKeyBundleInput := bundleOfV
@[simp] theorem valToPreKeyBundle_preKeyBundleToVal (b : PreKeyBundleInput) :
    valToPreKeyBundle (preKeyBundleToVal b) = b := rfl

abbrev handshakeHdrTy : Ty pqSig := hdrT
@[simp] abbrev handshakeHdrToVal : HandshakeHdr → handshakeHdrTy.denote := hdrV
@[simp] abbrev valToHandshakeHdr : handshakeHdrTy.denote → HandshakeHdr := hdrOfV

abbrev preKeyMsgTy : Ty pqSig := preKeyMsgT
@[simp] abbrev preKeyMsgToVal : PreKeyMsg → preKeyMsgTy.denote := preKeyMsgV
@[simp] abbrev valToPreKeyMsg : preKeyMsgTy.denote → PreKeyMsg := preKeyMsgOfV

abbrev sessionIdTy : Ty pqSig := sidT
@[simp] abbrev sessionIdToVal {S : Setup} : SessionId S → sessionIdTy.denote := sidV

abbrev authQueryTy : Ty pqSig := authQT
@[simp] abbrev authQueryToVal {S : Setup} : AuthQuery S → authQueryTy.denote := authQenc

abbrev authRespTy : Ty pqSig := authRT
@[simp] abbrev authRespToVal : AuthResponse → authRespTy.denote := authRenc
@[simp] abbrev valToAuthResp : authRespTy.denote → AuthResponse := authRdec
@[simp] theorem valToAuthResp_authRespToVal (r : AuthResponse) :
    valToAuthResp (authRespToVal r) = r := authRdec_authRenc r

abbrev principalEntryTy : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32) .bool)))
@[simp] def principalEntryToVal (e : PrincipalEntry) : principalEntryTy.denote :=
  (e.secIKA0, (e.ikAPk, (e.secIKAsign, (e.ikSignPk, e.corrupted))))

abbrev spkBundleEntryTy : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod (B 64)
    (.prod (B 3168) (.prod (B 1568) (.prod (B 64) .bool)))))
@[simp] def spkBundleEntryToVal (b : SpkBundleEntry) : spkBundleEntryTy.denote :=
  (b.spkSk, (b.spkPk, (b.spkSig, (b.pqspkSk, (b.pqspkPk, (b.pqspkSig, b.revealed))))))

abbrev opkEntryTy : Ty pqSig := .prod (B 32) (.prod (B 32) .bool)
@[simp] def opkEntryToVal (o : OpkEntry) : opkEntryTy.denote := (o.opkSk, (o.opkPk, o.consumed))

abbrev sentOPKEventTy : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (.prod (B 32) .bool)))))))
@[simp] def sentOPKEventToVal (e : SentOPKEvent) : sentOPKEventTy.denote :=
  (e.a0, (e.b0, (e.sb, (e.ob, (e.a1, (e.pk1, (e.ct, (e.m, e.matched))))))))

abbrev sentNoOPKEventTy : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (.prod (B 32) .bool))))))
@[simp] def sentNoOPKEventToVal (e : SentNoOPKEvent) : sentNoOPKEventTy.denote :=
  (e.a0, (e.b0, (e.sb, (e.a1, (e.pk1, (e.ct, (e.m, e.matched)))))))

abbrev recvdOPKEventTy : Ty pqSig :=
  .prod .bool (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (B 32))))))))
@[simp] def recvdOPKEventToVal (e : RecvdOPKEvent) : recvdOPKEventTy.denote :=
  (e.bCorr, (e.a0, (e.b0, (e.sb, (e.ob, (e.a1, (e.pk1, (e.ct, e.m))))))))

abbrev recvdNoOPKEventTy : Ty pqSig :=
  .prod .bool (.prod (B 32) (.prod (B 32)
    (.prod (B 32) (.prod (B 32) (.prod (B 1568) (.prod (B 1568) (B 32)))))))
@[simp] def recvdNoOPKEventToVal (e : RecvdNoOPKEvent) : recvdNoOPKEventTy.denote :=
  (e.bCorr, (e.a0, (e.b0, (e.sb, (e.a1, (e.pk1, (e.ct, e.m)))))))

abbrev authSessionEntryTy : Ty pqSig :=
  .prod sessionIdTy (.prod (B 32) (.prod (B 32) (.prod (.opt (B 32)) (.prod (B 1568)
    (.prod .bool (.prod .bool (.prod .bool (.prod (B 32) (.prod (B 32) (.prod .bool .bool))))))))))
@[simp] def authSessionEntryToVal {S : Setup} (s : AuthInitiatorEntry S) :
    authSessionEntryTy.denote :=
  (sessionIdToVal s.sid, (s.peerIkPk, (s.peerSpkPk, (s.peerOpkPk?, (s.peerPqspkPk,
    (s.spkHonest, (s.opkHonest, (s.pqspkHonest,
      (s.ekASk, (s.ephASk, (s.fresh, s.challenged)))))))))))

abbrev roCacheEntryTy : Ty pqSig := .prod (B 192) drKeyTy
abbrev rootRoCacheEntryTy : Ty pqSig := .prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))

abbrev authStateTy : Ty pqSig :=
  .prod .bool (.prod .bool (.prod (.list (.prod .nat principalEntryTy))
    (.prod (.list (.prod (.prod .nat .nat) spkBundleEntryTy))
      (.prod (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy))
        (.prod (.list authSessionEntryTy) (.prod (.list sessionIdTy)
          (.prod (.list (.prod .nat (.prod .nat .nat)))
            (.prod (.list (.prod .nat (.prod .nat .nat)))
              (.prod (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))
                (.prod (.list sentOPKEventTy) (.prod (.list sentNoOPKEventTy)
                  (.prod (.list recvdOPKEventTy) (.prod (.list recvdNoOPKEventTy)
                    (.prod (.list roCacheEntryTy)
                      (.prod (.list rootRoCacheEntryTy)
                        (.list (.prod (B 32) (B 32))))))))))))))))))

@[simp] def authStateToVal {S : Setup} (st : AuthState S) : authStateTy.denote :=
  (st.secb, (st.hasWonAuth, (st.principals.map (Prod.map id principalEntryToVal),
    (st.spkBundles.map (Prod.map id spkBundleEntryToVal),
      (st.opkEntries.map (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal),
        (st.sessions.map authSessionEntryToVal, (st.usedSendSessions.map sessionIdToVal,
          (st.usedRecvOPK.map (fun (k, j, o) => (k, (j, o))),
            (st.usedRecvNoOPK.map (fun (k, j, l) => (k, (j, l))),
              (st.seenKyberBaseKeys.map (fun (k, p, s, e) => (k, (p, (s, e)))),
                (st.sentOPKEvents.map sentOPKEventToVal,
                  (st.sentNoOPKEvents.map sentNoOPKEventToVal,
                    (st.recvdOPKEvents.map recvdOPKEventToVal,
                      (st.recvdNoOPKEvents.map recvdNoOPKEventToVal,
                        (st.roCache.map (Prod.map id drKeyToVal),
                          (st.rootRoCache, st.advKeys))))))))))))))))

abbrev fgPosTy : Ty pqSig :=
  .sum (.prod (B 32) .bool) (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))
@[simp] def fgPosToVal : FgPoS → fgPosTy.denote
  | .secret z c => .inl (z, c)
  | .pair p1 p2 w1 w2 => .inr (p1, (p2, (w1, w2)))
@[simp] def valToFgPos : fgPosTy.denote → FgPoS
  | .inl (z, c) => .secret z c
  | .inr (p1, (p2, (w1, w2))) => .pair p1 p2 w1 w2
@[simp] theorem valToFgPos_fgPosToVal (x : FgPoS) : valToFgPos (fgPosToVal x) = x := by
  cases x <;> rfl

abbrev fgPatchEntryTy : Ty pqSig :=
  .prod fgPosTy (.prod fgPosTy (.prod fgPosTy (.prod (.opt fgPosTy) (.prod (B 32) drKeyTy))))
@[simp] def fgPatchEntryToVal (e : FgPatchEntry) : fgPatchEntryTy.denote :=
  (fgPosToVal e.pos1, (fgPosToVal e.pos2,
    (fgPosToVal e.pos3, (e.pos4?.map fgPosToVal, (e.ss, drKeyToVal e.dk)))))
@[simp] def valToFgPatchEntry (v : fgPatchEntryTy.denote) : FgPatchEntry :=
  ⟨valToFgPos v.1, valToFgPos v.2.1, valToFgPos v.2.2.1,
    v.2.2.2.1.map valToFgPos, v.2.2.2.2.1, valToDrKey v.2.2.2.2.2⟩
def fgPatchEntryIso : ValIso FgPatchEntry fgPatchEntryTy :=
  ⟨fgPatchEntryToVal, valToFgPatchEntry, by
    intro ⟨p1, p2, p3, p4, ss, dk⟩
    cases p4 <;> simp only [fgPatchEntryToVal, valToFgPatchEntry, Option.map,
      valToFgPos_fgPosToVal, valToDrKey_drKeyToVal]⟩

/-! ## Expression and Computation Shorthands -/

end SignalPqxdh.Security.ReductionDsl

namespace ReductionDsl.Expr

open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl

variable {Γ : List (Ty pqSig)} {τ σ : Ty pqSig}

@[reducible] def litUnit : Expr pqxdhOps Γ .unit := .unit
@[reducible] def litBool (b : Bool) : Expr pqxdhOps Γ .bool := .bool b
@[reducible] def litNat (n : ℕ) : Expr pqxdhOps Γ .nat := .nat n
@[reducible] def noneE : Expr pqxdhOps Γ (.opt τ) := .none
@[reducible] def someE (a : Expr pqxdhOps Γ τ) : Expr pqxdhOps Γ (.opt τ) := .some a
@[reducible] def boolNot (a : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool := .not a
@[reducible] def boolAnd (a b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool := .and a b
@[reducible] def boolOr (a b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool := .ite a (.bool true) b

@[reducible] def listNil : Expr pqxdhOps Γ (.list τ) := .nil
@[reducible] def listCons (x : Expr pqxdhOps Γ τ) (l : Expr pqxdhOps Γ (.list τ)) :
    Expr pqxdhOps Γ (.list τ) := .cons x l
@[reducible] def findBounded (K : ℕ) (l : Expr pqxdhOps Γ (.list τ))
    (p : Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ (.opt τ) := .findB K l p
@[reducible] def anyBounded (K : ℕ) (l : Expr pqxdhOps Γ (.list τ))
    (p : Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ .bool := .anyB K l p
@[reducible] def mapBounded (K : ℕ) (l : Expr pqxdhOps Γ (.list τ))
    (f : Expr pqxdhOps (τ :: Γ) σ) : Expr pqxdhOps Γ (.list σ) := .mapB K l f

def litBytes (w : ℕ+) (bs : Bytes) : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.lit w bs)) .unit
def bytesAppend {m n : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) (b : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B n)) :
    Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B (m + n)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.cat m n)) (.pair a b)
def bytesCons {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B (w + 1)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.cons b w)) a
def bytesWiden (w d : ℕ+) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B (w + d)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.widen w d)) a
def bytesTakeK {w : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B k) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.takeK w k)) a
def bytesDrop {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.drop w)) (.pair n a)
def bytesLen {w : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) : Expr pqxdhOps Γ .nat :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.len w)) a
def bytesBeq {m n : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) (b : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B n)) :
    Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.eq m n)) (.pair a b)
def bytesVarint (n : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 10) :=
  Expr.op (O := pqxdhOps) (Sum.inl BOp.varint) n

def u32OfNat (n : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ SignalPqxdh.LegacyCosted.U32 :=
  Expr.op (O := pqxdhOps) (Sum.inr UOp.ofNat) n
def u32Beq (a b : Expr pqxdhOps Γ SignalPqxdh.LegacyCosted.U32) : Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inr UOp.eq) (.pair a b)

@[simp] theorem eval_litBytes (w : ℕ+) (bs : Bytes) (env : Env Γ) :
    (litBytes w bs).eval env = bs := rfl
@[simp] theorem eval_bytesAppend {m n : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) (b : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B n))
    (env : Env Γ) :
    (bytesAppend a b).eval env = a.eval env ++ b.eval env := rfl
@[simp] theorem eval_bytesCons {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) (env : Env Γ) :
    (bytesCons b a).eval env = b :: a.eval env := rfl
@[simp] theorem eval_bytesWiden (w d : ℕ+) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) (env : Env Γ) :
    (bytesWiden w d a).eval env = a.eval env := rfl
@[simp] theorem eval_bytesTakeK {w : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) (env : Env Γ) :
    (bytesTakeK k a).eval env = (a.eval env).take k := rfl
@[simp] theorem eval_bytesDrop {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w))
    (env : Env Γ) :
    (bytesDrop n a).eval env = (a.eval env).drop (n.eval env) := rfl
@[simp] theorem eval_bytesLen {w : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) (env : Env Γ) :
    (bytesLen a).eval env = (a.eval env).length := rfl
@[simp] theorem eval_bytesBeq {m n : ℕ+} (a : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) (b : Expr pqxdhOps Γ (SignalPqxdh.LegacyCosted.B n))
    (env : Env Γ) :
    (bytesBeq a b).eval env = (a.eval env == b.eval env) := rfl
@[simp] theorem eval_bytesVarint (n : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (bytesVarint n).eval env = pbVarint (n.eval env) := rfl
@[simp] theorem eval_u32OfNat (n : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (u32OfNat n).eval env = UInt32.ofNat (n.eval env) := rfl
@[simp] theorem eval_u32Beq (a b : Expr pqxdhOps Γ SignalPqxdh.LegacyCosted.U32) (env : Env Γ) :
    (u32Beq a b).eval env = (a.eval env == b.eval env) := rfl

end ReductionDsl.Expr

namespace ReductionDsl.Comp

open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
variable {Γ : List (Ty pqSig)} {t u v : Ty pqSig}

def letC (e : Expr pqxdhOps Γ t) (k : Comp pqxdhOps I (t :: Γ) u) : Comp pqxdhOps I Γ u :=
  .bind (.ret e) k

@[simp] theorem eval_letC (e : Expr pqxdhOps Γ t) (k : Comp pqxdhOps I (t :: Γ) u) (env : Env Γ) :
    (letC e k).eval env = k.eval (.cons (e.eval env) env) := by
  simp [letC, Comp.eval]

@[simp] theorem cost_letC (e : Expr pqxdhOps Γ t) (k : Comp pqxdhOps I (t :: Γ) u) :
    (letC e k).cost = e.cost + 1 + k.cost + 1 := rfl

@[simp] theorem costUB_letC (e : Expr pqxdhOps Γ t) (k : Comp pqxdhOps I (t :: Γ) u) :
    (letC e k).costUB = e.costUB + 1 + k.costUB + 1 := rfl

@[simp] theorem queries_letC (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ t) (k : Comp pqxdhOps I (t :: Γ) u) :
    (letC e k).queries w ws = k.queries w ws := by
  simp [letC, Comp.queries]

@[reducible] def iteC (b : Expr pqxdhOps Γ .bool) (c d : Comp pqxdhOps I Γ t) : Comp pqxdhOps I Γ t :=
  .ite b c d
@[reducible] def caseOptC (e : Expr pqxdhOps Γ (.opt t)) (n : Comp pqxdhOps I Γ u)
    (s : Comp pqxdhOps I (t :: Γ) u) : Comp pqxdhOps I Γ u :=
  .caseOpt e n s
@[reducible] def caseSumC (e : Expr pqxdhOps Γ (.sum t u)) (l : Comp pqxdhOps I (t :: Γ) v)
    (r : Comp pqxdhOps I (u :: Γ) v) : Comp pqxdhOps I Γ v :=
  .caseSum e l r
@[reducible] def findBoundedM (K : ℕ) (l : Expr pqxdhOps Γ (.list t))
    (p : Comp pqxdhOps I (t :: Γ) .bool) : Comp pqxdhOps I Γ (.opt t) :=
  .findM K l p
@[reducible] def anyBoundedM (K : ℕ) (l : Expr pqxdhOps Γ (.list t))
    (p : Comp pqxdhOps I (t :: Γ) .bool) : Comp pqxdhOps I Γ .bool :=
  .anyM K l p
@[reducible] def mapBoundedM (K : ℕ) (l : Expr pqxdhOps Γ (.list t))
    (f : Comp pqxdhOps I (t :: Γ) u) : Comp pqxdhOps I Γ (.list u) :=
  .mapM K l f
@[reducible] def foldBoundedM (K : ℕ) (l : Expr pqxdhOps Γ (.list t))
    (z : Expr pqxdhOps Γ u) (f : Comp pqxdhOps I (t :: u :: Γ) u) : Comp pqxdhOps I Γ u :=
  .foldM K l z f

def sampleBool : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ .bool :=
  Comp.sample (I := SignalPqxdh.LegacyCosted.pqPrimIface) PSamp.bool .unit
def sampleBytes32 : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ (SignalPqxdh.LegacyCosted.B 32) :=
  Comp.sample (I := SignalPqxdh.LegacyCosted.pqPrimIface) PSamp.bytes32 .unit
def sampleRandom64 : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ (SignalPqxdh.LegacyCosted.B 64) :=
  Comp.sample (I := SignalPqxdh.LegacyCosted.pqPrimIface) PSamp.random64 .unit
def sampleDrKey96 : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ drKeyTy :=
  Comp.sample (I := SignalPqxdh.LegacyCosted.pqPrimIface) PSamp.drKey96 .unit
def sampleIndex (N : ℕ) : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ .nat :=
  Comp.sample (I := SignalPqxdh.LegacyCosted.pqPrimIface) (PSamp.index N) .unit
def queryPrim (g : SignalPqxdh.LegacyCosted.PTag) (e : Expr pqxdhOps Γ g.dom) : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ g.cod :=
  Comp.query (I := SignalPqxdh.LegacyCosted.pqPrimIface) g e

def sampleBoolC {C : ChallengerOracle} : Comp pqxdhOps (pqChalIface C) Γ .bool :=
  Comp.sample (I := pqChalIface C) PSamp.bool .unit
def sampleBytes32C {C : ChallengerOracle} : Comp pqxdhOps (pqChalIface C) Γ (SignalPqxdh.LegacyCosted.B 32) :=
  Comp.sample (I := pqChalIface C) PSamp.bytes32 .unit
def sampleRandom64C {C : ChallengerOracle} : Comp pqxdhOps (pqChalIface C) Γ (SignalPqxdh.LegacyCosted.B 64) :=
  Comp.sample (I := pqChalIface C) PSamp.random64 .unit
def sampleDrKey96C {C : ChallengerOracle} : Comp pqxdhOps (pqChalIface C) Γ drKeyTy :=
  Comp.sample (I := pqChalIface C) PSamp.drKey96 .unit
def sampleIndexC {C : ChallengerOracle} (N : ℕ) : Comp pqxdhOps (pqChalIface C) Γ .nat :=
  Comp.sample (I := pqChalIface C) (PSamp.index N) .unit
def queryPrimC {C : ChallengerOracle} (g : SignalPqxdh.LegacyCosted.PTag) (e : Expr pqxdhOps Γ g.dom) :
    Comp pqxdhOps (pqChalIface C) Γ g.cod :=
  Comp.query (I := pqChalIface C) (Sum.inl g) e
def queryChal {C : ChallengerOracle} (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    Comp pqxdhOps (pqChalIface C) Γ (C.cod g) :=
  Comp.query (I := pqChalIface C) (Sum.inr g) e

end ReductionDsl.Comp

namespace SignalPqxdh.Security.ReductionDsl

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

theorem potC_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} {B : τ₂.denote → ℕ}
    (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) {n : ℕ}
    (hk : PotOK P B (k.eval (.cons (e.eval env) env)) n) :
    PotOK P B ((Comp.letC e k).eval env) n := by
  rw [Comp.eval_letC]; exact hk

/-! ## Monadic Combinator and Interface Bridges -/

@[simp] theorem id_map' {ι : Type} {T : OracleSpec ι} {α : Type} (mx : OracleComp T α) :
    (fun r => r) <$> mx = mx :=
  id_map mx

@[simp] theorem findML_eq_findMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α), findML p L = findMPrim p L
  | [] => rfl
  | x :: xs => by simp only [findML, findMPrim, findML_eq_findMPrim p xs]

@[simp] theorem anyML_eq_anyMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α), anyML p L = anyMPrim p L
  | [] => rfl
  | x :: xs => by simp only [anyML, anyMPrim, anyML_eq_anyMPrim p xs]

@[simp] theorem mapML_eq_mapMPrim {α β : Type} (f : α → OracleComp PrimBaseSpec β) :
    ∀ (L : List α), mapML f L = mapMPrim f L
  | [] => rfl
  | x :: xs => by simp only [mapML, mapMPrim, mapML_eq_mapMPrim f xs]

@[simp] theorem consumeFirstML_eq_consumeFirstMPrim {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (m : α → α) :
    ∀ (L : List α), consumeFirstML p m L = consumeFirstMPrim p m L
  | [] => rfl
  | x :: xs => by simp only [consumeFirstML, consumeFirstMPrim,
      consumeFirstML_eq_consumeFirstMPrim p m xs]

theorem findML_map {ι : Type} {T : OracleSpec ι} {α β : Type}
    (f : α → β) (p : β → OracleComp T Bool) (L : List α) :
    findML p (L.map f) = Option.map f <$> findML (fun x => p (f x)) L := by
  induction L with
  | nil => simp [findML]
  | cons x xs ih =>
    simp only [List.map_cons, findML, ih, map_bind]
    congr 1; funext b; cases b <;> simp

theorem anyML_map {ι : Type} {T : OracleSpec ι} {α β : Type}
    (f : α → β) (p : β → OracleComp T Bool) (L : List α) :
    anyML p (L.map f) = anyML (fun x => p (f x)) L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, anyML, ih]

theorem findMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    findMPrim p (L.map f) = Option.map f <$> findMPrim (fun x => p (f x)) L := by
  simp only [← findML_eq_findMPrim, findML_map]

theorem anyMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    anyMPrim p (L.map f) = anyMPrim (fun x => p (f x)) L := by
  simp only [← anyML_eq_anyMPrim, anyML_map]

@[simp] theorem pqPrimIface_smp : pqPrimIface.smp = pqSamplers := rfl

@[simp] theorem pqPrimIface_dec (g : PTag) : pqPrimIface.dec g = g.dec := rfl

@[simp] theorem pqPrimIface_enc_query (g : PTag) (x : g.dom.denote) :
    liftM (OracleSpec.query (spec := PrimBaseSpec) (pqPrimIface.enc g x)) =
      primQ (g.enc x) := rfl

@[simp] theorem pqSamplers_run (s : PSamp) (x : (pqSamplers.sDom s).denote) :
    pqSamplers.samp s x = s.run := rfl

@[simp] theorem pqChalIface_smp (C : ChallengerOracle) : (pqChalIface C).smp = pqSamplers := rfl

@[simp] theorem pqChalIface_qCost_inl (C : ChallengerOracle) (g : pqPrimIface.Tag) :
    (pqChalIface C).qCost (.inl g) = pqPrimIface.qCost g := rfl

@[simp] theorem pqPrimIface_liftP {α : Type} (p : ProbComp α) :
    pqPrimIface.liftP p = embedUnif p := rfl

@[simp] theorem pqChalIface_liftP {C : ChallengerOracle} {α : Type} (p : ProbComp α) :
    (pqChalIface C).liftP p = embedPrim (embedUnif p) := by
  rw [← pqPrimIface_liftP]
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    simp only [Iface.liftP, pqChalIface, pqPrimIface, simulateQ_query_bind]
    congr 1; funext u; exact ih u

@[simp] theorem eval_sampleBool {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleBool (Γ := Γ)).eval env = embedUnif ($ᵗ Bool) := rfl

@[simp] theorem eval_sampleBytes32 {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleBytes32 (Γ := Γ)).eval env = embedUnif SignalPqxdh.sampleBytes32 := rfl

@[simp] theorem eval_sampleRandom64 {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleRandom64 (Γ := Γ)).eval env = embedUnif SignalPqxdh.sampleRandom64 := rfl

@[simp] theorem eval_sampleDrKey96 {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleDrKey96 (Γ := Γ)).eval env =
      embedUnif (drKeyV <$> sampleDRKey96) := rfl

@[simp] theorem eval_sampleIndex {Γ : List (Ty pqSig)} (N : ℕ) (env : Env Γ) :
    (Comp.sampleIndex (Γ := Γ) N).eval env = embedUnif (sampleIndexRange N) := rfl

@[simp] theorem eval_queryPrim {Γ : List (Ty pqSig)} (g : PTag)
    (e : Expr pqxdhOps Γ g.dom) (env : Env Γ) :
    (Comp.queryPrim g e).eval env =
      g.dec (e.eval env) <$> primQ (g.enc (e.eval env)) := rfl

@[simp] theorem eval_sampleBoolC {C : ChallengerOracle} {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleBoolC (C := C) (Γ := Γ)).eval env =
      embedPrim (spec := C.spec) (embedUnif ($ᵗ Bool)) :=
  pqChalIface_liftP ($ᵗ Bool)

@[simp] theorem eval_sampleBytes32C {C : ChallengerOracle} {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleBytes32C (C := C) (Γ := Γ)).eval env =
      embedPrim (spec := C.spec) (embedUnif SignalPqxdh.sampleBytes32) :=
  pqChalIface_liftP SignalPqxdh.sampleBytes32

@[simp] theorem eval_sampleRandom64C {C : ChallengerOracle} {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleRandom64C (C := C) (Γ := Γ)).eval env =
      embedPrim (spec := C.spec) (embedUnif SignalPqxdh.sampleRandom64) :=
  pqChalIface_liftP SignalPqxdh.sampleRandom64

@[simp] theorem eval_sampleDrKey96C {C : ChallengerOracle} {Γ : List (Ty pqSig)} (env : Env Γ) :
    (Comp.sampleDrKey96C (C := C) (Γ := Γ)).eval env =
      embedPrim (spec := C.spec) (embedUnif (drKeyV <$> sampleDRKey96)) :=
  pqChalIface_liftP (drKeyV <$> sampleDRKey96)

@[simp] theorem eval_sampleIndexC {C : ChallengerOracle} {Γ : List (Ty pqSig)} (N : ℕ) (env : Env Γ) :
    (Comp.sampleIndexC (C := C) (Γ := Γ) N).eval env =
      embedPrim (spec := C.spec) (embedUnif (sampleIndexRange N)) :=
  pqChalIface_liftP (SignalPqxdh.LegacyCosted.sampleIndex N)

@[simp] theorem eval_queryPrimC {C : ChallengerOracle} {Γ : List (Ty pqSig)} (g : PTag)
    (e : Expr pqxdhOps Γ g.dom) (env : Env Γ) :
    (Comp.queryPrimC (C := C) g e).eval env =
      g.dec (e.eval env) <$>
        liftM (OracleSpec.query (spec := PrimBaseSpec + C.spec)
          (.inl (.inr (g.enc (e.eval env))))) := rfl

@[simp] theorem eval_queryChal {C : ChallengerOracle} {Γ : List (Ty pqSig)} (g : C.Tag)
    (e : Expr pqxdhOps Γ (C.dom g)) (env : Env Γ) :
    (Comp.queryChal (C := C) g e).eval env =
      C.dec g (e.eval env) <$>
        liftM (OracleSpec.query (spec := PrimBaseSpec + C.spec)
          (.inr (C.enc g (e.eval env)))) := rfl

@[simp] theorem embedUnif_map {α β : Type} (f : α → β) (p : ProbComp α) :
    embedUnif (f <$> p) = (embedUnif p >>= fun x => pure (f x)) := by
  unfold embedUnif liftComp
  rw [simulateQ_map, map_eq_bind_pure_comp]
  rfl

@[simp] theorem sampleIndex_eq_sampleIndexRange (N : ℕ) :
    sampleIndex N = sampleIndexRange N := rfl

@[simp] theorem embedPrim_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    embedPrim (spec := spec) (Pure.pure a) = Pure.pure a := rfl

@[simp] theorem embedPrim_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (m : OracleComp PrimBaseSpec α) (k : α → OracleComp PrimBaseSpec β) :
    embedPrim (spec := spec) (m >>= k) =
      embedPrim (spec := spec) m >>= fun a => embedPrim (spec := spec) (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (r u >>= k)) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (r u)) >>= fun a => embedPrim (spec := spec) (k a)
    rw [bind_assoc]
    congr 1; funext u
    exact ih u

@[simp] theorem embedPrim_map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β) (m : OracleComp PrimBaseSpec α) :
    embedPrim (spec := spec) (f <$> m) = f <$> embedPrim (spec := spec) m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, embedPrim_bind]
  rfl

@[simp] theorem embedPrim_findMPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α),
      embedPrim (spec := spec) (findMPrim p L) =
        findML (fun x => embedPrim (spec := spec) (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [findMPrim, findML, embedPrim_bind]
    congr 1; funext b; cases b <;> simp [embedPrim_findMPrim p xs]

@[simp] theorem embedPrim_anyMPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α),
      embedPrim (spec := spec) (anyMPrim p L) =
        anyML (fun x => embedPrim (spec := spec) (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [anyMPrim, anyML, embedPrim_bind]
    congr 1; funext b; cases b <;> simp [embedPrim_anyMPrim p xs]

@[simp] theorem embedPrim_mapMPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → OracleComp PrimBaseSpec β) :
    ∀ (L : List α),
      embedPrim (spec := spec) (mapMPrim f L) =
        mapML (fun x => embedPrim (spec := spec) (f x)) L
  | [] => rfl
  | x :: xs => by
    simp only [mapMPrim, mapML, embedPrim_bind, embedPrim_pure, embedPrim_mapMPrim f xs]

@[simp] theorem embedPrim_consumeFirstMPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (m : α → α) :
    ∀ (L : List α),
      embedPrim (spec := spec) (consumeFirstMPrim p m L) =
        consumeFirstML (fun x => embedPrim (spec := spec) (p x)) m L
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstMPrim, consumeFirstML, embedPrim_bind]
    congr 1; funext b; cases b <;>
      simp [embedPrim_consumeFirstMPrim p m xs]

@[simp] theorem embedPrim_foldML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β → OracleComp PrimBaseSpec β) :
    ∀ (init : β) (L : List α),
      embedPrim (spec := spec) (foldML f init L) =
        foldML (fun x acc => embedPrim (spec := spec) (f x acc)) init L
  | _, [] => rfl
  | init, x :: xs => by
    simp only [foldML, embedPrim_bind]
    congr 1; funext b'; exact embedPrim_foldML f b' xs

@[simp] theorem embedPrim_iterM {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (f : α → OracleComp PrimBaseSpec α) :
    ∀ (n : ℕ) (a : α),
      embedPrim (spec := spec) (iterM f n a) =
        iterM (fun x => embedPrim (spec := spec) (f x)) n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, embedPrim_bind]
    congr 1; funext a'; exact embedPrim_iterM f n a'

end SignalPqxdh.Security.ReductionDsl

namespace ReductionDsl.Comp

open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

/-- Lift a primitive-interface computation `Comp pqxdhOps pqPrimIface Γ t` into any
    challenger interface `Comp pqxdhOps (pqChalIface C) Γ t` with identical cost and
    zero challenger queries. -/
def liftChal {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig} :
    Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t → Comp pqxdhOps (pqChalIface C) Γ t
  | .ret e => .ret e
  | .bind c k => .bind c.liftChal k.liftChal
  | .ite b c d => .ite b c.liftChal d.liftChal
  | .caseOpt e n s => .caseOpt e n.liftChal s.liftChal
  | .caseSum e l r => .caseSum e l.liftChal r.liftChal
  | .sample s e => Comp.sample (I := pqChalIface C) s e
  | .query g e => Comp.query (I := pqChalIface C) (Sum.inl g) e
  | .iter n e body => .iter n e body.liftChal
  | .findM K l p => .findM K l p.liftChal
  | .anyM K l p => .anyM K l p.liftChal
  | .mapM K l f => .mapM K l f.liftChal
  | .consumeFirstM K l p mk => .consumeFirstM K l p.liftChal mk
  | .foldM K l z f => .foldM K l z f.liftChal

@[simp] theorem costUB_liftChal {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) : (c.liftChal (C := C)).costUB = c.costUB := by
  induction c <;> simp [Comp.liftChal, Comp.costUB, *]; rfl

@[simp] theorem queries_liftChal {C : ChallengerOracle}
    (w : (pqChalIface C).Tag → ℕ) (ws : PSamp → ℕ)
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (c.liftChal (C := C)).queries w ws = c.queries (fun g => w (.inl g)) ws := by
  induction c <;> simp [Comp.liftChal, Comp.queries, *]

@[simp] theorem eval_liftChal {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) (env : Env Γ) :
    (c.liftChal (C := C)).eval env = embedPrim (spec := C.spec) (c.eval env) := by
  induction c with
  | ret e => rfl
  | bind c k ihc ihk =>
    simp only [Comp.liftChal, Comp.eval, ihc env, embedPrim_bind]
    congr 1; funext x; exact ihk (.cons x env)
  | ite b c d ihc ihd =>
    simp only [Comp.liftChal, Comp.eval]
    cases b.eval env <;> simp [ihc env, ihd env]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.liftChal, Comp.eval]
    cases e.eval env with
    | none => exact ihn env
    | some x => exact ihs (.cons x env)
  | caseSum e l r ihl ihr =>
    simp only [Comp.liftChal, Comp.eval]
    cases e.eval env with
    | inl x => exact ihl (.cons x env)
    | inr y => exact ihr (.cons y env)
  | sample s e =>
    simp only [Comp.liftChal, Comp.eval, pqChalIface_liftP, pqPrimIface_liftP]
    rfl
  | query g e =>
    simp only [Comp.liftChal, Comp.eval, pqChalIface, SignalPqxdh.LegacyCosted.pqPrimIface, embedPrim_map]
    rfl
  | iter n e body ihb =>
    simp only [Comp.liftChal, Comp.eval, embedPrim_iterM]
    have hFn : (fun a => (body.liftChal (C := C)).eval (.cons a env)) =
        (fun a => embedPrim (spec := C.spec) (body.eval (.cons a env))) := by
      funext a; exact ihb (.cons a env)
    rw [hFn]
  | findM K l p ihp =>
    simp only [Comp.liftChal, Comp.eval, findML_eq_findMPrim, embedPrim_findMPrim]
    have hFn : (fun x => (p.liftChal (C := C)).eval (.cons x env)) =
        (fun x => embedPrim (spec := C.spec) (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | anyM K l p ihp =>
    simp only [Comp.liftChal, Comp.eval, anyML_eq_anyMPrim, embedPrim_anyMPrim]
    have hFn : (fun x => (p.liftChal (C := C)).eval (.cons x env)) =
        (fun x => embedPrim (spec := C.spec) (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | mapM K l f ihf =>
    simp only [Comp.liftChal, Comp.eval, mapML_eq_mapMPrim, embedPrim_mapMPrim]
    have hFn : (fun x => (f.liftChal (C := C)).eval (.cons x env)) =
        (fun x => embedPrim (spec := C.spec) (f.eval (.cons x env))) := by
      funext x; exact ihf (.cons x env)
    rw [hFn]
  | consumeFirstM K l p mk ihp =>
    simp only [Comp.liftChal, Comp.eval,
      consumeFirstML_eq_consumeFirstMPrim, embedPrim_consumeFirstMPrim]
    have hFn : (fun x => (p.liftChal (C := C)).eval (.cons x env)) =
        (fun x => embedPrim (spec := C.spec) (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | foldM K l z f ihf =>
    simp only [Comp.liftChal, Comp.eval, embedPrim_foldML]
    have hFn : (fun x acc => (f.liftChal (C := C)).eval (.cons x (.cons acc env))) =
        (fun x acc => embedPrim (spec := C.spec) (f.eval (.cons x (.cons acc env)))) := by
      funext x acc; exact ihf (.cons x (.cons acc env))
    rw [hFn]

end ReductionDsl.Comp

namespace ReductionDsl

open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

namespace Expr

end Expr

namespace Comp

end Comp

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

/-! ## Bounded Simulation Bridges -/

/-- Simulates an adversary `mx` using `I.fwdU` on coin queries and `step` on game queries. -/
def runWithIfaceStep {ι : Type} {T : OracleSpec ι}
    (I : Iface pqSig T) {κ : Type} {G : OracleSpec κ} {St α : Type}
    (step : (q : κ) → St → OracleComp T (G q × St))
    (mx : OracleComp (unifSpec + G) α) (st : St) :
    OracleComp T (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp T (α × St))
    (fun x st => pure (x, st))
    (fun q _ r st =>
      match q with
      | .inl n => do let u ← I.fwdU n; r u st
      | .inr gq => do let p ← step gq st; r p.1 p.2)
    mx st

theorem simulateQ_handlerImpl_eq_runWithIfaceStep
    {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {κ : Type} {G : OracleSpec κ} {C : GameCodec pqSig G} {σ : Ty pqSig}
    (h : Comp pqxdhOps I [σ, C.Q] (.prod C.R σ))
    {α : Type} (mx : OracleComp (unifSpec + G) α) (st : σ.denote) :
    (simulateQ (handlerImpl (C := C) h) mx).run st =
      runWithIfaceStep I
        (fun q s => do
          let p ← h.eval (.cons s (.cons (C.qenc q) .nil))
          return (C.rdec q p.1, p.2))
        mx st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change ((do let u ← I.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) =
        (I.fwdU uq >>= fun u => runWithIfaceStep I _ (k u) st)
      rw [bind_assoc]
      congr 1; funext u
      rw [pure_bind, ih u st]
    · change ((do
          let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
          return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) =
        ((do
          let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
          return (C.rdec gq p.1, p.2)) >>=
          fun x => runWithIfaceStep I _ (k x.1) x.2)
      congr 1; funext x
      exact ih x.1 x.2

/-! ## Named-Variable Combinators and `Auth` Handler Branches -/

namespace AuthHs

/-- Context extension `Ext Γ Δ`: `Δ` extends `Γ` by finitely many innermost binders. -/
class Ext (Γ Δ : List (Ty pqSig)) where
  wk : {τ : Ty pqSig} → Var Γ τ → Var Δ τ

instance (priority := high) Ext.refl {Γ : List (Ty pqSig)} : Ext Γ Γ := ⟨fun x => x⟩
instance Ext.step {Γ Δ : List (Ty pqSig)} {σ : Ty pqSig} [h : Ext Γ Δ] : Ext Γ (σ :: Δ) :=
  ⟨fun x => .vs (h.wk x)⟩

def v {Γ Δ : List (Ty pqSig)} {τ : Ty pqSig} [h : Ext Γ Δ] (x : Var Γ τ) : Expr pqxdhOps Δ τ :=
  .var (h.wk x)

def bindV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ := .bind m (k .vz)

def letV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ := .letC e (k .vz)

def caseOptV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  .caseOptC o kn (ks .vz)

def caseSumV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) : Comp pqxdhOps I Γ τ :=
  .caseSumC s (kl .vz) (kr .vz)

def findMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ (.opt τ) :=
  .findBoundedM K xs (p .vz)

def anyMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ .bool :=
  .anyBoundedM K xs (p .vz)

def mapMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ (.list τ₂) :=
  .mapBoundedM K xs (f .vz)

def foldMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (z : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ →
      Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    Comp pqxdhOps I Γ τ₂ :=
  .foldBoundedM K xs z (f .vz (.vs .vz))

def eLet {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ τ₂ := .letE e (k .vz)

def eLet2 {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (a : Expr pqxdhOps Γ τ₁) (b : Expr pqxdhOps Γ τ₂)
    (k : Var (τ₁ :: .prod τ₁ τ₂ :: Γ) τ₁ → Var (τ₂ :: τ₁ :: .prod τ₁ τ₂ :: Γ) τ₂ →
      Expr pqxdhOps (τ₂ :: τ₁ :: .prod τ₁ τ₂ :: Γ) τ) :
    Expr pqxdhOps Γ τ :=
  eLet (.pair a b) fun p => eLet (.fst (v p)) fun x => eLet (.snd (v p)) fun y => k x y

def eCaseOpt {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ τ₂ := .caseOpt o kn (ks .vz)

def eCaseSum {Γ : List (Ty pqSig)} {τ₁ τ₂ τ : Ty pqSig}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) : Expr pqxdhOps Γ τ :=
  .caseSum s (kl .vz) (kr .vz)

def eFind {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ (.opt τ) :=
  .findBounded K xs (p .vz)

def eAny {Γ : List (Ty pqSig)} {τ : Ty pqSig} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : Expr pqxdhOps Γ .bool :=
  .anyBounded K xs (p .vz)

def eMap {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ (.list τ₂) :=
  .mapBounded K xs (f .vz)

def natEq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool :=
  .eqN a b

def nat2Eq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.prod .nat .nat)) : Expr pqxdhOps Γ .bool :=
  .boolAnd (natEq (.fst a) (.fst b)) (natEq (.snd a) (.snd b))

def nat3Eq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.prod .nat (.prod .nat .nat))) :
    Expr pqxdhOps Γ .bool :=
  .boolAnd (natEq (.fst a) (.fst b)) (nat2Eq (.snd a) (.snd b))

def optBytesEq {w : ℕ+} {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.opt (B w))) :
    Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseOpt (v a)
    (eCaseOpt (v b) (.litBool true) fun _ => .litBool false)
    fun x => eCaseOpt (v b) (.litBool false) fun y => .bytesBeq (v x) (v y)

def optU32Eq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.opt .u32)) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseOpt (v a)
    (eCaseOpt (v b) (.litBool true) fun _ => .litBool false)
    fun x => eCaseOpt (v b) (.litBool false) fun y => .u32Beq (v x) (v y)

def sidEq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseSum (v a)
    (fun x => eCaseSum (v b) (fun y => nat2Eq (v x) (v y)) fun _ => .litBool false)
    fun a1 => eCaseSum (v a1)
      (fun x => eCaseSum (v b) (fun _ => .litBool false) fun b1 =>
        eCaseSum (v b1) (fun y => nat2Eq (v x) (v y)) fun _ => .litBool false)
      fun a2 => eCaseSum (v a2)
        (fun x => eCaseSum (v b) (fun _ => .litBool false) fun b1 =>
          eCaseSum (v b1) (fun _ => .litBool false) fun b2 =>
            eCaseSum (v b2) (fun y => nat3Eq (v x) (v y)) fun _ => .litBool false)
        fun x => eCaseSum (v b) (fun _ => .litBool false) fun b1 =>
          eCaseSum (v b1) (fun _ => .litBool false) fun b2 =>
            eCaseSum (v b2) (fun _ => .litBool false) fun y => nat3Eq (v x) (v y)

def kyberEq {Γ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) :
    Expr pqxdhOps Γ .bool :=
  .boolAnd (natEq (.fst a) (.fst b))
    (.boolAnd (.u32Beq (.fst (.snd a)) (.fst (.snd b)))
      (.boolAnd (.u32Beq (.fst (.snd (.snd a))) (.fst (.snd (.snd b))))
        (.bytesBeq (.snd (.snd (.snd a))) (.snd (.snd (.snd b))))))

def nonZero32 {Γ : List (Ty pqSig)} (b : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ .bool :=
  .boolNot (.bytesBeq b (.litBytes 32 (List.replicate 32 0)))

def buildSecretsE {Γ : List (Ty pqSig)} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 192) :=
  eLet2 (.pair dh1 (.pair dh2 (.pair dh3 ss))) dh4? fun p d =>
    eCaseOpt (v d)
      (.bytesWiden 160 32
        (.bytesAppend (.bytesAppend (.bytesAppend (.bytesAppend (.litBytes 32 F_X25519)
          (.fst (v p))) (.fst (.snd (v p)))) (.fst (.snd (.snd (v p)))))
          (.snd (.snd (.snd (v p))))))
      fun dh4 => .bytesAppend (.bytesAppend (.bytesAppend (.bytesAppend (.bytesAppend
        (.litBytes 32 F_X25519) (.fst (v p))) (.fst (.snd (v p)))) (.fst (.snd (.snd (v p)))))
        (v dh4)) (.snd (.snd (.snd (v p))))

@[simp] theorem buildSecretsE_eval {Γ : List (Ty pqSig)}
    (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32)))
    (ss : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).eval env =
      buildSecrets (dh1.eval env) (dh2.eval env) (dh3.eval env)
        (dh4?.eval env) (ss.eval env) := by
  unfold buildSecretsE buildSecrets eLet2 eLet eCaseOpt v
  dsimp only [Expr.eval, Env.get, Ext.step, Ext.refl]
  cases dh4?.eval env <;> rfl

def encEC {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 33) :=
  .bytesCons TAG_EC_DJB pk

@[simp] theorem encEC_eval {Γ : List (Ty pqSig)}
    (pk : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (encEC pk).eval env = encodeEC (pk.eval env) := rfl

def encKEM {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 1568)) : Expr pqxdhOps Γ (B 1569) :=
  .bytesCons TAG_KYBER_1024 pk

@[simp] theorem encKEM_eval {Γ : List (Ty pqSig)}
    (pk : Expr pqxdhOps Γ (B 1568)) (env : Env Γ) :
    (encKEM pk).eval env = encodeKEM (pk.eval env) := rfl

/-! ### State and Message Field Accessors -/

@[reducible] def stSecb {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ .bool := .fst e
@[reducible] def stHasWon {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd e)
@[reducible] def stPrin {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) := .fst (.snd (.snd e))
@[reducible] def stSpks {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) := .fst (.snd (.snd (.snd e)))
@[reducible] def stOpks {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) :=
  .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def stSess {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list authSessionEntryTy) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def stUsedS {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list sessionIdTy) := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def stUsedO {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def stUsedN {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
@[reducible] def stKyb {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
@[reducible] def stSOE {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list sentOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))
@[reducible] def stSNE {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list sentNoOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))
@[reducible] def stROE {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list recvdOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))
@[reducible] def stRNE {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list recvdNoOPKEventTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))))
@[reducible] def stRo {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))))
@[reducible] def stRoot {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))))))
@[reducible] def stAdv {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))))))

@[reducible] def stMk {Γ : List (Ty pqSig)}
    (secb : Expr pqxdhOps Γ .bool) (hasWon : Expr pqxdhOps Γ .bool)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)))
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (sess : Expr pqxdhOps Γ (.list authSessionEntryTy))
    (usedS : Expr pqxdhOps Γ (.list sessionIdTy))
    (usedO : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))))
    (usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))))
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (sOE : Expr pqxdhOps Γ (.list sentOPKEventTy))
    (sNE : Expr pqxdhOps Γ (.list sentNoOPKEventTy))
    (rOE : Expr pqxdhOps Γ (.list recvdOPKEventTy))
    (rNE : Expr pqxdhOps Γ (.list recvdNoOPKEventTy))
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)))
    (root : Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))))
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) :
    Expr pqxdhOps Γ authStateTy :=
  .pair secb (.pair hasWon (.pair prin (.pair spks (.pair opks (.pair sess (.pair usedS
    (.pair usedO (.pair usedN (.pair kyb (.pair sOE (.pair sNE (.pair rOE (.pair rNE
      (.pair ro (.pair root adv)))))))))))))))

@[reducible] def stUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authStateTy)
    (secb : Expr pqxdhOps Γ .bool := stSecb e)
    (hasWon : Expr pqxdhOps Γ .bool := stHasWon e)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) := stPrin e)
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) := stSpks e)
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) := stOpks e)
    (sess : Expr pqxdhOps Γ (.list authSessionEntryTy) := stSess e)
    (usedS : Expr pqxdhOps Γ (.list sessionIdTy) := stUsedS e)
    (usedO : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := stUsedO e)
    (usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := stUsedN e)
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) := stKyb e)
    (sOE : Expr pqxdhOps Γ (.list sentOPKEventTy) := stSOE e)
    (sNE : Expr pqxdhOps Γ (.list sentNoOPKEventTy) := stSNE e)
    (rOE : Expr pqxdhOps Γ (.list recvdOPKEventTy) := stROE e)
    (rNE : Expr pqxdhOps Γ (.list recvdNoOPKEventTy) := stRNE e)
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := stRo e)
    (root : Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))) := stRoot e)
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := stAdv e) :
    Expr pqxdhOps Γ authStateTy :=
  stMk secb hasWon prin spks opks sess usedS usedO usedN kyb sOE sNE rOE rNE ro root adv

@[reducible] def seSid {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ sessionIdTy := .fst e
@[reducible] def sePeerIk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def sePeerSpk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def sePeerOpk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (.opt (B 32)) := .fst (.snd (.snd (.snd e)))
@[reducible] def sePeerPqspk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def seSpkHon {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def seOpkHon {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def sePqspkHon {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def seEkASk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
@[reducible] def seEphASk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
@[reducible] def seFresh {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))
@[reducible] def seChal {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ authSessionEntryTy) :
    Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))

@[reducible] def seMk {Γ : List (Ty pqSig)}
    (sid : Expr pqxdhOps Γ sessionIdTy) (peerIk : Expr pqxdhOps Γ (B 32)) (peerSpk : Expr pqxdhOps Γ (B 32))
    (peerOpk : Expr pqxdhOps Γ (.opt (B 32))) (peerPqspk : Expr pqxdhOps Γ (B 1568))
    (spkHon opkHon pqspkHon : Expr pqxdhOps Γ .bool)
    (ekASk ephASk : Expr pqxdhOps Γ (B 32)) (fresh chal : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ authSessionEntryTy :=
  .pair sid (.pair peerIk (.pair peerSpk (.pair peerOpk (.pair peerPqspk (.pair spkHon
    (.pair opkHon (.pair pqspkHon (.pair ekASk (.pair ephASk (.pair fresh chal))))))))))

@[reducible] def pmHdr {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyMsgTy) :
    Expr pqxdhOps Γ handshakeHdrTy := .fst e
@[reducible] def pmEphAPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyMsgTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def pmPqMsg {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyMsgTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def pmAeadCt {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyMsgTy) :
    Expr pqxdhOps Γ (B 32) := .snd (.snd (.snd e))
@[reducible] def pmMk {Γ : List (Ty pqSig)}
    (hdr : Expr pqxdhOps Γ handshakeHdrTy) (ephAPk pqMsg aeadCt : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ preKeyMsgTy :=
  .pair hdr (.pair ephAPk (.pair pqMsg aeadCt))
@[reducible] def pmUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyMsgTy)
    (hdr : Expr pqxdhOps Γ handshakeHdrTy := pmHdr e)
    (ephAPk : Expr pqxdhOps Γ (B 32) := pmEphAPk e)
    (pqMsg : Expr pqxdhOps Γ (B 32) := pmPqMsg e)
    (aeadCt : Expr pqxdhOps Γ (B 32) := pmAeadCt e) :
    Expr pqxdhOps Γ preKeyMsgTy :=
  pmMk hdr ephAPk pqMsg aeadCt

@[reducible] def peSecIKA0 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def peIkAPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def peSecIKAsign {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def peIkSignPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd e)))
@[reducible] def peCorrupted {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy) :
    Expr pqxdhOps Γ .bool := .snd (.snd (.snd (.snd e)))
@[reducible] def peMk {Γ : List (Ty pqSig)}
    (secIKA0 ikAPk secIKAsign ikSignPk : Expr pqxdhOps Γ (B 32)) (corrupted : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ principalEntryTy :=
  .pair secIKA0 (.pair ikAPk (.pair secIKAsign (.pair ikSignPk corrupted)))
@[reducible] def peUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ principalEntryTy)
    (secIKA0 : Expr pqxdhOps Γ (B 32) := peSecIKA0 e)
    (ikAPk : Expr pqxdhOps Γ (B 32) := peIkAPk e)
    (secIKAsign : Expr pqxdhOps Γ (B 32) := peSecIKAsign e)
    (ikSignPk : Expr pqxdhOps Γ (B 32) := peIkSignPk e)
    (corrupted : Expr pqxdhOps Γ .bool := peCorrupted e) :
    Expr pqxdhOps Γ principalEntryTy :=
  peMk secIKA0 ikAPk secIKAsign ikSignPk corrupted

@[reducible] def sbSpkSk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def sbSpkPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def sbSpkSig {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 64) := .fst (.snd (.snd e))
@[reducible] def sbPqspkSk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 3168) := .fst (.snd (.snd (.snd e)))
@[reducible] def sbPqspkPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def sbPqspkSig {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ (B 64) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def sbRevealed {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ spkBundleEntryTy) :
    Expr pqxdhOps Γ .bool := .snd (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def sbMk {Γ : List (Ty pqSig)}
    (spkSk spkPk : Expr pqxdhOps Γ (B 32)) (spkSig : Expr pqxdhOps Γ (B 64))
    (pqspkSk : Expr pqxdhOps Γ (B 3168)) (pqspkPk : Expr pqxdhOps Γ (B 1568))
    (pqspkSig : Expr pqxdhOps Γ (B 64)) (revealed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ spkBundleEntryTy :=
  .pair spkSk (.pair spkPk (.pair spkSig (.pair pqspkSk (.pair pqspkPk (.pair pqspkSig revealed)))))

@[reducible] def oeOpkSk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ opkEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def oeOpkPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ opkEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def oeConsumed {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ opkEntryTy) :
    Expr pqxdhOps Γ .bool := .snd (.snd e)
@[reducible] def oeMk {Γ : List (Ty pqSig)}
    (opkSk opkPk : Expr pqxdhOps Γ (B 32)) (consumed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ opkEntryTy :=
  .pair opkSk (.pair opkPk consumed)
@[reducible] def oeUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ opkEntryTy)
    (opkSk : Expr pqxdhOps Γ (B 32) := oeOpkSk e)
    (opkPk : Expr pqxdhOps Γ (B 32) := oeOpkPk e)
    (consumed : Expr pqxdhOps Γ .bool := oeConsumed e) :
    Expr pqxdhOps Γ opkEntryTy :=
  oeMk opkSk opkPk consumed

@[reducible] def buIkB {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def buSpkId {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ .u32 := .fst (.snd e)
@[reducible] def buSpkB {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def buSpkSig {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (B 64) := .fst (.snd (.snd (.snd e)))
@[reducible] def buOpkB {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (.opt (.prod .u32 (B 32))) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def buPqspkId {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ .u32 := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def buPqspkB {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def buPqspkSig {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy) :
    Expr pqxdhOps Γ (B 64) := .snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def buMk {Γ : List (Ty pqSig)}
    (ikB : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ .u32) (spkB : Expr pqxdhOps Γ (B 32))
    (spkSig : Expr pqxdhOps Γ (B 64)) (opkB : Expr pqxdhOps Γ (.opt (.prod .u32 (B 32))))
    (pqspkId : Expr pqxdhOps Γ .u32) (pqspkB : Expr pqxdhOps Γ (B 1568))
    (pqspkSig : Expr pqxdhOps Γ (B 64)) :
    Expr pqxdhOps Γ preKeyBundleTy :=
  .pair ikB (.pair spkId (.pair spkB (.pair spkSig
    (.pair opkB (.pair pqspkId (.pair pqspkB pqspkSig))))))
@[reducible] def buUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ preKeyBundleTy)
    (ikB : Expr pqxdhOps Γ (B 32) := buIkB e)
    (spkId : Expr pqxdhOps Γ .u32 := buSpkId e)
    (spkB : Expr pqxdhOps Γ (B 32) := buSpkB e)
    (spkSig : Expr pqxdhOps Γ (B 64) := buSpkSig e)
    (opkB : Expr pqxdhOps Γ (.opt (.prod .u32 (B 32))) := buOpkB e)
    (pqspkId : Expr pqxdhOps Γ .u32 := buPqspkId e)
    (pqspkB : Expr pqxdhOps Γ (B 1568) := buPqspkB e)
    (pqspkSig : Expr pqxdhOps Γ (B 64) := buPqspkSig e) :
    Expr pqxdhOps Γ preKeyBundleTy :=
  buMk ikB spkId spkB spkSig opkB pqspkId pqspkB pqspkSig

@[reducible] def hdIkAPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def hdEkAPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def hdSpkId {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ .u32 := .fst (.snd (.snd e))
@[reducible] def hdOpkId {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ (.opt .u32) := .fst (.snd (.snd (.snd e)))
@[reducible] def hdPqspkId {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ .u32 := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def hdKemCt {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy) :
    Expr pqxdhOps Γ (B 1568) := .snd (.snd (.snd (.snd (.snd e))))
@[reducible] def hdMk {Γ : List (Ty pqSig)}
    (ikAPk ekAPk : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ .u32)
    (opkId : Expr pqxdhOps Γ (.opt .u32)) (pqspkId : Expr pqxdhOps Γ .u32)
    (kemCt : Expr pqxdhOps Γ (B 1568)) :
    Expr pqxdhOps Γ handshakeHdrTy :=
  .pair ikAPk (.pair ekAPk (.pair spkId (.pair opkId (.pair pqspkId kemCt))))
@[reducible] def hdUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ handshakeHdrTy)
    (ikAPk : Expr pqxdhOps Γ (B 32) := hdIkAPk e)
    (ekAPk : Expr pqxdhOps Γ (B 32) := hdEkAPk e)
    (spkId : Expr pqxdhOps Γ .u32 := hdSpkId e)
    (opkId : Expr pqxdhOps Γ (.opt .u32) := hdOpkId e)
    (pqspkId : Expr pqxdhOps Γ .u32 := hdPqspkId e)
    (kemCt : Expr pqxdhOps Γ (B 1568) := hdKemCt e) :
    Expr pqxdhOps Γ handshakeHdrTy :=
  hdMk ikAPk ekAPk spkId opkId pqspkId kemCt

def isSomeE {Γ : List (Ty pqSig)} {τ : Ty pqSig} (o : Expr pqxdhOps Γ (.opt τ)) : Expr pqxdhOps Γ .bool :=
  .caseOpt o (.litBool false) (.litBool true)

def getDBytes {w : ℕ+} {Γ : List (Ty pqSig)} (o : Expr pqxdhOps Γ (.opt (B w))) : Expr pqxdhOps Γ (B w) :=
  eCaseOpt o (.litBytes w []) fun x => v x

def optFst {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) : Expr pqxdhOps Γ (.opt τ₁) :=
  eCaseOpt o .noneE fun p => .someE (.fst (v p))

def optSnd {Γ : List (Ty pqSig)} {τ₁ τ₂ : Ty pqSig}
    (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) : Expr pqxdhOps Γ (.opt τ₂) :=
  eCaseOpt o .noneE fun p => .someE (.snd (v p))

def dhOptNZ {Γ : List (Ty pqSig)} (d : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ .bool :=
  eCaseOpt d (.litBool true) fun x => nonZero32 (v x)

def guardE {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    (c : Expr pqxdhOps Γ .bool) (e : Expr pqxdhOps Γ (.opt τ)) : Expr pqxdhOps Γ (.opt τ) :=
  .ite c e .noneE

def kyberCheckE {Γ : List (Ty pqSig)} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) :
    Expr pqxdhOps Γ (.prod .bool (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32)))))) :=
  eLet2 used entry fun u e =>
    .ite (eAny K (v u) fun t => kyberEq (v e) (v t))
      (.pair (.litBool false) (v u))
      (.pair (.litBool true) (.listCons (v e) (v u)))

/-! ### Primitive-Querying Helpers -/

section Helpers

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}

def findHonestC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod .nat principalEntryTy)) :=
  letV ik fun ik =>
    findMV (min K S.N_dh) (stPrin (v st)) fun e =>
      bindV (.queryPrim .pow8 (v ik)) fun p1 =>
        bindV (.queryPrim .pow8 (peIkAPk (.snd (v e)))) fun p2 =>
          .ret (.bytesBeq (v p1) (v p2))

def isAdvRegC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (.queryPrim .pow8 pk) fun p =>
    .ret (eAny K (stAdv (v st)) fun e => .bytesBeq (v p) (.fst (v e)))

def isGameSpkC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (stSpks (v st)) fun e =>
      bindV (.queryPrim .pow8 (sbSpkPk (.snd (v e)))) fun p1 =>
        bindV (.queryPrim .pow8 (v pk)) fun p2 => .ret (.bytesBeq (v p1) (v p2))

def isGameOpkC (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (stOpks (v st)) fun e =>
      bindV (.queryPrim .pow8 (oeOpkPk (.snd (v e)))) fun p1 =>
        bindV (.queryPrim .pow8 (v pk)) fun p2 => .ret (.bytesBeq (v p1) (v p2))

def koskBundleOkC (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (findHonestC S K st (buIkB (v bu))) fun f =>
  bindV (isAdvRegC K st (buIkB (v bu))) fun idA =>
  bindV (isGameSpkC S K st (buSpkB (v bu))) fun spkG =>
  bindV (isAdvRegC K st (buSpkB (v bu))) fun spkA =>
  caseOptV (buOpkB (v bu))
    (.ret (.boolAnd (.boolAnd (.boolOr (isSomeE (v f)) (v idA)) (.boolOr (v spkG) (v spkA)))
      (.litBool true)))
    fun o =>
      bindV (isGameOpkC S K st (.snd (v o))) fun opkG =>
      bindV (isAdvRegC K st (.snd (v o))) fun opkA =>
      .ret (.boolAnd (.boolAnd (.boolOr (isSomeE (v f)) (v idA)) (.boolOr (v spkG) (v spkA)))
        (.boolOr (v opkG) (v opkA)))

def koskSenderOkC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  bindV (isAdvRegC K st (v ik)) fun idA =>
  .ret (.boolOr (isSomeE (v f)) (v idA))

def resolveSigPkC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (B 32) :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  .ret (eCaseOpt (v f) (v ik) fun e => peIkSignPk (.snd (v e)))

def honestPeerC (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (.opt .nat) :=
  bindV (findHonestC S K st ik) fun f =>
  .ret (eCaseOpt (v f) .noneE fun e =>
    .ite (.boolNot (peCorrupted (.snd (v e)))) (.someE (.fst (v e))) .noneE)

def hkdfOrRoC (useRo : Bool) (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    Comp pqxdhOps pqPrimIface Δ (.prod drKeyTy (.list (.prod (B 192) drKeyTy))) :=
  letV sec fun sec =>
  if useRo then
    caseOptV (eFind K (stRo (v st)) fun e => .bytesBeq (.fst (v e)) (v sec))
      (bindV .sampleDrKey96 fun dk =>
        .ret (.pair (v dk) (.listCons (.pair (v sec) (v dk)) (stRo (v st)))))
      fun e => .ret (.pair (.snd (v e)) (stRo (v st)))
  else
    bindV (.queryPrim (.hkdfDerive96 192) (v sec)) fun dk =>
      .ret (.pair (v dk) (stRo (v st)))

end Helpers

def aNone {Γ : List (Ty pqSig)} : Expr pqxdhOps Γ authRespTy := .inl .litUnit
def aInitPrin {Γ : List (Ty pqSig)} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inl (.pair ik s))
def aPk {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inl pk))
def aCorr {Γ : List (Ty pqSig)} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inl (.pair ik s))))
def aBundle {Γ : List (Ty pqSig)} (b : Expr pqxdhOps Γ preKeyBundleTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inl b))))
def aSendFresh {Γ : List (Ty pqSig)} (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inl m)))))
def aSendUnfresh {Γ : List (Ty pqSig)} (dk : Expr pqxdhOps Γ drKeyTy) (rk ck : Expr pqxdhOps Γ (B 32))
    (m : Expr pqxdhOps Γ preKeyMsgTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk (.pair rk (.pair ck m)))))))))
def aRecvHonest {Γ : List (Ty pqSig)} : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl .litUnit)))))))
def aRecvUnfresh {Γ : List (Ty pqSig)} (dk : Expr pqxdhOps Γ drKeyTy) (rk ck pt : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk (.pair rk (.pair ck pt)))))))))))
def aDrKey {Γ : List (Ty pqSig)} (dk : Expr pqxdhOps Γ drKeyTy) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk)))))))))
def aRootKdf {Γ : List (Ty pqSig)} (rk ck : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ authRespTy :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair rk ck)))))))))))

abbrev RS : Ty pqSig := .prod authRespTy authStateTy

def rs {Γ : List (Ty pqSig)} (r : Expr pqxdhOps Γ authRespTy) (st : Expr pqxdhOps Γ authStateTy) :
    Expr pqxdhOps Γ RS := .pair r st

def firstMsgADE {Γ : List (Ty pqSig)} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    Expr pqxdhOps Γ (B 158) :=
  .bytesAppend
    (.bytesAppend
      (.bytesAppend (.bytesAppend (.bytesAppend (encEC ikA) (encEC ikB)) (.litBytes 1 [0x44]))
        (.bytesCons ((8 * 1 + 2 : Nat).toUInt8)
          (.letE (encEC eph) (.bytesAppend (.bytesVarint (.bytesLen (.var .vz))) (.var .vz)))))
      (.litBytes 4 [0x10, 0x00, 0x18, 0x00]))
    (.ite (.eqN (.bytesLen pq) (.litNat 0)) (.litBytes 43 [])
      (.bytesCons ((8 * 5 + 2 : Nat).toUInt8)
        (.bytesAppend (.bytesVarint (.bytesLen pq)) pq)))

theorem firstMsgAD_splitHs (ikA ikB ephAPk pq : Bytes) :
    firstMsgAD ikA ikB ephAPk pq =
      encodeEC ikA ++ encodeEC ikB ++ [0x44] ++
        ((8 * 1 + 2 : Nat).toUInt8 :: (pbVarint (encodeEC ephAPk).length ++ encodeEC ephAPk)) ++
        [0x10, 0x00, 0x18, 0x00] ++
        (if (pq.length == 0) = true then []
         else (8 * 5 + 2 : Nat).toUInt8 :: (pbVarint pq.length ++ pq)) := by
  cases pq <;> rfl

@[simp] theorem firstMsgADE_evalHs {Γ : List (Ty pqSig)}
    (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (firstMsgADE ikA ikB eph pq).eval env =
      firstMsgAD (ikA.eval env) (ikB.eval env) (eph.eval env) (pq.eval env) := by
  rw [firstMsgAD_splitHs]; rfl

def bytes2Eq {w₁ w₂ : ℕ+} {Γ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Γ (.prod (B w₁) (B w₂))) : Expr pqxdhOps Γ .bool :=
  .boolAnd (.bytesBeq (.fst a) (.fst b)) (.bytesBeq (.snd a) (.snd b))

def emptyAuthStE {Γ : List (Ty pqSig)} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ authStateTy :=
  stMk secb (.litBool false) .listNil .listNil .listNil .listNil .listNil .listNil .listNil
    .listNil .listNil .listNil .listNil .listNil .listNil .listNil .listNil

section Helpers2

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}

def rootRoC (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ
      (.prod (.prod (B 32) (B 32)) (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))) :=
  letV (.pair rk dh) fun inp =>
  caseOptV (eFind K (stRoot (v st)) fun e => bytes2Eq (.fst (v e)) (v inp))
    (bindV .sampleBytes32 fun rk1 => bindV .sampleBytes32 fun ck1 =>
      .ret (.pair (.pair (v rk1) (v ck1)) (.listCons (.pair (v inp) (.pair (v rk1) (v ck1)))
        (stRoot (v st)))))
    fun e => .ret (.pair (.snd (v e)) (stRoot (v st)))

end Helpers2

/-! ### `Auth` Handler Branches -/

abbrev sendQTy : Ty pqSig := .prod .nat (.prod .nat (.prod preKeyBundleTy (.prod (B 32) (B 32))))
abbrev recvQTy : Ty pqSig := .prod .nat (.prod .nat (.prod .nat preKeyMsgTy))

section BaseBranches

variable (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

def initPrinB (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun s0 => bindV (.queryPrim .x25519Base (v s0)) fun ik =>
  bindV .sampleBytes32 fun s1 => bindV (.queryPrim .sigPkGen (v s1)) fun sp =>
  .ret (rs (aInitPrin (v ik) (v sp)) (stUpd (v st) (prin := .listCons
    (.pair (v u) (peMk (v s0) (v ik) (v s1) (v sp) (.litBool false))) (stPrin (v st)))))

def corruptB (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs aNone (v st)))
    fun e => .ret (rs (aCorr (peSecIKA0 (.snd (v e))) (peSecIKAsign (.snd (v e))))
      (stUpd (v st) (prin := eMap K (stPrin (v st)) fun x =>
        .ite (natEq (.fst (v x)) (v u))
          (.pair (.fst (v x)) (peUpd (.snd (v x)) (corrupted := .litBool true))) (v x))))

def genSpkB (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (rs aNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs aNone (v st))) fun uE =>
  bindV .sampleBytes32 fun spkSk =>
  bindV (.queryPrim .x25519Base (v spkSk)) fun spkPk =>
  bindV .sampleRandom64 fun r1 =>
  bindV (.queryPrim (.sigSign 33)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV .sampleRandom64 fun seed =>
  bindV (.queryPrim .kemKeyGen (v seed)) fun kp =>
  bindV .sampleRandom64 fun r2 =>
  bindV (.queryPrim (.sigSign 1569) (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (rs (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk) (v sig1)
      .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk) (v spkPk) (v sig1) (.snd (v kp))
      (.fst (v kp)) (v sig2) (.litBool false))) (stSpks (v st)))))

def genOpkB (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (eAny K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v x)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun sk => bindV (.queryPrim .x25519Base (v sk)) fun pk =>
  .ret (rs (aPk (v pk)) (stUpd (v st) (opks := .listCons
    (.pair (v x) (oeMk (v sk) (v pk) (.litBool false))) (stOpks (v st)))))

def registerB (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (.boolNot (natEq (.bytesLen (v sk)) (.litNat 32))) (.ret (rs aNone (v st))) <|
  bindV (.queryPrim .x25519Base (v sk)) fun pk => bindV (.queryPrim .pow8 (v pk)) fun p8 =>
  .ret (rs (aPk (v pk)) (stUpd (v st) (adv := .listCons (.pair (v p8) (v pk)) (stAdv (v st)))))

end BaseBranches

section Branches

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}

def sendC (opk : Bool) (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret (rs aNone (v st))) <|
  .iteC (eAny K (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret (rs aNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs aNone (v st))) fun uE =>
  bindV (findHonestC S K st (buIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (rs aNone (v st))) <|
  letV (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0)) fun pt =>
  bindV (koskBundleOkC S K st bu) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun coins =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  bindV (resolveSigPkC S K st (buIkB (v bu))) fun spk =>
  bindV (.queryPrim (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrim (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (rs aNone (v st))) <|
  bindV (.queryPrim .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (rs aNone (v st))) fun sc =>
  bindV (.queryPrim .x25519Base (v ekSk)) fun ekPk =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (.snd (v uE))) (buSpkB (v bu)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4 =>
  bindV (hkdfOrRoC K true st (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .noneE fun _ => .someE (v dh4)) (.fst (v sc)))) fun dr =>
  bindV (.queryPrim .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrim .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (rootRoC K st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins)))
    fun sp? =>
  caseOptV (v sp?) (.ret (rs aNone (v st))) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrim (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad) (v pt)))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (rs (eCaseOpt (v pp) (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
      (usedS := .listCons (v sid) (stUsedS (v st))) (ro := .snd (v dr)) (root := .snd (v rkOut))))

def sendB (opk : Bool) (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (if opk then .boolNot (isSomeE (buOpkB (.fst (.snd (.snd (v x))))))
      else isSomeE (buOpkB (.fst (.snd (.snd (v x))))))
    (.ret (rs aNone (v st))) (sendC S K opk st x)

def recvTailC (opk : Bool) (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  letV oSk? fun oSk? =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  bindV (.queryPrim .isCanonical (hdEkAPk (v hdr))) fun can =>
  bindV (.queryPrim .isCanonical (pmEphAPk (v msg))) fun canE =>
  letV (kyberCheckE K (stKyb (v st)) (.pair (.fst (v x)) (.pair (hdPqspkId (v hdr))
      (.pair (hdSpkId (v hdr)) (hdEkAPk (v hdr)))))) fun kc =>
  .iteC (.boolOr (.boolOr (.boolNot (.fst (v kc))) (.boolNot (v can))) (.boolNot (v canE)))
    (.ret (rs aNone (v st))) <|
  bindV (.queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (rs aNone (v st))) fun ss =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdIkAPk (v hdr)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdEkAPk (v hdr)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdEkAPk (v hdr)))) fun dh3 =>
  bindV (if opk then
      bindV (.queryPrim .x25519 (.pair (getDBytes (v oSk?)) (hdEkAPk (v hdr)))) fun dh4 =>
        .ret (.someE (v dh4))
    else .ret .noneE) fun dh4? =>
  bindV (hkdfOrRoC K true st (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss))) fun dr =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pmEphAPk (v msg)))) fun dhR =>
  bindV (rootRoC K st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitRecv 32 32) (.pair (.snd (.snd (.fst (v dr)))) (pmPqMsg (v msg))))
    fun sp? =>
  caseOptV (v sp?) (.ret (rs aNone (v st))) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mk =>
  bindV (.queryPrim (.aeadDec 158 32 32)
      (.pair (v mk) (.pair (firstMsgADE (hdIkAPk (v hdr)) (peIkAPk (v kE))
        (pmEphAPk (v msg)) (pmPqMsg (v msg))) (pmAeadCt (v msg))))) fun pt? =>
  caseOptV (v pt?) (.ret (rs aNone (v st))) fun pt =>
  bindV (findHonestC S K st (hdIkAPk (v hdr))) fun snd? =>
  letV (if opk then
      stUpd (v st)
        (opks := eMap K (stOpks (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .litBool true))) (v e))
        (usedO := .listCons (v kjo) (stUsedO (v st)))
        (kyb := .snd (v kc)) (ro := .snd (v dr)) (root := .snd (v rkOut))
    else
      stUpd (v st)
        (usedN := .listCons (v kjo) (stUsedN (v st)))
        (kyb := .snd (v kc)) (ro := .snd (v dr)) (root := .snd (v rkOut))) fun st' =>
  .ret (rs (eCaseOpt (v snd?) (aRecvUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v pt))
      fun _ => aRecvHonest) (v st'))

def recvB (opk : Bool) (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .iteC (.boolNot (.boolAnd (.boolAnd (.boolAnd (.boolAnd (.boolAnd
      (.u32Beq (hdSpkId (v hdr)) (.u32OfNat (.fst (.snd (v x)))))
      (.u32Beq (hdPqspkId (v hdr)) (.u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdOpkId (v hdr))
        (if opk then .someE (.u32OfNat (.fst (.snd (.snd (v x))))) else .noneE)))
      (natEq (.bytesLen (hdIkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (hdEkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (pmEphAPk (v msg))) (.litNat 32))))
    (.ret (rs aNone (v st))) <|
  .iteC (eAny K (if opk then stUsedO (v st) else stUsedN (v st)) fun e => nat3Eq (v e) (v kjo))
    (.ret (rs aNone (v st))) <|
  bindV (koskSenderOkC S K st (hdIkAPk (v hdr))) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (rs aNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs aNone (v st))) fun kE =>
  caseOptV (eFind K (stSpks (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (rs aNone (v st))) fun bE =>
  letV (.snd (v kE)) fun kE' => letV (.snd (v bE)) fun bE' =>
  if opk then
    caseOptV (eFind K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
      (.ret (rs aNone (v st))) fun oE =>
    .iteC (oeConsumed (.snd (v oE))) (.ret (rs aNone (v st))) <|
    recvTailC S K true st x kE' bE' (.someE (oeOpkSk (.snd (v oE))))
  else
    recvTailC S K false st x kE' bE' .noneE

def roB (st : Var Γ₁ authStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  bindV (hkdfOrRoC K true st (v sec)) fun r =>
  .ret (rs (aDrKey (.fst (v r))) (stUpd (v st) (ro := .snd (v r))))

def roRootB (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod (B 32) (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  bindV (rootRoC K st (.fst (v x)) (.snd (v x))) fun r =>
  .ret (rs (aRootKdf (.fst (.fst (v r))) (.snd (.fst (v r)))) (stUpd (v st) (root := .snd (v r))))

end Branches

end AuthHs

end SignalPqxdh.Security.ReductionDsl

