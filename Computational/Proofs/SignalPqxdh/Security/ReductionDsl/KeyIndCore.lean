/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.PqxdhTables
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh

/-!
# Costed DSL Program for the `KeyInd` Game Handler

Defines the `ReductionDsl` encoding of `KeyIndState` and the 14 query-handler branches of
`pqxdhKeyIndImplPrim` with bounded list traversals, shared across the `KeyInd` reduction programs.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

/-! ## Value Encodings for `KeyInd` Game State -/

abbrev PT : Type := Ty pqSig
abbrev sessionIdTy : PT := sidT
abbrev preKeyBundleTy : PT := bundleT
abbrev handshakeHdrTy : PT := hdrT
abbrev drKeyTy : PT := drKeyT
abbrev keyIndQueryTy : PT := keyIndQT
abbrev keyIndRespTy : PT := keyIndRT

@[simp] abbrev sessionIdToVal {S : Setup} : SessionId S → sessionIdTy.denote := sidV
@[simp] abbrev preKeyBundleToVal : PreKeyBundleInput → preKeyBundleTy.denote := bundleV
@[simp] abbrev valToPreKeyBundle : preKeyBundleTy.denote → PreKeyBundleInput := bundleOfV
@[simp] abbrev handshakeHdrToVal : HandshakeHdr → handshakeHdrTy.denote := hdrV
@[simp] abbrev valToHandshakeHdr : handshakeHdrTy.denote → HandshakeHdr := hdrOfV
@[simp] abbrev drKeyToVal : DRKey → drKeyTy.denote := drKeyV
@[simp] abbrev valToDrKey : drKeyTy.denote → DRKey := drKeyOfV
@[simp] abbrev keyIndQueryToVal {S : Setup} : KeyIndQuery S → keyIndQueryTy.denote := keyIndQenc
@[simp] abbrev keyIndRespToVal : KeyIndResponse → keyIndRespTy.denote := keyIndRenc
@[simp] abbrev valToKeyIndResp : keyIndRespTy.denote → KeyIndResponse := keyIndRdec

abbrev principalEntryTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 32) .bool)))

@[simp] def principalEntryToVal (e : PrincipalEntry) : principalEntryTy.denote :=
  (e.secIKA0, (e.ikAPk, (e.secIKAsign, (e.ikSignPk, e.corrupted))))

@[simp] def valToPrincipalEntry (v : principalEntryTy.denote) : PrincipalEntry :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩

abbrev spkBundleEntryTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (B 64) (.prod (B 3168) (.prod (B 1568) (.prod (B 64) .bool)))))

@[simp] def spkBundleEntryToVal (b : SpkBundleEntry) : spkBundleEntryTy.denote :=
  (b.spkSk, (b.spkPk, (b.spkSig, (b.pqspkSk, (b.pqspkPk, (b.pqspkSig, b.revealed))))))

@[simp] def valToSpkBundleEntry (v : spkBundleEntryTy.denote) : SpkBundleEntry :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩

abbrev opkEntryTy : PT := .prod (B 32) (.prod (B 32) .bool)

@[simp] def opkEntryToVal (o : OpkEntry) : opkEntryTy.denote :=
  (o.opkSk, (o.opkPk, o.consumed))

@[simp] def valToOpkEntry (v : opkEntryTy.denote) : OpkEntry :=
  ⟨v.1, v.2.1, v.2.2⟩

abbrev keyIndSessionEntryTy : PT :=
  .prod sidT (.prod (.opt .nat) (.prod (B 32) (.prod (B 32) (.prod (.opt (B 32))
    (.prod (B 1568) (.prod .bool (.prod .bool (.prod .bool (.prod (B 32) (.prod .bool
      (.prod drKeyT (.prod drKeyT (.prod hdrT (.prod .bool .bool))))))))))))))

@[simp] def keyIndSessionEntryToVal {S : Setup} (s : KeyIndInitiatorEntry S) :
    keyIndSessionEntryTy.denote :=
  (sidV s.sid, (s.honestPeer, (s.peerIkPk, (s.peerSpkPk, (s.peerOpkPk?,
    (s.peerPqspkPk, (s.spkHonest, (s.opkHonest, (s.pqspkHonest, (s.ekASk, (s.fresh,
      (drKeyV s.drKeyReal, (drKeyV s.drKeyRand,
        (hdrV s.hdr, (s.tested, s.revealed)))))))))))))))

abbrev keyIndRespEntryTy : PT :=
  .prod sidT (.prod (B 32) (.prod (B 32) (.prod (.opt (B 32)) (.prod (B 1568)
    (.prod hdrT (.prod .bool (.prod drKeyT (.prod drKeyT (.prod .bool .bool)))))))))

@[simp] def keyIndRespEntryToVal {S : Setup} (r : KeyIndRespEntry S) :
    keyIndRespEntryTy.denote :=
  (sidV r.sid, (r.respIkPk, (r.spkPk, (r.opkPk?, (r.pqspkPk,
    (hdrV r.hdr, (r.senderHonest,
      (drKeyV r.drKeyReal, (drKeyV r.drKeyRand, (r.tested, r.revealed))))))))))

abbrev keyIndStateTy : PT :=
  .prod .bool (.prod (.list (.prod .nat principalEntryTy))
    (.prod (.list (.prod (.prod .nat .nat) spkBundleEntryTy))
      (.prod (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy))
        (.prod (.list keyIndSessionEntryTy) (.prod (.list keyIndRespEntryTy)
          (.prod (.list (.prod .nat (.prod .nat .nat)))
            (.prod (.list (.prod .nat (.prod .nat .nat)))
              (.prod (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))
                (.prod (.list (.prod (B 192) drKeyT)) (.list (.prod (B 32) (B 32))))))))))))

@[simp] def keyIndStateToVal {S : Setup} (st : KeyIndState S) : keyIndStateTy.denote :=
  (st.secb, (st.principals.map (Prod.map id principalEntryToVal),
    (st.spkBundles.map (Prod.map id spkBundleEntryToVal),
      (st.opkEntries.map (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal),
        (st.sessions.map keyIndSessionEntryToVal, (st.respSessions.map keyIndRespEntryToVal,
          (st.usedRecvOPK.map (fun (k, j, o) => (k, (j, o))),
            (st.usedRecvNoOPK.map (fun (k, j, l) => (k, (j, l))),
              (st.seenKyberBaseKeys.map (fun (k, p, s, e) => (k, (p, (s, e)))),
                (st.roCache.map (Prod.map id drKeyV), st.advKeys))))))))))

abbrev fgPosTy : PT :=
  .sum (.prod (B 32) .bool) (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))

@[simp] def fgPosToVal : FgPoS → fgPosTy.denote
  | .secret z c => .inl (z, c)
  | .pair p1 p2 w1 w2 => .inr (p1, (p2, (w1, w2)))

abbrev fgPatchEntryTy : PT :=
  .prod fgPosTy (.prod fgPosTy (.prod fgPosTy (.prod (.opt fgPosTy) (.prod (B 32) drKeyT))))

@[simp] def fgPatchEntryToVal (e : FgPatchEntry) : fgPatchEntryTy.denote :=
  (fgPosToVal e.pos1, (fgPosToVal e.pos2,
    (fgPosToVal e.pos3, (e.pos4?.map fgPosToVal, (e.ss, drKeyV e.dk)))))

/-! ## Named-Variable Binder Helpers -/

/-- `Ext Γ Δ`: `Δ` extends `Γ` by finitely many new innermost binders. -/
class Ext (Γ Δ : List PT) where
  wk : {τ : PT} → Var Γ τ → Var Δ τ

instance (priority := high) Ext.refl {Γ : List PT} : Ext Γ Γ := ⟨fun x => x⟩
instance Ext.step {Γ Δ : List PT} {σ : PT} [h : Ext Γ Δ] : Ext Γ (σ :: Δ) :=
  ⟨fun x => .succ (h.wk x)⟩

def v {Γ Δ : List PT} {τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) : Expr pqxdhOps Δ τ := .var (h.wk x)

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}

def bindV {Γ : List PT} {τ₁ τ₂ : PT} (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ := .bind m (k .zero)

def letV {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  .bind (.ret e) (k .zero)

def caseOptV {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ τ₂ :=
  .caseOpt o kn (ks .zero)

def caseSumV {Γ : List PT} {τ₁ τ₂ τ : PT} (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) : Comp pqxdhOps I Γ τ :=
  .caseSum s (kl .zero) (kr .zero)

def findMV {Γ : List PT} {τ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ (.opt τ) :=
  .findM K xs (p .zero)

def anyMV {Γ : List PT} {τ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : Comp pqxdhOps I Γ .bool :=
  .anyM K xs (p .zero)

def mapMV {Γ : List PT} {τ₁ τ₂ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ (.list τ₂) :=
  .mapM K xs (f .zero)

def foldMV {Γ : List PT} {τ₁ τ₂ : PT} (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    Comp pqxdhOps I Γ τ₂ :=
  .foldM K xs init (f .zero (.succ .zero))

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
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : Expr pqxdhOps Γ (.list τ₂) := .mapB K xs (f .zero)

/-! ## `pqxdhOps` Expression Wrappers and `liftBase` -/

def litB (w : ℕ+) (bs : Bytes) {Γ : List PT} : Expr pqxdhOps Γ (B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.lit w bs)) .unit

def catB {m n : ℕ+} {Γ : List PT}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) : Expr pqxdhOps Γ (B (m + n)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.cat m n)) (.pair a b)

def consB {w : ℕ+} {Γ : List PT}
    (b : UInt8) (e : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B (w + 1)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.cons b w)) e

def widenB (w d : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B (w + d)) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.widen w d)) e

def takeKB (w k : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B k) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.takeK w k)) e

def dropB {w : ℕ+} {Γ : List PT}
    (n : Expr pqxdhOps Γ .nat) (e : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.drop w)) (.pair n e)

def lenB {w : ℕ+} {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ .nat :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.len w)) e

def eqB {m n : ℕ+} {Γ : List PT}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) : Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inl (BOp.eq m n)) (.pair a b)

def u32OfNat {Γ : List PT} (e : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ U32 :=
  Expr.op (O := pqxdhOps) (Sum.inr UOp.ofNat) e

def eqU32 {Γ : List PT} (a b : Expr pqxdhOps Γ U32) : Expr pqxdhOps Γ .bool :=
  Expr.op (O := pqxdhOps) (Sum.inr UOp.eq) (.pair a b)

def orE {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ .bool :=
  .ite a (.bool true) b

def mulRight {Γ : List PT} (a : Expr pqxdhOps Γ .nat) (k : ℕ) : Expr pqxdhOps Γ .nat :=
  .mulK k a

def natEq {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool := .eqN a b

def nat2Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat .nat)) : Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b)) (natEq (.snd a) (.snd b))

def nat3Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat (.prod .nat .nat))) : Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b)) (nat2Eq (.snd a) (.snd b))

def optBytesEq {w : ℕ+} {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt (B w))) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseOpt (v a)
    (eCaseOpt (v b) (.bool true) fun _ => .bool false)
    fun x => eCaseOpt (v b) (.bool false) fun y => eqB (v x) (v y)

def optU32Eq {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt U32)) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseOpt (v a)
    (eCaseOpt (v b) (.bool true) fun _ => .bool false)
    fun x => eCaseOpt (v b) (.bool false) fun y => eqU32 (v x) (v y)

def sidEq {Γ : List PT} (a b : Expr pqxdhOps Γ sidT) : Expr pqxdhOps Γ .bool :=
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

def kyberEq {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    Expr pqxdhOps Γ .bool :=
  .and (natEq (.fst a) (.fst b))
    (.and (eqU32 (.fst (.snd a)) (.fst (.snd b)))
      (.and (eqU32 (.fst (.snd (.snd a))) (.fst (.snd (.snd b))))
        (eqB (.snd (.snd (.snd a))) (.snd (.snd (.snd b))))))

def nonZero32 {Γ : List PT} (b : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ .bool :=
  .not (eqB b (litB 32 (List.replicate 32 0)))

def buildSecretsE {Γ : List PT} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32)) (dh4? : Expr pqxdhOps Γ (.opt (B 32)))
    (ss : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 192) :=
  eLet2 (.pair dh1 (.pair dh2 (.pair dh3 ss))) dh4? fun p d =>
    eCaseOpt (v d)
      (widenB 160 32 (catB (catB (catB (catB (litB 32 F_X25519)
        (.fst (v p))) (.fst (.snd (v p)))) (.fst (.snd (.snd (v p)))))
        (.snd (.snd (.snd (v p))))))
      fun dh4 => catB (catB (catB (catB (catB
        (litB 32 F_X25519) (.fst (v p))) (.fst (.snd (v p)))) (.fst (.snd (.snd (v p)))))
        (v dh4)) (.snd (.snd (.snd (v p))))

def encEC {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 33) :=
  consB TAG_EC_DJB pk

def encKEM {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) : Expr pqxdhOps Γ (B 1569) :=
  consB TAG_KYBER_1024 pk

def liftBase {C : ChallengerOracle} {Γ : List PT} {t : PT} :
    Comp pqxdhOps pqPrimIface Γ t → Comp pqxdhOps (pqChalIface C) Γ t
  | .ret e => .ret e
  | .bind c k => .bind (liftBase c) (liftBase k)
  | .ite b c d => .ite b (liftBase c) (liftBase d)
  | .caseOpt e n s => .caseOpt e (liftBase n) (liftBase s)
  | .caseSum e l r => .caseSum e (liftBase l) (liftBase r)
  | .sample s e => Comp.sample (I := pqChalIface C) s e
  | .query g e => Comp.query (I := pqChalIface C) (Sum.inl g) e
  | .iter n e body => .iter n e (liftBase body)
  | .findM K l p => .findM K l (liftBase p)
  | .anyM K l p => .anyM K l (liftBase p)
  | .mapM K l f => .mapM K l (liftBase f)
  | .consumeFirstM K l p mk => .consumeFirstM K l (liftBase p) mk
  | .foldM K l z f => .foldM K l z (liftBase f)

def sBool {Γ : List PT} : Comp pqxdhOps pqPrimIface Γ .bool :=
  Comp.sample (I := pqPrimIface) PSamp.bool .unit
def sBytes32 {Γ : List PT} : Comp pqxdhOps pqPrimIface Γ (B 32) :=
  Comp.sample (I := pqPrimIface) PSamp.bytes32 .unit
def sRandom64 {Γ : List PT} : Comp pqxdhOps pqPrimIface Γ (B 64) :=
  Comp.sample (I := pqPrimIface) PSamp.random64 .unit
def sDrKey96 {Γ : List PT} : Comp pqxdhOps pqPrimIface Γ drKeyT :=
  Comp.sample (I := pqPrimIface) PSamp.drKey96 .unit
def sIndex (N : ℕ) {Γ : List PT} : Comp pqxdhOps pqPrimIface Γ .nat :=
  Comp.sample (I := pqPrimIface) (PSamp.index N) .unit

def qX25519 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    Comp pqxdhOps pqPrimIface Γ (B 32) := Comp.query (I := pqPrimIface) PTag.x25519 e
def qX25519Base {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqPrimIface Γ (B 32) := Comp.query (I := pqPrimIface) PTag.x25519Base e
def qIsCanonical {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqPrimIface Γ .bool := Comp.query (I := pqPrimIface) PTag.isCanonical e
def qPow8 {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqPrimIface Γ (B 32) := Comp.query (I := pqPrimIface) PTag.pow8 e
def qSigPkGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqPrimIface Γ (B 32) := Comp.query (I := pqPrimIface) PTag.sigPkGen e
def qSigSign (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    Comp pqxdhOps pqPrimIface Γ (B 64) := Comp.query (I := pqPrimIface) (PTag.sigSign m) e
def qSigVerify (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    Comp pqxdhOps pqPrimIface Γ .bool := Comp.query (I := pqPrimIface) (PTag.sigVerify m) e
def qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    Comp pqxdhOps pqPrimIface Γ (.prod (B 1568) (B 3168)) :=
  Comp.query (I := pqPrimIface) PTag.kemKeyGen e
def qKemEncaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    Comp pqxdhOps pqPrimIface Γ (.opt (.prod (B 32) (B 1568))) :=
  Comp.query (I := pqPrimIface) PTag.kemEncaps e
def qKemDecaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    Comp pqxdhOps pqPrimIface Γ (.opt (B 32)) := Comp.query (I := pqPrimIface) PTag.kemDecaps e
def qHkdfDerive96 (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) :
    Comp pqxdhOps pqPrimIface Γ drKeyT := Comp.query (I := pqPrimIface) (PTag.hkdfDerive96 w) e

/-! ## Encoding Accessors -/

/-! ### State (`keyIndStateTy`) -/

@[reducible] def stSecb {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) : Expr pqxdhOps Γ .bool := .fst e
@[reducible] def stPrin {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) := .fst (.snd e)
@[reducible] def stSpks {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) := .fst (.snd (.snd e))
@[reducible] def stOpks {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def stSess {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list keyIndSessionEntryTy) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def stResps {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list keyIndRespEntryTy) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def stUsedO {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def stUsedN {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def stKyb {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
@[reducible] def stRo {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 192) drKeyT)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
@[reducible] def stAdv {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy) :
    Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))

@[reducible] def stMk {Γ : List PT}
    (secb : Expr pqxdhOps Γ .bool)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)))
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (sess : Expr pqxdhOps Γ (.list keyIndSessionEntryTy))
    (resps : Expr pqxdhOps Γ (.list keyIndRespEntryTy))
    (usedO : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))))
    (usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))))
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyT)))
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) :
    Expr pqxdhOps Γ keyIndStateTy :=
  .pair secb (.pair prin (.pair spks (.pair opks (.pair sess
    (.pair resps (.pair usedO (.pair usedN (.pair kyb (.pair ro adv)))))))))

@[reducible] def stUpd {Γ : List PT} (e : Expr pqxdhOps Γ keyIndStateTy)
    (secb : Expr pqxdhOps Γ .bool := stSecb e)
    (prin : Expr pqxdhOps Γ (.list (.prod .nat principalEntryTy)) := stPrin e)
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)) := stSpks e)
    (opks : Expr pqxdhOps Γ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)) := stOpks e)
    (sess : Expr pqxdhOps Γ (.list keyIndSessionEntryTy) := stSess e)
    (resps : Expr pqxdhOps Γ (.list keyIndRespEntryTy) := stResps e)
    (usedO : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := stUsedO e)
    (usedN : Expr pqxdhOps Γ (.list (.prod .nat (.prod .nat .nat))) := stUsedN e)
    (kyb : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))) := stKyb e)
    (ro : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyT)) := stRo e)
    (adv : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := stAdv e) :
    Expr pqxdhOps Γ keyIndStateTy :=
  stMk secb prin spks opks sess resps usedO usedN kyb ro adv

/-! ### Principal entry (`principalEntryTy`) -/

@[reducible] def peSecIKA0 {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst e
@[reducible] def peIkAPk {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd e)
@[reducible] def peSecIKAsign {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
@[reducible] def peIkSignPk {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def peCorrupted {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd e)))

@[reducible] def peMk {Γ : List PT}
    (secIKA0 ikAPk secIKAsign ikSignPk : Expr pqxdhOps Γ (B 32)) (corrupted : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ principalEntryTy :=
  .pair secIKA0 (.pair ikAPk (.pair secIKAsign (.pair ikSignPk corrupted)))

@[reducible] def peUpd {Γ : List PT} (e : Expr pqxdhOps Γ principalEntryTy)
    (secIKA0 : Expr pqxdhOps Γ (B 32) := peSecIKA0 e)
    (ikAPk : Expr pqxdhOps Γ (B 32) := peIkAPk e)
    (secIKAsign : Expr pqxdhOps Γ (B 32) := peSecIKAsign e)
    (ikSignPk : Expr pqxdhOps Γ (B 32) := peIkSignPk e)
    (corrupted : Expr pqxdhOps Γ .bool := peCorrupted e) :
    Expr pqxdhOps Γ principalEntryTy :=
  peMk secIKA0 ikAPk secIKAsign ikSignPk corrupted

/-! ### SPK bundle entry (`spkBundleEntryTy`) -/

@[reducible] def sbSpkSk {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst e
@[reducible] def sbSpkPk {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd e)
@[reducible] def sbSpkSig {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 64) :=
  .fst (.snd (.snd e))
@[reducible] def sbPqspkSk {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 3168) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def sbPqspkPk {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def sbPqspkSig {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ (B 64) :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def sbRevealed {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd e)))))

@[reducible] def sbMk {Γ : List PT}
    (spkSk spkPk : Expr pqxdhOps Γ (B 32)) (spkSig : Expr pqxdhOps Γ (B 64))
    (pqspkSk : Expr pqxdhOps Γ (B 3168)) (pqspkPk : Expr pqxdhOps Γ (B 1568))
    (pqspkSig : Expr pqxdhOps Γ (B 64)) (revealed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ spkBundleEntryTy :=
  .pair spkSk (.pair spkPk (.pair spkSig (.pair pqspkSk (.pair pqspkPk (.pair pqspkSig revealed)))))

@[reducible] def sbUpd {Γ : List PT} (e : Expr pqxdhOps Γ spkBundleEntryTy)
    (spkSk : Expr pqxdhOps Γ (B 32) := sbSpkSk e)
    (spkPk : Expr pqxdhOps Γ (B 32) := sbSpkPk e)
    (spkSig : Expr pqxdhOps Γ (B 64) := sbSpkSig e)
    (pqspkSk : Expr pqxdhOps Γ (B 3168) := sbPqspkSk e)
    (pqspkPk : Expr pqxdhOps Γ (B 1568) := sbPqspkPk e)
    (pqspkSig : Expr pqxdhOps Γ (B 64) := sbPqspkSig e)
    (revealed : Expr pqxdhOps Γ .bool := sbRevealed e) :
    Expr pqxdhOps Γ spkBundleEntryTy :=
  sbMk spkSk spkPk spkSig pqspkSk pqspkPk pqspkSig revealed

/-! ### OPK entry (`opkEntryTy`) -/

@[reducible] def oeOpkSk {Γ : List PT} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def oeOpkPk {Γ : List PT} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd e)
@[reducible] def oeConsumed {Γ : List PT} (e : Expr pqxdhOps Γ opkEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd e)

@[reducible] def oeMk {Γ : List PT}
    (opkSk opkPk : Expr pqxdhOps Γ (B 32)) (consumed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ opkEntryTy :=
  .pair opkSk (.pair opkPk consumed)

@[reducible] def oeUpd {Γ : List PT} (e : Expr pqxdhOps Γ opkEntryTy)
    (opkSk : Expr pqxdhOps Γ (B 32) := oeOpkSk e)
    (opkPk : Expr pqxdhOps Γ (B 32) := oeOpkPk e)
    (consumed : Expr pqxdhOps Γ .bool := oeConsumed e) :
    Expr pqxdhOps Γ opkEntryTy :=
  oeMk opkSk opkPk consumed

/-! ### Initiator session entry (`keyIndSessionEntryTy`) -/

@[reducible] def seSid {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) : Expr pqxdhOps Γ sidT :=
  .fst e
@[reducible] def seHonestPeer {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (.opt .nat) := .fst (.snd e)
@[reducible] def sePeerIk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def sePeerSpk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd e)))
@[reducible] def sePeerOpk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (.opt (B 32)) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def sePeerPqspk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def seSpkHon {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def seOpkHon {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def sePqspkHon {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
@[reducible] def seEkASk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
@[reducible] def seFresh {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))
@[reducible] def seDrReal {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))
@[reducible] def seDrRand {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))
@[reducible] def seHdr {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ hdrT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))))))
@[reducible] def seTested {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))))
@[reducible] def seRevealed {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy) :
    Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))))))))

@[reducible] def seMk {Γ : List PT}
    (sid : Expr pqxdhOps Γ sidT) (honestPeer : Expr pqxdhOps Γ (.opt .nat))
    (peerIk peerSpk : Expr pqxdhOps Γ (B 32)) (peerOpk : Expr pqxdhOps Γ (.opt (B 32)))
    (peerPqspk : Expr pqxdhOps Γ (B 1568)) (spkHon opkHon pqspkHon : Expr pqxdhOps Γ .bool)
    (ekASk : Expr pqxdhOps Γ (B 32)) (fresh : Expr pqxdhOps Γ .bool) (drReal drRand : Expr pqxdhOps Γ drKeyT)
    (hdr : Expr pqxdhOps Γ hdrT) (tested revealed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ keyIndSessionEntryTy :=
  .pair sid (.pair honestPeer (.pair peerIk (.pair peerSpk (.pair peerOpk (.pair peerPqspk
    (.pair spkHon (.pair opkHon (.pair pqspkHon (.pair ekASk (.pair fresh (.pair drReal
      (.pair drRand (.pair hdr (.pair tested revealed))))))))))))))

@[reducible] def seUpd {Γ : List PT} (e : Expr pqxdhOps Γ keyIndSessionEntryTy)
    (sid : Expr pqxdhOps Γ sidT := seSid e)
    (honestPeer : Expr pqxdhOps Γ (.opt .nat) := seHonestPeer e)
    (peerIk : Expr pqxdhOps Γ (B 32) := sePeerIk e)
    (peerSpk : Expr pqxdhOps Γ (B 32) := sePeerSpk e)
    (peerOpk : Expr pqxdhOps Γ (.opt (B 32)) := sePeerOpk e)
    (peerPqspk : Expr pqxdhOps Γ (B 1568) := sePeerPqspk e)
    (spkHon : Expr pqxdhOps Γ .bool := seSpkHon e)
    (opkHon : Expr pqxdhOps Γ .bool := seOpkHon e)
    (pqspkHon : Expr pqxdhOps Γ .bool := sePqspkHon e)
    (ekASk : Expr pqxdhOps Γ (B 32) := seEkASk e)
    (fresh : Expr pqxdhOps Γ .bool := seFresh e)
    (drReal : Expr pqxdhOps Γ drKeyT := seDrReal e)
    (drRand : Expr pqxdhOps Γ drKeyT := seDrRand e)
    (hdr : Expr pqxdhOps Γ hdrT := seHdr e)
    (tested : Expr pqxdhOps Γ .bool := seTested e)
    (revealed : Expr pqxdhOps Γ .bool := seRevealed e) :
    Expr pqxdhOps Γ keyIndSessionEntryTy :=
  seMk sid honestPeer peerIk peerSpk peerOpk peerPqspk spkHon opkHon pqspkHon ekASk fresh drReal
    drRand hdr tested revealed

/-! ### Responder session entry (`keyIndRespEntryTy`) -/

@[reducible] def reSid {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ sidT := .fst e
@[reducible] def reRespIk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd e)
@[reducible] def reSpk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
@[reducible] def reOpk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) :
    Expr pqxdhOps Γ (.opt (B 32)) := .fst (.snd (.snd (.snd e)))
@[reducible] def rePqspk {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def reHdr {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ hdrT :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def reSenderHonest {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def reDrReal {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def reDrRand {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ drKeyT :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))))
@[reducible] def reTested {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))
@[reducible] def reRevealed {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy) : Expr pqxdhOps Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))))

@[reducible] def reMk {Γ : List PT}
    (sid : Expr pqxdhOps Γ sidT) (respIk spk : Expr pqxdhOps Γ (B 32)) (opk : Expr pqxdhOps Γ (.opt (B 32)))
    (pqspk : Expr pqxdhOps Γ (B 1568)) (hdr : Expr pqxdhOps Γ hdrT) (senderHonest : Expr pqxdhOps Γ .bool)
    (drReal drRand : Expr pqxdhOps Γ drKeyT) (tested revealed : Expr pqxdhOps Γ .bool) :
    Expr pqxdhOps Γ keyIndRespEntryTy :=
  .pair sid (.pair respIk (.pair spk (.pair opk (.pair pqspk (.pair hdr
    (.pair senderHonest (.pair drReal (.pair drRand (.pair tested revealed)))))))))

@[reducible] def reUpd {Γ : List PT} (e : Expr pqxdhOps Γ keyIndRespEntryTy)
    (sid : Expr pqxdhOps Γ sidT := reSid e)
    (respIk : Expr pqxdhOps Γ (B 32) := reRespIk e)
    (spk : Expr pqxdhOps Γ (B 32) := reSpk e)
    (opk : Expr pqxdhOps Γ (.opt (B 32)) := reOpk e)
    (pqspk : Expr pqxdhOps Γ (B 1568) := rePqspk e)
    (hdr : Expr pqxdhOps Γ hdrT := reHdr e)
    (senderHonest : Expr pqxdhOps Γ .bool := reSenderHonest e)
    (drReal : Expr pqxdhOps Γ drKeyT := reDrReal e)
    (drRand : Expr pqxdhOps Γ drKeyT := reDrRand e)
    (tested : Expr pqxdhOps Γ .bool := reTested e)
    (revealed : Expr pqxdhOps Γ .bool := reRevealed e) :
    Expr pqxdhOps Γ keyIndRespEntryTy :=
  reMk sid respIk spk opk pqspk hdr senderHonest drReal drRand tested revealed

/-! ### Pre-key bundle (`bundleT`) -/

@[reducible] def buIkB {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def buSpkId {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ U32 := .fst (.snd e)
@[reducible] def buSpkB {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
@[reducible] def buSpkSig {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ (B 64) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def buOpkB {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) :
    Expr pqxdhOps Γ (.opt (.prod U32 (B 32))) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def buPqspkId {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ U32 :=
  .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def buPqspkB {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ (B 1568) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def buPqspkSig {Γ : List PT} (e : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ (B 64) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd e))))))

@[reducible] def buMk {Γ : List PT}
    (ikB : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ U32) (spkB : Expr pqxdhOps Γ (B 32))
    (spkSig : Expr pqxdhOps Γ (B 64)) (opkB : Expr pqxdhOps Γ (.opt (.prod U32 (B 32))))
    (pqspkId : Expr pqxdhOps Γ U32) (pqspkB : Expr pqxdhOps Γ (B 1568)) (pqspkSig : Expr pqxdhOps Γ (B 64)) :
    Expr pqxdhOps Γ bundleT :=
  .pair ikB (.pair spkId (.pair spkB (.pair spkSig (.pair opkB (.pair pqspkId
    (.pair pqspkB pqspkSig))))))

/-! ### Handshake header (`hdrT`) -/

@[reducible] def hdIkAPk {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def hdEkAPk {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def hdSpkId {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ U32 :=
  .fst (.snd (.snd e))
@[reducible] def hdOpkId {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ (.opt U32) :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def hdPqspkId {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ U32 :=
  .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def hdKemCt {Γ : List PT} (e : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ (B 1568) :=
  .snd (.snd (.snd (.snd (.snd e))))

@[reducible] def hdMk {Γ : List PT}
    (ikAPk ekAPk : Expr pqxdhOps Γ (B 32)) (spkId : Expr pqxdhOps Γ U32) (opkId : Expr pqxdhOps Γ (.opt U32))
    (pqspkId : Expr pqxdhOps Γ U32) (kemCt : Expr pqxdhOps Γ (B 1568)) :
    Expr pqxdhOps Γ hdrT :=
  .pair ikAPk (.pair ekAPk (.pair spkId (.pair opkId (.pair pqspkId kemCt))))

/-! ### Response constructors (`keyIndRT`) -/

def rNone {Γ : List PT} : Expr pqxdhOps Γ keyIndRT := .inl .unit
def rInitPrin {Γ : List PT} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inl (.pair ik s))
def rPk {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inl pk))
def rCorr {Γ : List PT} (ik s : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inl (.pair ik s))))
def rBundle {Γ : List PT} (b : Expr pqxdhOps Γ bundleT) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inl b))))
def rHdr {Γ : List PT} (h : Expr pqxdhOps Γ hdrT) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inl h)))))
def rInitUnfresh {Γ : List PT} (dk : Expr pqxdhOps Γ drKeyT) (h : Expr pqxdhOps Γ hdrT) :
    Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair dk h)))))))
def rAccFresh {Γ : List PT} : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl .unit)))))))
def rDrKey {Γ : List PT} (dk : Expr pqxdhOps Γ drKeyT) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk))))))))
def rDh {Γ : List PT} (l1 l2 l3 l4 : Expr pqxdhOps Γ (.list (B 32))) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
    (.inl (.pair l1 (.pair l2 (.pair l3 l4))))))))))))
def rSpkSk {Γ : List PT} (sk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ keyIndRT :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk)))))))))

/-! ## Small Expression Helpers -/

def isSomeE {Γ : List PT} {τ : PT} (o : Expr pqxdhOps Γ (.opt τ)) : Expr pqxdhOps Γ .bool :=
  .caseOpt o (.bool false) (.bool true)

def getDBytes {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ (B 32) :=
  eCaseOpt o (litB 32 []) fun x => v x

def optFst {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) :
    Expr pqxdhOps Γ (.opt τ₁) :=
  eCaseOpt o .none fun p => .some (.fst (v p))

def optSnd {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂))) :
    Expr pqxdhOps Γ (.opt τ₂) :=
  eCaseOpt o .none fun p => .some (.snd (v p))

def dhOptNZ {Γ : List PT} (d : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ .bool :=
  eCaseOpt d (.bool true) fun x => nonZero32 (v x)

def guardE {Γ : List PT} {τ : PT} (c : Expr pqxdhOps Γ .bool) (e : Expr pqxdhOps Γ (.opt τ)) :
    Expr pqxdhOps Γ (.opt τ) :=
  .ite c e .none

abbrev RS : PT := .prod keyIndRT keyIndStateTy

def rs {Γ : List PT} (r : Expr pqxdhOps Γ keyIndRT) (st : Expr pqxdhOps Γ keyIndStateTy) : Expr pqxdhOps Γ RS :=
  .pair r st

def kyberCheckE {Γ : List PT} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    Expr pqxdhOps Γ (.prod .bool (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))) :=
  eLet2 used entry fun u e =>
    .ite (eAny K (v u) fun t => kyberEq (v e) (v t))
      (.pair (.bool false) (v u))
      (.pair (.bool true) (.cons (v e) (v u)))

def freshE {Γ : List PT} (K : Nat) (st : Expr pqxdhOps Γ keyIndStateTy) (sid : Expr pqxdhOps Γ sidT) :
    Expr pqxdhOps Γ .bool :=
  eLet2 st sid fun st sid =>
    eCaseOpt (eFind K (stSess (v st)) fun e => sidEq (seSid (v e)) (v sid))
      (eCaseOpt (eFind K (stResps (v st)) fun r => sidEq (reSid (v r)) (v sid)) (.bool false)
        fun r => .and (.and (reSenderHonest (v r)) (.not (reTested (v r))))
          (.not (reRevealed (v r))))
      fun e => .and (.and (seFresh (v e)) (.not (seTested (v e))))
        (.not (seRevealed (v e)))

def emptyStE {Γ : List PT} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ keyIndStateTy :=
  stMk secb .nil .nil .nil .nil .nil .nil .nil .nil .nil .nil

/-! ## Primitive-Querying Helpers -/

section Helpers

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Δ : List PT}

def findHonestC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod .nat principalEntryTy)) :=
  letV ik fun ik =>
    findMV (min K S.N_dh) (stPrin (v st)) fun e =>
      bindV (qPow8 (v ik)) fun p1 =>
        bindV (qPow8 (peIkAPk (.snd (v e)))) fun p2 =>
          .ret (eqB (v p1) (v p2))

def isAdvRegC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (qPow8 pk) fun p =>
    .ret (eAny K (stAdv (v st)) fun e => eqB (v p) (.fst (v e)))

def isGameSpkC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (stSpks (v st)) fun e =>
      bindV (qPow8 (sbSpkPk (.snd (v e)))) fun p1 =>
        bindV (qPow8 (v pk)) fun p2 => .ret (eqB (v p1) (v p2))

def isGameOpkC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV pk fun pk =>
    anyMV (min K S.N_dh) (stOpks (v st)) fun e =>
      bindV (qPow8 (oeOpkPk (.snd (v e)))) fun p1 =>
        bindV (qPow8 (v pk)) fun p2 => .ret (eqB (v p1) (v p2))

def koskBundleOkC (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (findHonestC S K st (buIkB (v bu))) fun f =>
  bindV (isAdvRegC K st (buIkB (v bu))) fun idA =>
  bindV (isGameSpkC S K st (buSpkB (v bu))) fun spkG =>
  bindV (isAdvRegC K st (buSpkB (v bu))) fun spkA =>
  caseOptV (buOpkB (v bu))
    (.ret (.and (.and (orE (isSomeE (v f)) (v idA)) (orE (v spkG) (v spkA)))
      (.bool true)))
    fun o =>
      bindV (isGameOpkC S K st (.snd (v o))) fun opkG =>
      bindV (isAdvRegC K st (.snd (v o))) fun opkA =>
      .ret (.and (.and (orE (isSomeE (v f)) (v idA)) (orE (v spkG) (v spkA)))
        (orE (v opkG) (v opkA)))

def koskSenderOkC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  bindV (isAdvRegC K st (v ik)) fun idA =>
  .ret (orE (isSomeE (v f)) (v idA))

def resolveSigPkC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (B 32) :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  .ret (eCaseOpt (v f) (v ik) fun e => peIkSignPk (.snd (v e)))

def honestPeerC (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ (.opt .nat) :=
  bindV (findHonestC S K st ik) fun f =>
  .ret (eCaseOpt (v f) .none fun e =>
    .ite (.not (peCorrupted (.snd (v e)))) (.some (.fst (v e))) .none)

def checkProvC (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.prod .bool (.prod .bool .bool)) :=
  bindV (findHonestC S K st (buIkB (v bu))) fun f =>
  caseOptV (v f) (.ret (.pair (.bool false) (.pair (.bool false) (.bool false)))) fun kE =>
    bindV (anyMV (min K S.N_dh) (stSpks (v st)) fun e =>
      bindV (qPow8 (sbSpkPk (.snd (v e)))) fun p1 =>
      bindV (qPow8 (buSpkB (v bu))) fun p2 =>
      .ret (.and (natEq (.fst (.fst (v e))) (.fst (v kE))) (eqB (v p1) (v p2))))
    fun spkHon =>
    letV (eAny K (stSpks (v st)) fun e =>
      .and (natEq (.fst (.fst (v e))) (.fst (v kE)))
        (eqB (sbPqspkPk (.snd (v e))) (buPqspkB (v bu)))) fun pqHon =>
    bindV (caseOptV (buOpkB (v bu)) (.ret (.bool false)) fun o =>
      anyMV (min K S.N_dh) (stOpks (v st)) fun e =>
        bindV (qPow8 (oeOpkPk (.snd (v e)))) fun p1 =>
        bindV (qPow8 (.snd (v o))) fun p2 =>
        .ret (.and (natEq (.fst (.fst (v e))) (.fst (v kE))) (eqB (v p1) (v p2))))
    fun opkHon =>
    .ret (.pair (v spkHon) (.pair (v opkHon) (v pqHon)))

def partnerC (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (qPow8 (hdIkAPk (seHdr (v s)))) fun sIk =>
  bindV (qPow8 (hdIkAPk (reHdr (v r)))) fun rIk =>
  bindV (qPow8 (sePeerIk (v s))) fun sPeer =>
  bindV (qPow8 (reRespIk (v r))) fun rResp =>
  bindV (qPow8 (sePeerSpk (v s))) fun sSpk =>
  bindV (qPow8 (reSpk (v r))) fun rSpk =>
  bindV (qPow8 (getDBytes (sePeerOpk (v s)))) fun sOpk =>
  bindV (qPow8 (getDBytes (reOpk (v r)))) fun rOpk =>
  .ret (.and (.and (.and (.and (.and (.and
    (eqB (v sIk) (v rIk)) (eqB (v sPeer) (v rResp))) (eqB (v sSpk) (v rSpk)))
    (optBytesEq (eCaseOpt (sePeerOpk (v s)) .none fun _ => .some (v sOpk))
      (eCaseOpt (reOpk (v r)) .none fun _ => .some (v rOpk))))
    (eqB (hdEkAPk (seHdr (v s))) (hdEkAPk (reHdr (v r)))))
    (eqB (sePeerPqspk (v s)) (rePqspk (v r))))
    (eqB (hdKemCt (seHdr (v s))) (hdKemCt (reHdr (v r)))))

def recordRespC (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    Comp pqxdhOps pqPrimIface Δ keyIndStateTy :=
  letV p fun p => letV (.fst (v p)) fun r =>
  bindV (findMV (min K S.N_dh) (stSess (.snd (v p))) fun s => partnerC s r) fun found =>
  bindV (caseOptV (v found) sDrKey96 fun s => .ret (seDrRand (v s))) fun dr =>
  .ret (stUpd (.snd (v p)) (resps := .cons (reUpd (v r) (drRand := v dr)) (stResps (.snd (v p)))))

def hkdfOrRoC (useRo : Bool) (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    Comp pqxdhOps pqPrimIface Δ (.prod drKeyT (.list (.prod (B 192) drKeyT))) :=
  letV sec fun sec =>
  if useRo then
    caseOptV (eFind K (stRo (v st)) fun e => eqB (.fst (v e)) (v sec))
      (bindV sDrKey96 fun dk =>
        .ret (.pair (v dk) (.cons (.pair (v sec) (v dk)) (stRo (v st)))))
      fun e => .ret (.pair (.snd (v e)) (stRo (v st)))
  else
    bindV (qHkdfDerive96 192 (v sec)) fun dk => .ret (.pair (v dk) (stRo (v st)))

end Helpers

/-- Encoding of `AcceptKeysInput` restricted to its non-constant fields
`(ikBSk, spkBSk, opkBSk?, pqspkBSk, replayOk, hdr)`. -/
abbrev accInpTy : PT :=
  .prod (B 32) (.prod (B 32) (.prod (.opt (B 32)) (.prod (B 3168) (.prod .bool hdrT))))

def aiIkSk {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ (B 32) := .fst e
def aiSpkSk {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ (B 32) := .fst (.snd e)
def aiOpkSk {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ (.opt (B 32)) :=
  .fst (.snd (.snd e))
def aiPqSk {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ (B 3168) :=
  .fst (.snd (.snd (.snd e)))
def aiReplay {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ .bool :=
  .fst (.snd (.snd (.snd (.snd e))))
def aiHdr {Γ : List PT} (e : Expr pqxdhOps Γ accInpTy) : Expr pqxdhOps Γ hdrT :=
  .snd (.snd (.snd (.snd (.snd e))))

def acceptKeysC {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) : Comp pqxdhOps pqPrimIface Δ (.opt drKeyT) :=
  letV inp fun i =>
  bindV (qIsCanonical (hdEkAPk (aiHdr (v i)))) fun canon =>
  bindV (qX25519 (.pair (aiSpkSk (v i)) (hdIkAPk (aiHdr (v i))))) fun dh1 =>
  bindV (qX25519 (.pair (aiIkSk (v i)) (hdEkAPk (aiHdr (v i))))) fun dh2 =>
  bindV (qX25519 (.pair (aiSpkSk (v i)) (hdEkAPk (aiHdr (v i))))) fun dh3 =>
  bindV (qX25519 (.pair (getDBytes (aiOpkSk (v i))) (hdEkAPk (aiHdr (v i))))) fun dh4r =>
  bindV (qKemDecaps (.pair (aiPqSk (v i)) (hdKemCt (aiHdr (v i))))) fun ss =>
  letV (eCaseOpt (hdOpkId (aiHdr (v i)))
      (eCaseOpt (aiOpkSk (v i)) (.some .none) fun _ => .none)
      fun _ => eCaseOpt (aiOpkSk (v i)) .none fun _ => .some (.some (v dh4r))) fun d4 =>
  bindV (qHkdfDerive96 192 (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (v d4) .none fun x => v x) (getDBytes (v ss)))) fun hk =>
  .ret (guardE (.bool true) <| guardE (aiReplay (v i)) <|
    guardE (natEq (lenB (hdIkAPk (aiHdr (v i)))) (.nat 32)) <|
    guardE (natEq (lenB (hdEkAPk (aiHdr (v i)))) (.nat 32)) <|
    guardE (v canon) <| guardE (nonZero32 (v dh1)) <| guardE (nonZero32 (v dh2)) <|
    guardE (nonZero32 (v dh3)) <|
    eCaseOpt (v d4) .none fun d => guardE (dhOptNZ (v d)) <|
      eCaseOpt (v ss) .none fun _ => .some (v hk))

/-! ## `KeyInd` Handler Branches -/

abbrev initQTy : PT := .prod .nat (.prod .nat bundleT)
abbrev accQTy : PT := .prod .nat (.prod .nat (.prod .nat hdrT))

def qK {Γ : List PT} (e : Expr pqxdhOps Γ accQTy) : Expr pqxdhOps Γ .nat := .fst e
def qJ {Γ : List PT} (e : Expr pqxdhOps Γ accQTy) : Expr pqxdhOps Γ .nat := .fst (.snd e)
def qO {Γ : List PT} (e : Expr pqxdhOps Γ accQTy) : Expr pqxdhOps Γ .nat := .fst (.snd (.snd e))
def qHdr {Γ : List PT} (e : Expr pqxdhOps Γ accQTy) : Expr pqxdhOps Γ hdrT := .snd (.snd (.snd e))
def qKJO {Γ : List PT} (e : Expr pqxdhOps Γ accQTy) : Expr pqxdhOps Γ (.prod .nat (.prod .nat .nat)) :=
  .pair (qK e) (.pair (qJ e) (qO e))

section Branches

variable (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

def initPrinB (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs rNone (v st))) <|
  bindV sBytes32 fun s0 => bindV (qX25519Base (v s0)) fun ik =>
  bindV sBytes32 fun s1 => bindV (qSigPkGen (v s1)) fun sp =>
  .ret (rs (rInitPrin (v ik) (v sp)) (stUpd (v st) (prin := .cons
    (.pair (v u) (peMk (v s0) (v ik) (v s1) (v sp) (.bool false))) (stPrin (v st)))))

def corruptB (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs rNone (v st)))
    fun e => .ret (rs (rCorr (peSecIKA0 (.snd (v e))) (peSecIKAsign (.snd (v e))))
      (stUpd (v st) (prin := eMap K (stPrin (v st)) fun x =>
        .ite (natEq (.fst (v x)) (v u))
          (.pair (.fst (v x)) (peUpd (.snd (v x)) (corrupted := .bool true))) (v x))))

def genSpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (rs rNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs rNone (v st))) fun uE =>
  bindV sBytes32 fun spkSk =>
  bindV (qX25519Base (v spkSk)) fun spkPk =>
  bindV sRandom64 fun r1 =>
  bindV (qSigSign 33 (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV sRandom64 fun seed =>
  bindV (qKemKeyGen (v seed)) fun kp =>
  bindV sRandom64 fun r2 =>
  bindV (qSigSign 1569 (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (rs (rBundle (buMk (peIkAPk (.snd (v uE))) (u32OfNat (.snd (v x))) (v spkPk) (v sig1) .none
      (u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (stUpd (v st) (spks := .cons (.pair (v x) (sbMk (v spkSk) (v spkPk) (v sig1) (.snd (v kp))
      (.fst (v kp)) (v sig2) (.bool false))) (stSpks (v st)))))

def genOpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (eAny K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v x)) (.ret (rs rNone (v st))) <|
  bindV sBytes32 fun sk => bindV (qX25519Base (v sk)) fun pk =>
  .ret (rs (rPk (v pk)) (stUpd (v st) (opks := .cons
    (.pair (v x) (oeMk (v sk) (v pk) (.bool false))) (stOpks (v st)))))

def initSidE {Γ : List PT} (opk : Bool) (x : Expr pqxdhOps Γ initQTy) : Expr pqxdhOps Γ sidT :=
  if opk then .inl (.pair (.fst x) (.fst (.snd x)))
  else .inr (.inl (.pair (.fst x) (.fst (.snd x))))

/-- Post-encapsulation continuation of `runKeyIndInitiatePrim`. -/
def initFinishC {Γ₃ Γ₄ Γ₅ Γ₆ : List PT} (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy)) (ekSk : Var Γ₅ (B 32))
    (sc : Var Γ₆ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  bindV (qX25519Base (v ekSk)) fun ekPk =>
  bindV (qX25519 (.pair (peSecIKA0 (.snd (v uE))) (buSpkB (v bu)))) fun dh1 =>
  bindV (qX25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (qX25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (qX25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4r =>
  bindV (hkdfOrRoC K useRo st (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .none fun _ => .some (v dh4r)) (.fst (v sc)))) fun dr =>
  letV (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) fun hdr =>
  bindV (honestPeerC S K st (buIkB (v bu))) fun hp =>
  bindV (checkProvC S K st bu) fun prov =>
  letV (seMk (v sid) (v hp) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu)))
      (buPqspkB (v bu)) (.fst (v prov)) (.fst (.snd (v prov))) (.snd (.snd (v prov))) (v ekSk)
      (isSomeE (v hp)) (.fst (v dr)) (.fst (v dr)) (v hdr) (.bool false) (.bool false)) fun se =>
  bindV (findMV (min K S.N_sess_tot) (stResps (v st)) fun r => partnerC se r) fun found =>
  bindV (caseOptV (v found) sDrKey96 fun r => .ret (reDrRand (v r))) fun drr =>
  bindV (findHonestC S K st (buIkB (v bu))) fun fh =>
  .ret (rs (eCaseOpt (v fh) (rInitUnfresh (.fst (v dr)) (v hdr)) fun _ => rHdr (v hdr))
    (stUpd (v st) (sess := .cons (seUpd (v se) (drRand := v drr)) (stSess (v st)))
      (ro := .snd (v dr))))

def preCheckC {Γ₃ Γ₄ : List PT} (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod .nat principalEntryTy)) :=
  .ite (eAny K (stSess (v st)) fun e => sidEq (seSid (v e)) (v sid)) (.ret .none) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret .none) fun uE =>
  bindV (koskBundleOkC S K st bu) fun ok =>
  .ret (.ite (.not (v ok)) .none (.some (v uE)))

def checkSigsC (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (resolveSigPkC S K st (buIkB (v bu))) fun spk =>
  bindV (qSigVerify 33 (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (qSigVerify 1569 (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .ret (.and (v v1) (v v2))

def initiateC (opk : Bool) (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  letV (.snd (.snd (v x))) fun bu =>
  letV (initSidE opk (v x)) fun sid =>
  .ite (eAny K (stSess (v st)) fun e => sidEq (seSid (v e)) (v sid)) (.ret (rs rNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs rNone (v st))) fun uE =>
  bindV (koskBundleOkC S K st bu) fun ok =>
  .ite (.not (v ok)) (.ret (rs rNone (v st))) <|
  bindV sBytes32 fun ekSk =>
  bindV sBytes32 fun coins =>
  bindV (resolveSigPkC S K st (buIkB (v bu))) fun spk =>
  bindV (qSigVerify 33 (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (qSigVerify 1569 (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (rs rNone (v st))) <|
  bindV (qKemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (rs rNone (v st))) fun sc =>
  initFinishC useRo S K st sid bu uE ekSk sc

def initiateOpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (.not (isSomeE (buOpkB (.snd (.snd (v x)))))) (.ret (rs rNone (v st)))
    (initiateC useRo S K true st x)

def initiateNoOpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (isSomeE (buOpkB (.snd (.snd (v x))))) (.ret (rs rNone (v st)))
    (initiateC useRo S K false st x)

def acceptOpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (.not (.and (.and (.and (.and
      (eqU32 (hdSpkId (qHdr (v x))) (u32OfNat (qJ (v x))))
      (eqU32 (hdPqspkId (qHdr (v x))) (u32OfNat (qJ (v x)))))
      (optU32Eq (hdOpkId (qHdr (v x))) (.some (u32OfNat (qO (v x))))))
      (natEq (lenB (hdIkAPk (qHdr (v x)))) (.nat 32)))
      (natEq (lenB (hdEkAPk (qHdr (v x)))) (.nat 32))))
    (.ret (rs rNone (v st))) <|
  .ite (eAny K (stUsedO (v st)) fun e => nat3Eq (qKJO (v x)) (v e)) (.ret (rs rNone (v st))) <|
  bindV (koskSenderOkC S K st (hdIkAPk (qHdr (v x)))) fun ok =>
  .ite (.not (v ok)) (.ret (rs rNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (qK (v x)))
    (.ret (rs rNone (v st))) fun kE =>
  caseOptV (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
    (.ret (rs rNone (v st))) fun bE =>
  caseOptV (eFind K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (qKJO (v x)))
    (.ret (rs rNone (v st))) fun oE =>
  .ite (oeConsumed (.snd (v oE))) (.ret (rs rNone (v st))) <|
  letV (kyberCheckE K (stKyb (v st)) (.pair (qK (v x)) (.pair (hdPqspkId (qHdr (v x)))
      (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun rk =>
  bindV (acceptKeysC (.pair (peSecIKA0 (.snd (v kE))) (.pair (sbSpkSk (.snd (v bE)))
      (.pair (.some (oeOpkSk (.snd (v oE)))) (.pair (sbPqspkSk (.snd (v bE)))
        (.pair (.fst (v rk)) (qHdr (v x)))))))) fun acc =>
  caseOptV (v acc) (.ret (rs rNone (v st))) fun _ =>
  bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (qHdr (v x))))) fun ss? =>
  caseOptV (v ss?) (.ret (rs rNone (v st))) fun ss =>
  bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdIkAPk (qHdr (v x))))) fun dh1 =>
  bindV (qX25519 (.pair (peSecIKA0 (.snd (v kE))) (hdEkAPk (qHdr (v x))))) fun dh2 =>
  bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdEkAPk (qHdr (v x))))) fun dh3 =>
  bindV (qX25519 (.pair (oeOpkSk (.snd (v oE))) (hdEkAPk (qHdr (v x))))) fun dh4 =>
  bindV (hkdfOrRoC K useRo st (buildSecretsE (v dh1) (v dh2) (v dh3) (.some (v dh4)) (v ss)))
    fun dr =>
  letV (stUpd (v st)
      (opks := eMap K (stOpks (v st)) fun e =>
        .ite (nat3Eq (.fst (v e)) (qKJO (v x)))
          (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e))
      (usedO := .cons (qKJO (v x)) (stUsedO (v st)))
      (kyb := .snd (v rk)) (ro := .snd (v dr))) fun st1 =>
  bindV (findHonestC S K st (hdIkAPk (qHdr (v x)))) fun sh =>
  bindV (recordRespC S K (.pair (reMk (.inr (.inr (.inl (qKJO (v x))))) (peIkAPk (.snd (v kE)))
      (sbSpkPk (.snd (v bE))) (.some (oeOpkPk (.snd (v oE)))) (sbPqspkPk (.snd (v bE))) (qHdr (v x))
      (isSomeE (v sh)) (.fst (v dr)) (.fst (v dr)) (.bool false) (.bool false)) (v st1)))
    fun st2 =>
  bindV (findHonestC S K st (hdIkAPk (qHdr (v x)))) fun sh2 =>
  .ret (rs (eCaseOpt (v sh2) (rDrKey (.fst (v dr))) fun _ => rAccFresh) (v st2))

def acceptNoOpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (.not (.and (.and (.and (.and
      (eqU32 (hdSpkId (qHdr (v x))) (u32OfNat (qJ (v x))))
      (eqU32 (hdPqspkId (qHdr (v x))) (u32OfNat (qJ (v x)))))
      (optU32Eq (hdOpkId (qHdr (v x))) .none))
      (natEq (lenB (hdIkAPk (qHdr (v x)))) (.nat 32)))
      (natEq (lenB (hdEkAPk (qHdr (v x)))) (.nat 32))))
    (.ret (rs rNone (v st))) <|
  .ite (eAny K (stUsedN (v st)) fun e => nat3Eq (qKJO (v x)) (v e)) (.ret (rs rNone (v st))) <|
  bindV (koskSenderOkC S K st (hdIkAPk (qHdr (v x)))) fun ok =>
  .ite (.not (v ok)) (.ret (rs rNone (v st))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (qK (v x)))
    (.ret (rs rNone (v st))) fun kE =>
  caseOptV (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (.pair (qK (v x)) (qJ (v x))))
    (.ret (rs rNone (v st))) fun bE =>
  letV (kyberCheckE K (stKyb (v st)) (.pair (qK (v x)) (.pair (hdPqspkId (qHdr (v x)))
      (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun rk =>
  bindV (acceptKeysC (.pair (peSecIKA0 (.snd (v kE))) (.pair (sbSpkSk (.snd (v bE)))
      (.pair .none (.pair (sbPqspkSk (.snd (v bE)))
        (.pair (.fst (v rk)) (qHdr (v x)))))))) fun acc =>
  caseOptV (v acc) (.ret (rs rNone (v st))) fun _ =>
  bindV (qKemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (qHdr (v x))))) fun ss? =>
  caseOptV (v ss?) (.ret (rs rNone (v st))) fun ss =>
  bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdIkAPk (qHdr (v x))))) fun dh1 =>
  bindV (qX25519 (.pair (peSecIKA0 (.snd (v kE))) (hdEkAPk (qHdr (v x))))) fun dh2 =>
  bindV (qX25519 (.pair (sbSpkSk (.snd (v bE))) (hdEkAPk (qHdr (v x))))) fun dh3 =>
  bindV (hkdfOrRoC K useRo st (buildSecretsE (v dh1) (v dh2) (v dh3) .none (v ss))) fun dr =>
  letV (stUpd (v st) (usedN := .cons (qKJO (v x)) (stUsedN (v st)))
      (kyb := .snd (v rk)) (ro := .snd (v dr))) fun st1 =>
  bindV (findHonestC S K st (hdIkAPk (qHdr (v x)))) fun sh =>
  bindV (recordRespC S K (.pair (reMk (.inr (.inr (.inr (qKJO (v x))))) (peIkAPk (.snd (v kE)))
      (sbSpkPk (.snd (v bE))) .none (sbPqspkPk (.snd (v bE))) (qHdr (v x))
      (isSomeE (v sh)) (.fst (v dr)) (.fst (v dr)) (.bool false) (.bool false)) (v st1)))
    fun st2 =>
  bindV (findHonestC S K st (hdIkAPk (qHdr (v x)))) fun sh2 =>
  .ret (rs (eCaseOpt (v sh2) (rDrKey (.fst (v dr))) fun _ => rAccFresh) (v st2))

def testB (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (.not (freshE K (v st) (v sid))) (.ret (rs rNone (v st))) <|
  caseOptV (eFind K (stSess (v st)) fun e => sidEq (seSid (v e)) (v sid))
    (caseOptV (eFind K (stResps (v st)) fun r => sidEq (reSid (v r)) (v sid))
      (.ret (rs rNone (v st))) fun r =>
      .ret (rs (rDrKey (.ite (stSecb (v st)) (reDrReal (v r)) (reDrRand (v r))))
        (stUpd (v st) (resps := eMap K (stResps (v st)) fun y =>
          .ite (sidEq (reSid (v y)) (v sid)) (reUpd (v y) (tested := .bool true)) (v y)))))
    fun e =>
      .ret (rs (rDrKey (.ite (stSecb (v st)) (seDrReal (v e)) (seDrRand (v e))))
        (stUpd (v st) (sess := eMap K (stSess (v st)) fun y =>
          .ite (sidEq (seSid (v y)) (v sid)) (seUpd (v y) (tested := .bool true)) (v y))))

def revealB (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  caseOptV (eFind K (stSess (v st)) fun e => sidEq (seSid (v e)) (v sid))
    (caseOptV (eFind K (stResps (v st)) fun r => sidEq (reSid (v r)) (v sid))
      (.ret (rs rNone (v st))) fun r =>
      .ite (reTested (v r)) (.ret (rs rNone (v st))) <|
      .ret (rs (rDrKey (reDrReal (v r)))
        (stUpd (v st) (resps := eMap K (stResps (v st)) fun y =>
          .ite (sidEq (reSid (v y)) (v sid)) (reUpd (v y) (revealed := .bool true)) (v y)))))
    fun e =>
      .ite (seTested (v e)) (.ret (rs rNone (v st))) <|
      .ret (rs (rDrKey (seDrReal (v e)))
        (stUpd (v st) (sess := eMap K (stSess (v st)) fun y =>
          .ite (sidEq (seSid (v y)) (v sid)) (seUpd (v y) (revealed := .bool true)) (v y))))

def roB (st : Var Γ₁ keyIndStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  if !useRo then .ret (rs rNone (v st)) else
  bindV (hkdfOrRoC K true st (v sec)) fun r =>
  .ret (rs (rDrKey (.fst (v r))) (stUpd (v st) (ro := .snd (v r))))

def revealDhB (st : Var Γ₁ keyIndStateTy) [Ext Γ₁ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  if useRo then .ret (rs rNone (v st)) else
  .ret (rs (rDh (eMap K (stPrin (v st)) fun e => peSecIKA0 (.snd (v e)))
      (eMap K (stSpks (v st)) fun e => sbSpkSk (.snd (v e)))
      (eMap K (stOpks (v st)) fun e => oeOpkSk (.snd (v e)))
      (eMap K (stSess (v st)) fun e => seEkASk (v e)))
    (v st))

def registerB (st : Var Γ₁ keyIndStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .ite (.not (natEq (lenB (v sk)) (.nat 32))) (.ret (rs rNone (v st))) <|
  bindV (qX25519Base (v sk)) fun pk => bindV (qPow8 (v pk)) fun p8 =>
  .ret (rs (rPk (v pk)) (stUpd (v st) (adv := .cons (.pair (v p8) (v pk)) (stAdv (v st)))))

def revealSpkB (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  caseOptV (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (rs rNone (v st)))
    fun bE => .ret (rs (rSpkSk (sbSpkSk (.snd (v bE))))
      (stUpd (v st) (spks := eMap K (stSpks (v st)) fun e =>
        .ite (nat2Eq (.fst (v e)) (v x))
          (.pair (.fst (v e)) (sbUpd (.snd (v e)) (revealed := .bool true))) (v e))))

end Branches

end SignalPqxdh.Security.ReductionDsl.KeyInd
