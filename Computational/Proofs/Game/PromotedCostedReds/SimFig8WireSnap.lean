/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Atomic `mkPub`, Wire Parsing, and Curve Helpers for `SimFig8`

Defines and verifies `mkPubAtomicC`, `parseRecvAtomicC`, `toWireAtomicE`, and curve/point
admissibility helpers over `atomicSessionOps`, with static query, cost, and `descBits` bounds.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits
  atomicSig atomicSessionOps B U32 U64 BV256 BV512 PK PtT
  AtomicPureOp AtomicGroupOp AtomicPtDecOp AtomicCurveCheckOp
  atomicPtDecOps atomicCurveCheckOps
  lpubT lpubV wireSaltCtT wireSaltCtV fig8CtT fig8CtV salt32V signalParsedT)
open CryptoGames (Party effectiveHkdfSalt32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes paramsV1 serializedPartyAddresses)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (spqrSendAtomicC spqrSendAtomicC_eval spqrSendAtomicC_cost spqrSendAtomicC_queries
   spqrRecvAtomicC spqrRecvAtomicC_eval spqrRecvAtomicC_cost spqrRecvAtomicC_queries)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet eval_eLet cost_eLet descBits_eLet
   sOpPure eval_sOpPure cost_sOpPure descBits_sOpPure
   sOpGrp eval_sOpGrp cost_sOpGrp descBits_sOpGrp
   sOpPtDec eval_sOpPtDec cost_sOpPtDec descBits_sOpPtDec
   sOpCurve eval_sOpCurve cost_sOpCurve descBits_sOpCurve
   bits_zero bits_eq_of_bounds bits_le_of_lt_pow)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
  (spqrSendAtomicC_descBits_le spqrRecvAtomicC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap

/-! ## Semantic helper lemmas -/

theorem spqrSend_panics_guard_eq {β : Type} (F : ShaCompress) (K : MlKem) (pq : Bytes)
    (r : BitVec 512) (f : Bytes × CryptoGames.HKDF.Salt × Bytes → β) :
    (if (spqrV1SessionUniformCoins F K).sendPanics pq r then none
      else ((spqrV1SessionUniformCoins F K).send pq r).map f) =
      ((spqrV1SessionUniformCoins F K).send pq r).map f := by
  by_cases hp : (spqrV1SessionUniformCoins F K).sendPanics pq r = true
  · simp only [hp, ↓reduceIte]
    rcases hs : (spqrV1SessionUniformCoins F K).send pq r with _ | x
    · rfl
    · have h := CryptoVerification.SpqrV1Sync.SendTotal.sendPanics_eq_false_of_isSome F K pq r
        (by rw [hs]; rfl)
      rw [h] at hp; cases hp
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]

theorem salt32V_effectiveHkdfSalt32 (s : CryptoGames.HKDF.Salt) :
    salt32V (effectiveHkdfSalt32 s) =
      (s.map fun v => bytesToKey32 v.toList).getD 0 := by
  rcases s with _ | v
  · rfl
  · rfl

/-! ## `mkPubAtomicC` -/

section MkPub

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def effSaltE {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) : Expr AOps Γ BV256 :=
  .caseOpt s (sOpPure (.bv256Lit 0) .unit) .v0

@[simp] theorem effSaltE_eval {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) (ρ : Env Γ) :
    (effSaltE s).eval ρ = (s.eval ρ).getD 0 := by
  unfold effSaltE
  simp only [Expr.eval]
  cases s.eval ρ <;> rfl

theorem effSaltE_cost {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) :
    (effSaltE s).cost ≤ s.cost + 5 := by
  unfold effSaltE
  simp only [Expr.cost, cost_sOpPure, Expr.v0]
  have : (AtomicPureOp.bv256Lit 0).cost ℓ = 2 := rfl
  omega

def optBytesLitE {Γ : List (Ty ASig)} : Option Bytes → Expr AOps Γ (.opt (B 32))
  | none => .none
  | some v => .some (sOpPure (.bytesLit 32 v) .unit)

@[simp] theorem optBytesLitE_eval {Γ : List (Ty ASig)} (a : Option Bytes) (ρ : Env Γ) :
    (optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) a).eval ρ = a := by
  cases a <;> rfl

theorem optBytesLitE_cost {Γ : List (Ty ASig)} (a : Option Bytes) (n : ℕ)
    (ha : ∀ v, a = some v → v.length ≤ n) :
    (optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) (Γ := Γ) a).cost ≤ n + 34 := by
  cases a with
  | none => simp [optBytesLitE, Expr.cost]
  | some v =>
    have hv := ha v rfl
    simp only [optBytesLitE, Expr.cost, cost_sOpPure]
    have : (AtomicPureOp.bytesLit 32 v).cost ℓ = 32 + v.length := rfl
    omega

/-- Atomic SPQR send step assembling `LibsignalMsgPublicPart` from `(pq, (r, (pn, addrs)))`. -/
def mkPubAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    Comp AOps I' Γ (.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))) :=
  .bind (.ret inpE)
    (.bind (spqrSendAtomicC I' (.pair (.fst .v0) (.fst (.snd .v0))))
      (.ret (.caseOpt .v0 .none
        (.some (.pair (.fst .v0)
          (.pair (.fst (.snd (.snd .v2)))
            (.pair (.snd (.snd .v0))
              (.pair (effSaltE (.fst (.snd .v0))) (.snd (.snd (.snd .v2)))))))))))

theorem mkPubAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (mkPubAtomicC I' inpE).queries w ws = 0 := by
  simp [mkPubAtomicC, Comp.queries, spqrSendAtomicC_queries]

theorem mkPubAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    (mkPubAtomicC I' inpE).cost ≤ inpE.cost + 2144100 := by
  have h1 := spqrSendAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I'
    (Γ := (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))) :: Γ)
    (.pair (.fst .v0) (.fst (.snd .v0)))
  have h2 := effSaltE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.prod (.opt BV256) (B 32))) ::
      (.opt (.prod (B 32) (.prod (.opt BV256) (B 32)))) ::
      (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))) :: Γ)
    (.fst (.snd .v0))
  unfold mkPubAtomicC
  generalize spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ = cs at h1 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v2] at h1 h2 ⊢
  omega

theorem mkPubAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))))
    (ρ : Env Γ) (pq : Bytes) (r : BitVec 512) (pn : BitVec 32) (addr : Option Bytes)
    (hinp : inpE.eval ρ = (pq, (r, (pn, addr)))) (htight : TopStateTight C.F K pq) :
    (mkPubAtomicC I' inpE).eval ρ =
      pure (((spqrV1SessionUniformCoins C.F K).send pq r).map fun x =>
        (x.1, lpubV (ℓ := ℓ) (Pt := Pt) ⟨pn, x.2.2, effectiveHkdfSalt32 x.2.1, addr⟩)) := by
  unfold mkPubAtomicC
  simp only [Comp.eval, pure_bind, hinp]
  rw [spqrSendAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ _ (by simpa [Expr.eval, Expr.v0] using htight)]
  simp only [Expr.eval, Expr.v0, Env.get, pure_bind]
  rw [spqrSend_panics_guard_eq]
  congr 1
  rcases (spqrV1SessionUniformCoins C.F K).send pq r with _ | ⟨pq', salt, msg⟩
  · rfl
  · simp only [Option.map_some, Expr.eval, effSaltE_eval, lpubV, salt32V_effectiveHkdfSalt32]
    rfl

end MkPub

/-! ## `parseRecvAtomicC` -/

theorem parse_take_eq_tryFrom (w : Bytes) (hw : ¬ w.length < 9) :
    (CryptoGames.LibsignalSession.signalWireCodec protoSignalCodec).parse (w.take (w.length - 8)) =
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec w with
      | .ok m => some (m.header, m.ciphertext)
      | .error _ => none := by
  rcases hp : (CryptoGames.LibsignalSession.signalWireCodec protoSignalCodec).parse
      (w.take (w.length - 8)) with _ | ⟨h, body⟩
  · obtain ⟨e, he⟩ := CryptoGames.LibsignalSM.Proofs.Refinement.tryFrom_isError_of_parse_none
      protoSignalCodec w (Or.inr hp)
    rw [he]
  · rw [CryptoGames.LibsignalSM.Proofs.Refinement.tryFrom_of_parse protoSignalCodec w h body hw hp]
    rfl

section ParseRecv

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Output type `(pq', (min (ctr + 1) B, (rk, (decT rk, (ctr + 1, lct)))))` of `parseRecvAtomicC`. -/
@[reducible] def parseOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (B 32) (.prod .nat (.prod PK (.prod (.opt PtT) (.prod .nat (wireSaltCtT (ℓ := ℓ) (Pt := Pt))))))

def parseOutV (x : Bytes × (ℕ × (PublicKey × (Option Pt × (ℕ × LibsignalCiphertextWithSalt32))))) :
    (parseOutT ℓ Pt).denote :=
  (x.1, (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2.1, wireSaltCtV (ℓ := ℓ) (Pt := Pt) x.2.2.2.2.2)))))

def addrCheckE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qB : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) : Expr AOps Γ .bool :=
  .letE (.pair addrs (.ite qB (optBytesLitE (paramsV1 C K idA idB).addrAB)
      (optBytesLitE (paramsV1 C K idA idB).addrBA)))
    (.caseOpt (.fst .v0) (.bool true)
      (.caseOpt (.snd .v1) (.bool false) (sOpPure (.bytesEq 32 32) (.pair .v1 .v0))))

theorem addrCheckE_eval (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qB : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) (ρ : Env Γ) :
    (addrCheckE idA idB qB addrs).eval ρ =
      CryptoGames.LibsignalAead.addressCheckPasses (addrs.eval ρ)
        ((paramsV1 C K idA idB).expectedAddrs (CryptoGames.SM.partyDec (qB.eval ρ))) := by
  unfold addrCheckE
  rcases ha : addrs.eval ρ with _ | a <;> cases hq : qB.eval ρ <;>
    simp [Expr.eval, ha, hq, CryptoGames.LibsignalAead.addressCheckPasses, Expr.v0, Expr.v1,
      CryptoGames.SM.partyDec, CryptoGames.LibsignalSession.Params.expectedAddrs] <;>
    rcases (paramsV1 C K idA idB).addrAB with _ | e <;>
    rcases (paramsV1 C K idA idB).addrBA with _ | e' <;> rfl

theorem addrCheckE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qB : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) :
    (addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qB addrs).cost ≤ qB.cost + addrs.cost + 400 := by
  have hab := optBytesLitE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrAB 128
    (fun v hv => Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B v hv)
  have hba := optBytesLitE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrBA 128
    (fun v hv => Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A v hv)
  have heq : (AtomicPureOp.bytesEq 32 32).cost ℓ = 64 := rfl
  unfold addrCheckE
  generalize optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  simp only [Expr.cost, cost_sOpPure, heq, Expr.v0, Expr.v1]
  omega

def parseBodyE (Bc : ℕ) {Γ : List (Ty ASig)} :
    Expr AOps
      ((.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
        (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
      (parseOutT ℓ Pt) :=
  let w : Expr AOps _ (B 32) := .snd (.snd .v3)
  let n8 : Expr AOps _ .nat := .sub (sOpPure (.bytesLen 32) w) (.nat 8)
  let ctrN : Expr AOps _ .nat := .add (sOpPure .u32ToNat (.fst (.snd (.snd (.fst .v2))))) (.nat 1)
  let rk : Expr AOps _ PK := .fst (.snd (.fst .v2))
  .pair (.fst .v0)
    (.pair (.ite (.lt ctrN (.nat Bc)) ctrN (.nat Bc))
      (.pair rk
        (.pair (sOpPtDec .ptDecPk rk)
          (.pair ctrN
            (.pair
              (.pair (sOpPure (.bytesTake 32) (.pair n8 w))
                (sOpPure .bytesToU64Le
                  (sOpPure (.bytesTakeK 32 8) (sOpPure (.bytesDrop 32) (.pair n8 w)))))
              (effSaltE (.snd .v0)))))))

theorem parseBodyE_cost (Bc : ℕ) {Γ : List (Ty ASig)} :
    (parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ) Bc).cost ≤ 2 * bits Bc + 350 := by
  have hs := effSaltE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
      (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
    (.snd .v0)
  have hb32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb8 : bits 8 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have h8v : ((8 : ℕ+) : ℕ) = 8 := rfl
  unfold parseBodyE
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at hs ⊢
  simp only [Expr.cost, cost_sOpPure, cost_sOpPtDec, AtomicPureOp.cost, h32v, h8v, hb32, hb8, hb1,
    Expr.v0, Expr.v2, Expr.v3] at hs ⊢
  omega

/-- Atomic wire parsing and SPQR receive computation implementing `simParseRecvC` on `(qB, (pq, w))`. -/
def parseRecvAtomicC (idA idB : IdentityKey) (Bc : ℕ) {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    Comp AOps I' Γ (.opt (parseOutT ℓ Pt)) :=
  .bind (.ret inpE)
    (.ite (.lt (sOpPure (.bytesLen 32) (.snd (.snd .v0))) (.nat 9)) (.ret .none)
      (.caseOpt (sOpPure .signalMsgParse (.snd (.snd .v0))) (.ret .none)
        (.ite (.not (addrCheckE idA idB (.fst .v1) (.snd (.snd (.snd .v0))))) (.ret .none)
          (.bind (spqrRecvAtomicC I' (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0)))))
            (.ret (.caseOpt .v0 .none (.some (parseBodyE Bc))))))))

theorem parseRecvAtomicC_queries (idA idB : IdentityKey) (Bc : ℕ) {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32))))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (parseRecvAtomicC idA idB Bc I' inpE).queries w ws = 0 := by
  simp [parseRecvAtomicC, Comp.queries, spqrRecvAtomicC_queries]

theorem parseRecvAtomicC_cost (idA idB : IdentityKey) (Bc : ℕ) {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB Bc I' inpE).cost ≤
      inpE.cost + ℓ / 32 + 2 * bits Bc + 131201200 := by
  let t0 := Ty.prod (S := ASig) .bool (.prod (B 32) (B 32))
  let Γ1 := t0 :: Γ
  let Γ2 := signalParsedT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hac := addrCheckE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (.fst .v1) (.snd (.snd (.snd .v0)))
  have hspqr := spqrRecvAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0))))
  have hbody := parseBodyE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb9 : bits 9 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  unfold parseRecvAtomicC
  generalize addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ _ = eac at hac ⊢
  generalize spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) _ = cspqr at hspqr ⊢
  generalize parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc = ebody at hbody ⊢
  simp only [Comp.cost, Expr.cost, cost_sOpPure, AtomicPureOp.cost, h32v, hb32, hb9,
    Expr.v0, Expr.v1] at hac hspqr hbody ⊢
  omega

private theorem ite_lt_eq_min' (a b : ℕ) : (if decide (a < b) = true then a else b) = min a b := by
  by_cases h : a < b
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)]

omit [DecidableEq Pt] [Zero Pt] in
private theorem signalMsgParse_eval' (body : Bytes) :
    AtomicPureOp.eval ℓ Pt .signalMsgParse body =
      match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
      | .ok m => some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
          (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none :=
  Computational.Proofs.ReductionDsl.Fig8Atomic.atomicPureOps_eval_signalMsgParse_lossless ℓ Pt body

private theorem tag_take8_eq (w : Bytes) (hw : ¬ w.length < 9) :
    ReductionDsl.bytesToWordLE 64 ((w.drop (w.length - 8)).take 8) =
      CryptoGames.HMAC.bytesToWord64LE (w.drop (w.length - 8)) := by
  rw [List.take_of_length_le (by simp; omega)]
  rfl

theorem parseRecvAtomicC_eval (idA idB : IdentityKey) (Bc : ℕ) {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) (ρ : Env Γ)
    (qB : Bool) (pq w : Bytes) (hinp : inpE.eval ρ = (qB, (pq, w)))
    (htight : TopStateTight C.F K pq) :
    (parseRecvAtomicC idA idB Bc I' inpE).eval ρ =
      pure ((CryptoGames.Ratchet.LibsignalSim.simParseRecvC (paramsV1 C K idA idB) decT Bc qB pq w).map
        (parseOutV (ℓ := ℓ) (Pt := Pt))) := by
  unfold parseRecvAtomicC CryptoGames.Ratchet.LibsignalSim.simParseRecvC
  simp only [Comp.eval, pure_bind, hinp, Expr.eval, Expr.v0, Env.get, eval_sOpPure]
  have hlenEval : AtomicPureOp.eval ℓ Pt (.bytesLen 32) w = w.length := rfl
  rw [hlenEval]
  by_cases hlen : w.length < 9
  · simp [hlen]
  · simp only [hlen, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
    rw [hcodec, parse_take_eq_tryFrom w hlen, signalMsgParse_eval']
    rcases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec w with e | m
    · rfl
    · simp only [addrCheckE_eval, Expr.eval, Expr.v1, Env.get,
        CryptoGames.LibsignalSession.SignalMessage.header]
      by_cases haddr : CryptoGames.LibsignalAead.addressCheckPasses m.addresses
          ((paramsV1 C K idA idB).expectedAddrs (CryptoGames.SM.partyDec qB)) = true
      · simp only [haddr, Bool.not_true, Bool.false_eq_true, Bool.false_or, ↓reduceIte]
        rw [spqrRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) I' _ _ (by simpa [Expr.eval, Expr.v0, Expr.v1] using htight)]
        simp only [Expr.eval, Env.get, pure_bind]
        have hspqrEq : (paramsV1 C K idA idB).spqr = spqrV1SessionUniformCoins C.F K := rfl
        rw [hspqrEq]
        by_cases hp : (spqrV1SessionUniformCoins C.F K).recvPanics pq m.pqRatchet = true
        · simp [hp]
        · simp only [hp, Bool.false_eq_true, ↓reduceIte]
          rcases hrec : (spqrV1SessionUniformCoins C.F K).recv pq m.pqRatchet with
            err | ⟨pq', salt⟩
          · rfl
          · simp only [Option.map_some, parseBodyE, parseOutV, wireSaltCtV,
              Expr.eval, eval_sOpPure, eval_sOpPtDec, effSaltE_eval,
              Expr.v0, Expr.v2, Expr.v3, Env.get]
            congr 1
            congr 1
            change (pq',
              ((if decide (m.counter.toNat + 1 < Bc) = true then m.counter.toNat + 1 else Bc),
                (m.senderRatchetKey, (decT m.senderRatchetKey, (m.counter.toNat + 1,
                  ((w.take (w.length - 8),
                    ReductionDsl.bytesToWordLE 64 ((w.drop (w.length - 8)).take 8)),
                  (salt.map fun v => bytesToKey32 v.toList).getD 0)))))) = _
            rw [ite_lt_eq_min', tag_take8_eq w hlen, ← salt32V_effectiveHkdfSalt32]
      · simp [haddr]

end ParseRecv

/-! ## Wire serialization and curve checks -/

theorem toLEBytes8_eq_tagBytes (t : BitVec 64) :
    ReductionDsl.toLEBytes 8 t = CryptoGames.Ratchet.LibsignalSim.tagBytes t := by
  refine List.ext_getElem
    (by simp [ReductionDsl.toLEBytes, CryptoGames.Ratchet.LibsignalSim.tagBytes]) fun j h1 h2 => ?_
  simp only [ReductionDsl.toLEBytes, CryptoGames.Ratchet.LibsignalSim.tagBytes,
    List.getElem_ofFn, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [BitVec.getLsbD_ushiftRight, hk, Nat.add_comm]

section WireAndCurve

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def toWireAtomicE {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ (B 32) :=
  eLet (.fst (.snd (.snd cE)))
    (sOpPure .bytesAppend8 (.pair (.fst .v0) (sOpPure .u64LeBytes (.snd .v0))))

theorem toWireAtomicE_eval {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (c : CryptoGames.Ratchet.LibsignalSim.Fig8C Pt) (hc : cE.eval ρ = fig8CtV c) :
    (toWireAtomicE cE).eval ρ = CryptoGames.Ratchet.LibsignalSim.toWire c := by
  unfold toWireAtomicE CryptoGames.Ratchet.LibsignalSim.toWire
  rw [eval_eLet]
  have h1 : (Expr.fst (.snd (.snd cE))).eval ρ = c.2.2.1 := by
    simp [Expr.eval, hc, fig8CtV, ReductionDsl.lctV, wireSaltCtV]
  rw [h1]
  simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, Expr.v0, Env.get_cons_zero]
  rw [List.take_of_length_le (Nat.le_of_eq (Computational.Proofs.ReductionDsl.Fig8Atomic.toLEBytes8_length _)),
    toLEBytes8_eq_tagBytes]

theorem toWireAtomicE_cost {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + 20 := by
  unfold toWireAtomicE
  simp only [cost_eLet, Expr.cost, cost_sOpPure, AtomicPureOp.cost, Expr.v0]
  omega

def ratchetKeyAdmissibleAtomicE {Γ : List (Ty ASig)}
    (wE : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sOpCurve .checkRatchetKeyOnCurve wE

@[simp] theorem ratchetKeyAdmissibleAtomicE_eval {Γ : List (Ty ASig)}
    (wE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (ratchetKeyAdmissibleAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) wE).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (wE.eval ρ) := rfl

theorem ratchetKeyAdmissibleAtomicE_cost {Γ : List (Ty ASig)}
    (wE : Expr AOps Γ (B 32)) :
    (ratchetKeyAdmissibleAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) wE).cost ≤ wE.cost + ℓ / 32 + 24 := by
  unfold ratchetKeyAdmissibleAtomicE
  simp only [cost_sOpCurve, atomicCurveCheckOps]
  omega

def isZeroPtOptAtomicE {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) : Expr AOps Γ .bool :=
  .caseOpt tOptE (.bool false) (sOpGrp .ptIsZero .v0)

theorem isZeroPtOptAtomicE_eval {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) (ρ : Env Γ) :
    (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tOptE).eval ρ = (tOptE.eval ρ == some 0) := by
  unfold isZeroPtOptAtomicE
  rcases h : tOptE.eval ρ with _ | x
  · simp [Expr.eval, h]
  · simp only [Expr.eval, h, eval_sOpGrp, AtomicGroupOp.eval, Expr.v0, Env.get_cons_zero]
    by_cases hx : x = 0 <;> simp [hx]

theorem isZeroPtOptAtomicE_cost {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) :
    (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tOptE).cost ≤ tOptE.cost + 5 := by
  unfold isZeroPtOptAtomicE
  simp only [Expr.cost, cost_sOpGrp, AtomicGroupOp.cost, Expr.v0]
  omega

end WireAndCurve

/-! ## Syntactic `descBits` bounds -/

section DescBits

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "SDesc" =>
  atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

theorem effSaltE_descBits_le {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) :
    atomicExprDescBits SDesc (effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) s) ≤
      atomicExprDescBits SDesc s + 310 := by
  have hb0 : bits 0 = 1 := bits_zero
  simp only [effSaltE, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits,
    Expr.v0, varIdx, hb0]
  omega

theorem optBytesLitE_descBits_le {Γ : List (Ty ASig)} (a : Option Bytes)
    (ha : ∀ v, a = some v → v.length ≤ 128) :
    atomicExprDescBits SDesc
      (optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ) a) ≤ 1100 := by
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by
    rw [h32v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  cases a with
  | none =>
    simp only [optBytesLitE, B, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, hb32]
    omega
  | some v =>
    have hv := ha v rfl
    have hbv : bits v.length ≤ 8 := bits_le_of_lt_pow (by omega) (by omega)
    simp only [optBytesLitE, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits, hb32]
    omega

theorem mkPubAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    atomicCompDescBits SDesc sB qB
      (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' inpE) ≤
      atomicExprDescBits SDesc inpE + 26000 := by
  let t0 := Ty.prod (S := ASig) (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))
  let tRes := Ty.prod (S := ASig) (B 32) (.prod (.opt BV256) (B 32))
  have h1 := spqrSendAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' sB qB (Γ := t0 :: Γ)
    (.pair (.fst .v0) (.fst (.snd .v0)))
  have h2 := effSaltE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := tRes :: (.opt tRes) :: t0 :: Γ) (.fst (.snd .v0))
  have hb0 : bits 0 = 1 := bits_zero
  have hb2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by
    rw [h32v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  unfold mkPubAtomicC
  generalize spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ = cs at h1 ⊢
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at h2 ⊢
  simp only [atomicCompDescBits, atomicExprDescBits, B, U32, BV256,
    atomicTyDescBits, atomicSortDescBits, Expr.v0, Expr.v2, varIdx, Nat.reduceAdd,
    hb0, hb2, hb32] at h1 h2 ⊢
  omega

theorem addrCheckE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qB : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) :
    atomicExprDescBits SDesc
      (addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qB addrs) ≤
      atomicExprDescBits SDesc qB + atomicExprDescBits SDesc addrs + 2400 := by
  have hab := optBytesLitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrAB
    (fun v hv => Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B v hv)
  have hba := optBytesLitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrBA
    (fun v hv => Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A v hv)
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by
    rw [h32v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  unfold addrCheckE
  generalize optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  simp only [atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits,
    Expr.v0, Expr.v1, varIdx, Nat.reduceAdd, hb0, hb1, hb32]
  omega

theorem parseBodyE_descBits_le (Bc : ℕ) {Γ : List (Ty ASig)} :
    atomicExprDescBits SDesc
      (parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc) ≤ 4 * bits Bc + 1200 := by
  have hs := effSaltE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
      (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
    (.snd .v0)
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb8 : bits 8 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h8v : ((8 : ℕ+) : ℕ) = 8 := rfl
  have hb8p : bits ((8 : ℕ+) : ℕ) = 4 := by
    rw [h8v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by
    rw [h32v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  unfold parseBodyE
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at hs ⊢
  simp only [atomicExprDescBits, descBits_sOpPure, descBits_sOpPtDec, atomicPureOpDescBits,
    Expr.v0, Expr.v2, Expr.v3, varIdx, Nat.reduceAdd, hb0, hb1, hb2, hb3, hb8, hb8p, hb32] at hs ⊢
  omega

theorem parseRecvAtomicC_descBits_le (idA idB : IdentityKey) (Bc : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    atomicCompDescBits SDesc sB qB
      (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB Bc I' inpE) ≤
      atomicExprDescBits SDesc inpE + 4 * bits Bc + 95000 := by
  let t0 := Ty.prod (S := ASig) .bool (.prod (B 32) (B 32))
  let Γ1 := t0 :: Γ
  let Γ2 := signalParsedT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hac := addrCheckE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (.fst .v1) (.snd (.snd (.snd .v0)))
  have hspqr := spqrRecvAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' sB qB (Γ := Γ2)
    (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0))))
  have hbody := parseBodyE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb9 : bits 9 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have h32v : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by
    rw [h32v]; exact bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  unfold parseRecvAtomicC
  generalize addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ _ = eac at hac ⊢
  generalize spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) _ = cspqr at hspqr ⊢
  generalize parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc = ebody at hbody ⊢
  simp only [atomicCompDescBits, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits,
    parseOutT, wireSaltCtT, B, U64, BV256, PK, PtT, atomicTyDescBits, atomicSortDescBits,
    Expr.v0, Expr.v1, varIdx, Nat.reduceAdd, hb0, hb1, hb9, hb32] at hac hspqr hbody ⊢
  omega

theorem toWireAtomicE_descBits_le {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits SDesc
      (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) cE) ≤
      atomicExprDescBits SDesc cE + 120 := by
  have hb0 : bits 0 = 1 := bits_zero
  simp only [toWireAtomicE, descBits_eLet, atomicExprDescBits, descBits_sOpPure,
    atomicPureOpDescBits, Expr.v0, varIdx, hb0]
  omega

theorem ratchetKeyAdmissibleAtomicE_descBits_le {Γ : List (Ty ASig)}
    (wE : Expr AOps Γ (B 32)) :
    atomicExprDescBits SDesc
      (ratchetKeyAdmissibleAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) wE) ≤
      atomicExprDescBits SDesc wE + 30 := by
  simp only [ratchetKeyAdmissibleAtomicE, descBits_sOpCurve]
  omega

theorem isZeroPtOptAtomicE_descBits_le {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) :
    atomicExprDescBits SDesc
      (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) tOptE) ≤
      atomicExprDescBits SDesc tOptE + 50 := by
  have hb0 : bits 0 = 1 := bits_zero
  simp only [isZeroPtOptAtomicE, atomicExprDescBits, descBits_sOpGrp, Expr.v0, varIdx, hb0]
  omega

end DescBits

end Computational.Proofs.Game.PromotedCostedReds.SimFig8WireSnap
