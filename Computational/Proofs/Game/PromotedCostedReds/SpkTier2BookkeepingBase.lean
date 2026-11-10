/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingProofs -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import

/-!
# Base Types and Metadata Operations for Tier-2 SPK Bookkeeping

Defines the `ReductionDsl` encoding `tier2GsTy` of `Tier2Gs`, `SM.spec` response codecs, and
constant-depth metadata expressions.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase

open ReductionDsl (Sig Ty Env Ops Expr bits atomicSig e2eSessionCodec GhostStT PlainT B
  recvResultT recvResultEnc recvResultDec smRT smRdec)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record RecvResult GameState inWindow
  noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10 partyEnc posTy posEnc posDec posSender
  posEpoch posIdx orE orE_eval maxN maxN_eval minN minN_eval leN sendsInE pGet pSet healedByE
  maxOptE letE_eval sendsInE_eval pGet_eval healedByE_eval maxOptE_eval)
open CryptoGames.Ratchet.LibsignalInst (configR1OnCurve)
open CryptoGames.LibsignalSession (PublicKey GhostState)
open CryptoVerification.E2E (Bytes noBobCorrInEpoch0 noBobCorrWhileAliceBelowEpoch10
  configRefuseEarlyBobCorr)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingPure (Tier2Gs updParty
  updTbl1 updPosTbl Tier2GsRel)

/-! ## Response codecs -/

section RespExprs

variable {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}

@[simp] theorem recvResultDec_recvResultEnc (r : RecvResult (Plain ℓ)) :
    recvResultDec (Pt := Pt) (recvResultEnc r) = r := by
  cases r <;> rfl

@[expose] def tier2SmRenc :
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) →
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q →
    (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote
  | .inl (.inl (.inl (.inl _))), w? => (w?, (none, none))
  | .inl (.inl (.inl (.inr _))), w? => (w?, (none, none))
  | .inl (.inl (.inr _)), rr? => (none, (rr?.map recvResultEnc, none))
  | .inl (.inr _), rr? => (none, (rr?.map recvResultEnc, none))
  | .inr _, st? => (none, (none, st?))

@[simp] theorem e2eSessionCodec_rdec_tier2SmRenc
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (ans : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    (e2eSessionCodec ℓ Pt).rdec sq (tier2SmRenc sq ans) = ans := by
  rcases sq with (((_ | _) | _) | _) | _ <;> cases ans <;> simp [smRdec, tier2SmRenc]

@[expose] def tier2RecvRejE {Γ : List (Ty (atomicSig ℓ Pt))} :
    Expr O Γ (recvResultT (ℓ := ℓ) (Pt := Pt)) :=
  .inl .unit

@[expose] def tier2RecvAccE {Γ : List (Ty (atomicSig ℓ Pt))}
    (t i : Expr O Γ .nat) (m? : Expr O Γ (.opt PlainT)) :
    Expr O Γ (recvResultT (ℓ := ℓ) (Pt := Pt)) :=
  .inr (.pair t (.pair i m?))

@[expose] def tier2SmRWireE {Γ : List (Ty (atomicSig ℓ Pt))}
    (w? : Expr O Γ (.opt (B 32))) : Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair w? (.pair .none .none)

@[expose] def tier2SmRRecvE {Γ : List (Ty (atomicSig ℓ Pt))}
    (rr? : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))) :
    Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair rr? .none)

@[expose] def tier2SmRCorrE {Γ : List (Ty (atomicSig ℓ Pt))}
    (st? : Expr O Γ (.opt GhostStT)) : Expr O Γ (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) :=
  .pair .none (.pair .none st?)

@[simp] theorem eval_tier2RecvRejE {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (tier2RecvRejE (ℓ := ℓ) (Pt := Pt) (O := O)).eval ρ = recvResultEnc .rejected := rfl

@[simp] theorem cost_tier2RecvRejE {Γ : List (Ty (atomicSig ℓ Pt))} :
    (tier2RecvRejE (ℓ := ℓ) (Pt := Pt) (O := O) (Γ := Γ)).cost = 2 := rfl

@[simp] theorem eval_tier2RecvAccE {Γ : List (Ty (atomicSig ℓ Pt))}
    (t i : Expr O Γ .nat) (m? : Expr O Γ (.opt PlainT)) (ρ : Env Γ) :
    (tier2RecvAccE t i m?).eval ρ =
      recvResultEnc (.accepted (t.eval ρ) (i.eval ρ) (m?.eval ρ)) := rfl

theorem cost_tier2RecvAccE {Γ : List (Ty (atomicSig ℓ Pt))}
    (t i : Expr O Γ .nat) (m? : Expr O Γ (.opt PlainT)) :
    (tier2RecvAccE t i m?).cost = t.cost + i.cost + m?.cost + 3 := by
  simp only [tier2RecvAccE, Expr.cost]; omega

@[simp] theorem eval_tier2SmRWireE {Γ : List (Ty (atomicSig ℓ Pt))}
    (w? : Expr O Γ (.opt (B 32))) (ρ : Env Γ) :
    (tier2SmRWireE w?).eval ρ = (w?.eval ρ, (none, none)) := rfl

theorem cost_tier2SmRWireE {Γ : List (Ty (atomicSig ℓ Pt))}
    (w? : Expr O Γ (.opt (B 32))) :
    (tier2SmRWireE w?).cost = w?.cost + 4 := by
  simp only [tier2SmRWireE, Expr.cost]

@[simp] theorem eval_tier2SmRRecvE {Γ : List (Ty (atomicSig ℓ Pt))}
    (rr? : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))) (ρ : Env Γ) :
    (tier2SmRRecvE rr?).eval ρ = (none, (rr?.eval ρ, none)) := rfl

theorem cost_tier2SmRRecvE {Γ : List (Ty (atomicSig ℓ Pt))}
    (rr? : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt)))) :
    (tier2SmRRecvE rr?).cost = rr?.cost + 4 := by
  simp only [tier2SmRRecvE, Expr.cost]; omega

@[simp] theorem eval_tier2SmRCorrE {Γ : List (Ty (atomicSig ℓ Pt))}
    (st? : Expr O Γ (.opt GhostStT)) (ρ : Env Γ) :
    (tier2SmRCorrE st?).eval ρ = (none, (none, st?.eval ρ)) := rfl

theorem cost_tier2SmRCorrE {Γ : List (Ty (atomicSig ℓ Pt))}
    (st? : Expr O Γ (.opt GhostStT)) :
    (tier2SmRCorrE st?).cost = st?.cost + 4 := by
  simp only [tier2SmRCorrE, Expr.cost]; omega

end RespExprs

/-! ## Per-party table helpers -/

section TblHelpers

variable {S : Sig} {O : Ops S}

@[expose] def tbl1GetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool) (i : Expr O Γ .nat) :
    Expr O Γ τ :=
  .tget (pGet tbl p) i

theorem eval_tbl1GetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool) (i : Expr O Γ .nat)
    (ρ : Env Γ) (f : Party → ℕ → τ.denote) (P : Party)
    (htbl : tbl.eval ρ = (f .A, f .B)) (hp : p.eval ρ = partyEnc P) :
    (tbl1GetE tbl p i).eval ρ = f P (i.eval ρ) := by
  unfold tbl1GetE
  dsimp only [Expr.eval]
  rw [pGet_eval tbl p ρ (fun Q => f Q) P htbl hp]

theorem cost_tbl1GetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool) (i : Expr O Γ .nat) :
    (tbl1GetE tbl p i).cost ≤ tbl.cost + p.cost + i.cost + 80 := by
  simp only [tbl1GetE, pGet, Expr.cost, Expr.v0]; omega

@[expose] def tbl1SetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool)
    (i : Expr O Γ .nat) (v : Expr O Γ τ) :
    Expr O Γ (.prod (.tbl τ) (.tbl τ)) :=
  .letE (.pair tbl (.pair p (.pair i v)))
    (let tbl0 : Expr O _ (.prod (.tbl τ) (.tbl τ)) := .fst .v0
     let p0 : Expr O _ .bool := .fst (.snd .v0)
     let i0 : Expr O _ .nat := .fst (.snd (.snd .v0))
     let v0 : Expr O _ τ := .snd (.snd (.snd .v0))
     let cur : Expr O _ (.tbl τ) := .ite p0 (.snd tbl0) (.fst tbl0)
     let upd : Expr O _ (.tbl τ) := .tset cur i0 v0
     .ite p0 (.pair (.fst tbl0) upd) (.pair upd (.snd tbl0)))

theorem eval_tbl1SetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool)
    (i : Expr O Γ .nat) (v : Expr O Γ τ) (ρ : Env Γ)
    (f : Party → ℕ → τ.denote) (P : Party)
    (htbl : tbl.eval ρ = (f .A, f .B)) (hp : p.eval ρ = partyEnc P) :
    (tbl1SetE tbl p i v).eval ρ =
      (updTbl1 f P (i.eval ρ) (v.eval ρ) .A, updTbl1 f P (i.eval ρ) (v.eval ρ) .B) := by
  cases P <;> simp [tbl1SetE, updTbl1, updParty, partyEnc, htbl, hp, Expr.eval, Expr.v0]

theorem cost_tbl1SetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl τ) (.tbl τ))) (p : Expr O Γ .bool)
    (i : Expr O Γ .nat) (v : Expr O Γ τ) :
    (tbl1SetE tbl p i v).cost ≤ tbl.cost + p.cost + i.cost + v.cost + 170 := by
  simp only [tbl1SetE, Expr.cost, Expr.v0]; omega

@[expose] def posTblGetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) : Expr O Γ τ :=
  .letE (.pair tbl pos)
    (let tbl0 : Expr O _ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))) := .fst .v0
     let pos0 : Expr O _ posTy := .snd .v0
     let pTbl : Expr O _ (.tbl (.tbl τ)) := .ite (posSender pos0) (.snd tbl0) (.fst tbl0)
     .tget (.tget pTbl (posEpoch pos0)) (posIdx pos0))

theorem eval_posTblGetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) (ρ : Env Γ)
    (f : Party → ℕ → ℕ → τ.denote) (p0 : Pos)
    (htbl : tbl.eval ρ = (f .A, f .B)) (hpos : pos.eval ρ = posEnc p0) :
    (posTblGetE tbl pos).eval ρ = f p0.sender p0.epoch p0.idx := by
  rcases p0 with ⟨s, ep, idx⟩
  cases s <;>
    simp [posTblGetE, posSender, posEpoch, posIdx, posEnc, partyEnc, htbl, hpos,
      Expr.eval, Expr.v0]

theorem cost_posTblGetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) :
    (posTblGetE tbl pos).cost ≤ tbl.cost + pos.cost + 160 := by
  simp only [posTblGetE, posSender, posEpoch, posIdx, Expr.cost, Expr.v0]; omega

@[expose] def posTblSetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) (v : Expr O Γ τ) :
    Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))) :=
  .letE (.pair tbl (.pair pos v))
    (let tbl0 : Expr O _ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))) := .fst .v0
     let pos0 : Expr O _ posTy := .fst (.snd .v0)
     let v0 : Expr O _ τ := .snd (.snd .v0)
     let s0 := posSender pos0
     let ep0 := posEpoch pos0
     let idx0 := posIdx pos0
     let pTbl : Expr O _ (.tbl (.tbl τ)) := .ite s0 (.snd tbl0) (.fst tbl0)
     let row := Expr.tget pTbl ep0
     let upd : Expr O _ (.tbl (.tbl τ)) := .tset pTbl ep0 (.tset row idx0 v0)
     .ite s0 (.pair (.fst tbl0) upd) (.pair upd (.snd tbl0)))

theorem eval_posTblSetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) (v : Expr O Γ τ) (ρ : Env Γ)
    (f : Party → ℕ → ℕ → τ.denote) (p0 : Pos)
    (htbl : tbl.eval ρ = (f .A, f .B)) (hpos : pos.eval ρ = posEnc p0) :
    (posTblSetE tbl pos v).eval ρ =
      (updPosTbl f p0 (v.eval ρ) .A, updPosTbl f p0 (v.eval ρ) .B) := by
  rcases p0 with ⟨s, ep, idx⟩
  cases s <;>
    (simp [posTblSetE, posSender, posEpoch, posIdx, posEnc, partyEnc,
       updPosTbl, updParty, htbl, hpos, Expr.eval, Expr.v0]
     funext e; by_cases he : e = ep <;> simp [he])

theorem cost_posTblSetE {τ : Ty S} {Γ : List (Ty S)}
    (tbl : Expr O Γ (.prod (.tbl (.tbl τ)) (.tbl (.tbl τ))))
    (pos : Expr O Γ posTy) (v : Expr O Γ τ) :
    (posTblSetE tbl pos v).cost ≤ tbl.cost + pos.cost + v.cost + 380 := by
  simp only [posTblSetE, posSender, posEpoch, posIdx, Expr.cost, Expr.v0]; omega

end TblHelpers

/-! ## Game-state encoding and metadata operations -/

@[expose, reducible] def tier2RecTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod posTy (.prod PlainT (B 32))

@[expose] def tier2RecEnc {ℓ : ℕ} {Pt : Type} (r : Record (Plain ℓ) Bytes) : (tier2RecTy ℓ Pt).denote :=
  (posEnc r.pos, (r.msg, r.ct))

@[expose] def tier2RecDec {ℓ : ℕ} {Pt : Type} (v : (tier2RecTy ℓ Pt).denote) : Record (Plain ℓ) Bytes :=
  ⟨posDec v.1, v.2.1, v.2.2⟩

@[simp] theorem tier2RecDec_tier2RecEnc {ℓ : ℕ} {Pt : Type} (r : Record (Plain ℓ) Bytes) :
    tier2RecDec (Pt := Pt) (tier2RecEnc r) = r := by
  cases r; simp [tier2RecEnc, tier2RecDec]

@[expose, reducible] def tier2CoreTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (.prod GhostStT GhostStT) (.prod .bool .bool))
        (.prod (.prod (.prod .nat .nat) (.prod .nat .nat))
               (.prod (.opt .nat) (.prod (.tbl .nat) (.tbl .nat))))

@[expose, reducible] def tier2DllTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod .nat (.prod (.tbl .nat) (.tbl .nat)))
        (.prod (.prod (.tbl (.opt (tier2RecTy ℓ Pt))) (.tbl .nat))
               (.prod (.tbl .nat) (.tbl .nat)))

@[expose, reducible] def tier2FlagsTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (.tbl (.tbl .nat)) (.tbl (.tbl .nat)))
        (.prod (.prod (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) (.prod .nat .nat))
               (.prod (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) (.prod .nat .nat)))

/-- Balanced `Ty (atomicSig ℓ Pt)` encoding of `Tier2Gs ℓ`. -/
@[expose, reducible] def tier2GsTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (tier2CoreTy ℓ Pt) (.prod (tier2DllTy ℓ Pt) (tier2FlagsTy ℓ Pt))

@[expose] def tier2GsEnc {ℓ : ℕ} (Pt : Type) (d : Tier2Gs ℓ) : (tier2GsTy ℓ Pt).denote :=
  ((((d.st .A, d.st .B), (d.b, d.win)),
    (((d.epoch .A, d.epoch .B), (d.idx .A, d.idx .B)),
     (d.tL, (d.maxAcc .A, d.maxAcc .B)))),
   (((d.nextId, (d.headTbl .A, d.headTbl .B)),
     ((fun j => (d.nodeRec j).map tier2RecEnc, d.nodeKey),
      (d.nodePrev, d.nodeNext))),
    ((d.posNode .A, d.posNode .B),
     (((d.challTbl .A, d.challTbl .B), (d.challCount .A, d.challCount .B)),
      ((d.compTbl .A, d.compTbl .B), (d.uncompCount .A, d.uncompCount .B))))))

section GsMetadataOps

variable {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}

local notation "S" => atomicSig ℓ Pt

@[expose] def tier2RecPos {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) : Expr O Γ posTy := .fst r
def tier2RecMsg {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) : Expr O Γ PlainT := .fst (.snd r)
@[expose] def tier2RecCt {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) : Expr O Γ (B 32) := .snd (.snd r)

@[expose] def tier2RecMk {Γ : List (Ty S)} (pos : Expr O Γ posTy) (msg : Expr O Γ PlainT)
    (ct : Expr O Γ (B 32)) : Expr O Γ (tier2RecTy ℓ Pt) :=
  .pair pos (.pair msg ct)

@[simp] theorem eval_tier2RecPos {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) (ρ : Env Γ)
    (rec_ : Record (Plain ℓ) Bytes) (hr : r.eval ρ = tier2RecEnc rec_) :
    (tier2RecPos r).eval ρ = posEnc rec_.pos := by
  simp [tier2RecPos, Expr.eval, hr, tier2RecEnc]

@[simp] theorem eval_tier2RecMsg {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) (ρ : Env Γ)
    (rec_ : Record (Plain ℓ) Bytes) (hr : r.eval ρ = tier2RecEnc rec_) :
    (tier2RecMsg r).eval ρ = rec_.msg := by
  simp [tier2RecMsg, Expr.eval, hr, tier2RecEnc]

@[simp] theorem eval_tier2RecCt {Γ : List (Ty S)} (r : Expr O Γ (tier2RecTy ℓ Pt)) (ρ : Env Γ)
    (rec_ : Record (Plain ℓ) Bytes) (hr : r.eval ρ = tier2RecEnc rec_) :
    (tier2RecCt r).eval ρ = rec_.ct := by
  simp [tier2RecCt, Expr.eval, hr, tier2RecEnc]

@[simp] theorem eval_tier2RecMk {Γ : List (Ty S)} (pos : Expr O Γ posTy)
    (msg : Expr O Γ PlainT) (ct : Expr O Γ (B 32)) (ρ : Env Γ) (p0 : Pos)
    (hpos : pos.eval ρ = posEnc p0) :
    (tier2RecMk pos msg ct).eval ρ = tier2RecEnc ⟨p0, msg.eval ρ, ct.eval ρ⟩ := by
  simp [tier2RecMk, Expr.eval, hpos, tier2RecEnc]

theorem cost_tier2RecMk {Γ : List (Ty S)} (pos : Expr O Γ posTy)
    (msg : Expr O Γ PlainT) (ct : Expr O Γ (B 32)) :
    (tier2RecMk pos msg ct).cost = pos.cost + msg.cost + ct.cost + 2 := by
  simp only [tier2RecMk, Expr.cost]; omega

@[expose] def gsStTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod GhostStT GhostStT) := .fst (.fst (.fst s))
@[expose] def gsBTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ .bool := .fst (.snd (.fst (.fst s)))
@[expose] def gsWinTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ .bool := .snd (.snd (.fst (.fst s)))
@[expose] def gsEpochTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod .nat .nat) := .fst (.fst (.snd (.fst s)))
@[expose] def gsIdxTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod .nat .nat) := .snd (.fst (.snd (.fst s)))
@[expose] def gsTLTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.opt .nat) := .fst (.snd (.snd (.fst s)))
@[expose] def gsMaxAccTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod (.tbl .nat) (.tbl .nat)) := .snd (.snd (.snd (.fst s)))

@[expose] def gsNextIdTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ .nat := .fst (.fst (.fst (.snd s)))
@[expose] def gsHeadTblTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod (.tbl .nat) (.tbl .nat)) := .snd (.fst (.fst (.snd s)))
@[expose] def gsNodeRecTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.tbl (.opt (tier2RecTy ℓ Pt))) := .fst (.fst (.snd (.fst (.snd s))))
@[expose] def gsNodeKeyTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.tbl .nat) := .snd (.fst (.snd (.fst (.snd s))))
@[expose] def gsNodePrevTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.tbl .nat) := .fst (.snd (.snd (.fst (.snd s))))
@[expose] def gsNodeNextTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.tbl .nat) := .snd (.snd (.snd (.fst (.snd s))))

@[expose] def gsPosNodeTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod (.tbl (.tbl .nat)) (.tbl (.tbl .nat))) := .fst (.snd (.snd s))
@[expose] def gsChallTblTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) := .fst (.fst (.snd (.snd (.snd s))))
@[expose] def gsChallCountTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod .nat .nat) := .snd (.fst (.snd (.snd (.snd s))))
@[expose] def gsCompTblTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) := .fst (.snd (.snd (.snd (.snd s))))
@[expose] def gsUncompCountTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    Expr O Γ (.prod .nat .nat) := .snd (.snd (.snd (.snd (.snd s))))

@[expose] def initGsTier2E {Γ : List (Ty S)} (stA stB : Expr O Γ GhostStT) (b : Expr O Γ .bool) :
    Expr O Γ (tier2GsTy ℓ Pt) :=
  .pair
    (.pair (.pair (.pair stA stB) (.pair b (.bool false)))
           (.pair (.pair (.pair (.nat 0) (.nat 0)) (.pair (.nat 0) (.nat 0)))
                  (.pair .none (.pair (.tconst (.nat 0)) (.tconst (.nat 0))))))
    (.pair
      (.pair (.pair (.nat 1) (.pair (.tconst (.nat 0)) (.tconst (.nat 0))))
             (.pair (.pair (.tconst .none) (.tconst (.nat 0)))
                    (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))))
      (.pair (.pair (.tconst (.tconst (.nat 0))) (.tconst (.tconst (.nat 0))))
             (.pair (.pair (.pair (.tconst (.tconst (.bool false)))
                                  (.tconst (.tconst (.bool false))))
                           (.pair (.nat 0) (.nat 0)))
                    (.pair (.pair (.tconst (.tconst (.bool false)))
                                  (.tconst (.tconst (.bool false))))
                           (.pair (.nat 0) (.nat 0))))))

@[simp] theorem eval_initGsTier2E {Γ : List (Ty S)}
    (stA stB : Expr O Γ GhostStT) (b : Expr O Γ .bool) (ρ : Env Γ) :
    (initGsTier2E stA stB b).eval ρ =
      tier2GsEnc Pt (Tier2Gs.init (stA.eval ρ) (stB.eval ρ) (b.eval ρ)) := by
  simp [initGsTier2E, tier2GsEnc, Tier2Gs.init, Expr.eval]

theorem cost_initGsTier2E {Γ : List (Ty S)}
    (stA stB : Expr O Γ GhostStT) (b : Expr O Γ .bool) :
    (initGsTier2E stA stB b).cost ≤ stA.cost + stB.cost + b.cost + 85 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  simp only [initGsTier2E, Expr.cost, hb0, hb1]; omega

@[expose] def setWinTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (w : Expr O Γ .bool) :
    Expr O Γ (tier2GsTy ℓ Pt) :=
  .letE (.pair s w)
    (let s0 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let w0 : Expr O _ .bool := .snd .v0
     .pair (.pair (.pair (gsStTier2E s0) (.pair (gsBTier2E s0) w0)) (.snd (.fst s0)))
           (.snd s0))

@[simp] theorem eval_setWinTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (w : Expr O Γ .bool) (ρ : Env Γ) (d : Tier2Gs ℓ)
    (hs : s.eval ρ = tier2GsEnc Pt d) :
    (setWinTier2E s w).eval ρ = tier2GsEnc Pt (d.setWin (w.eval ρ)) := by
  simp [setWinTier2E, gsStTier2E, gsBTier2E, tier2GsEnc, Tier2Gs.setWin, hs,
    Expr.eval, Expr.v0]

theorem cost_setWinTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (w : Expr O Γ .bool) :
    (setWinTier2E s w).cost ≤ s.cost + w.cost + 30 := by
  simp only [setWinTier2E, gsStTier2E, gsBTier2E, Expr.cost, Expr.v0]; omega

@[expose] def safeChTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) : Expr O Γ .bool :=
  .letE (.pair s p)
    (healedByE (gsTLTier2E (.fst .v0)) Δ (pGet (gsEpochTier2E (.fst .v0)) (.snd .v0)))

@[simp] theorem eval_safeChTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (ρ : Env Γ) (d : Tier2Gs ℓ) (P : Party)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (safeChTier2E Δ s p).eval ρ = d.safeCh Δ P := by
  unfold safeChTier2E Tier2Gs.safeCh
  rw [letE_eval]
  have hp0 : (Expr.pair s p).eval ρ = (tier2GsEnc Pt d, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) .bool) (tier2GsEnc Pt d, partyEnc P) ρ
  rw [healedByE_eval, pGet_eval (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.snd .v0) ρ₁ d.epoch P rfl rfl]
  rfl

theorem cost_safeChTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (safeChTier2E Δ s p).cost ≤ s.cost + p.cost + bits Δ + 60 := by
  simp only [safeChTier2E, healedByE, CryptoGames.SM.leN, pGet, gsTLTier2E, gsEpochTier2E,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[expose] def safeInjTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt)) : Expr O Γ .bool :=
  .letE s
    (healedByE (gsTLTier2E .v0) Δ
      (minN (.fst (gsEpochTier2E .v0)) (.snd (gsEpochTier2E .v0))))

@[simp] theorem eval_safeInjTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (ρ : Env Γ) (d : Tier2Gs ℓ) (hs : s.eval ρ = tier2GsEnc Pt d) :
    (safeInjTier2E Δ s).eval ρ = d.safeInj Δ := by
  unfold safeInjTier2E Tier2Gs.safeInj
  rw [letE_eval, hs]
  set ρ₁ := Env.cons (t := tier2GsTy ℓ Pt) (tier2GsEnc Pt d) ρ
  rw [healedByE_eval, CryptoGames.SM.minN_eval]
  rfl

theorem cost_safeInjTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt)) :
    (safeInjTier2E Δ s).cost ≤ s.cost + bits Δ + 65 := by
  simp only [safeInjTier2E, healedByE, CryptoGames.SM.leN, minN, gsTLTier2E, gsEpochTier2E,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[expose] def leakTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (l : Expr O Γ .nat) :
    Expr O Γ (tier2GsTy ℓ Pt) :=
  .letE (.pair s l)
    (let s0 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let l0 : Expr O _ .nat := .snd .v0
     .pair (.pair (.fst (.fst s0))
                  (.pair (.fst (.snd (.fst s0)))
                         (.pair (.some (maxOptE (gsTLTier2E s0) l0)) (gsMaxAccTier2E s0))))
           (.snd s0))

@[simp] theorem eval_leakTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (l : Expr O Γ .nat) (ρ : Env Γ) (d : Tier2Gs ℓ) (hs : s.eval ρ = tier2GsEnc Pt d) :
    (leakTier2E s l).eval ρ = tier2GsEnc Pt (d.leak (l.eval ρ)) := by
  unfold leakTier2E Tier2Gs.leak
  rw [letE_eval]
  have hp0 : (Expr.pair s l).eval ρ = (tier2GsEnc Pt d, l.eval ρ) := by
    simp [Expr.eval, hs]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) .nat) (tier2GsEnc Pt d, l.eval ρ) ρ
  have hm := maxOptE_eval (gsTLTier2E (.fst (Expr.v0 (O := O)))) (.snd (Expr.v0 (O := O))) ρ₁
  dsimp only [Expr.eval]
  rw [hm]
  simp only [gsTLTier2E, gsMaxAccTier2E, tier2GsEnc, ρ₁, Expr.eval, Expr.v0, Env.get]

theorem cost_leakTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (l : Expr O Γ .nat) :
    (leakTier2E s l).cost ≤ s.cost + l.cost + 70 := by
  simp only [leakTier2E, maxOptE, maxN, CryptoGames.SM.leN, gsTLTier2E, gsMaxAccTier2E,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[expose] def epMgmtTier2E {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (bad : Expr O Γ .bool) : Expr O Γ (.opt (tier2GsTy ℓ Pt)) :=
  .letE (.pair s (.pair p bad))
    (let s0 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let p0 : Expr O _ .bool := .fst (.snd .v0)
     let bad0 : Expr O _ .bool := .snd (.snd .v0)
     let epP : Expr O _ .nat := pGet (gsEpochTier2E s0) p0
     let epNext : Expr O _ .nat := .add epP (.nat 1)
     .ite (sendsInE p0 epNext)
       (.ite (.lt (.nat qep) epNext)
         .none
         (.letE (.ite (.and bad0 (.not (safeChTier2E Δ s0 p0))) (leakTier2E s0 epNext) s0)
           (.some
             (.pair
               (.pair (.fst (.fst .v0))
                      (.pair (.pair (pSet (gsEpochTier2E .v0) (Expr.fst (.snd .v1))
                                      (.add (pGet (gsEpochTier2E .v0) (Expr.fst (.snd .v1))) (.nat 1)))
                                    (pSet (gsIdxTier2E .v0) (Expr.fst (.snd .v1)) (.nat 0)))
                             (.snd (.snd (.fst .v0)))))
               (.snd .v0)))))
       (.ite (.lt (.nat qep) epP) .none (.some s0)))

private theorem ite_eval {τ : Ty S} {Γ : List (Ty S)}
    (c : Expr O Γ .bool) (t e : Expr O Γ τ) (ρ : Env Γ) :
    (Expr.ite c t e).eval ρ = if c.eval ρ = true then t.eval ρ else e.eval ρ := rfl

@[simp] theorem eval_epMgmtTier2E {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (bad : Expr O Γ .bool) (ρ : Env Γ)
    (d : Tier2Gs ℓ) (P : Party)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (epMgmtTier2E Δ qep s p bad).eval ρ =
      (d.epMgmt Δ qep P (bad.eval ρ)).map (tier2GsEnc Pt) := by
  unfold epMgmtTier2E Tier2Gs.epMgmt
  rw [letE_eval]
  have hp0 : (Expr.pair s (.pair p bad)).eval ρ =
      (tier2GsEnc Pt d, (partyEnc P, bad.eval ρ)) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) (.prod .bool .bool))
    (tier2GsEnc Pt d, (partyEnc P, bad.eval ρ)) ρ
  have hepP : (pGet (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0))).eval ρ₁ =
      d.epoch P :=
    pGet_eval (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0)) ρ₁ d.epoch P rfl rfl
  have hsends : (sendsInE (.fst (.snd (Expr.v0 (O := O))))
      (.add (pGet (gsEpochTier2E (.fst .v0)) (.fst (.snd .v0))) (.nat 1))).eval ρ₁ =
      P.sendsIn (d.epoch P + 1) := by
    rw [sendsInE_eval (.fst (.snd (Expr.v0 (O := O)))) _ ρ₁ P rfl]
    dsimp only [Expr.eval]
    rw [hepP]
  have hlt1 : (Expr.lt (.nat qep)
      (.add (pGet (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0))) (.nat 1))).eval ρ₁ =
      decide (qep < d.epoch P + 1) := by
    dsimp only [Expr.eval]
    simp only [hepP]
  have hlt0 : (Expr.lt (.nat qep)
      (pGet (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.fst (.snd .v0)))).eval ρ₁ =
      decide (qep < d.epoch P) := by
    dsimp only [Expr.eval]
    simp only [hepP]
  rw [ite_eval, hsends]
  by_cases hsIn : P.sendsIn (d.epoch P + 1)
  · simp only [hsIn, ↓reduceIte]
    rw [ite_eval, hlt1]
    by_cases hq : qep < d.epoch P + 1
    · simp [hq, Expr.eval]
    · simp only [↓reduceIte, hq, Option.map_some, decide_eq_true_eq]
      rw [letE_eval]
      have hsc : (safeChTier2E Δ (.fst (Expr.v0 (O := O))) (.fst (.snd .v0))).eval ρ₁ =
          d.safeCh Δ P := eval_safeChTier2E Δ _ _ ρ₁ d P rfl rfl
      have hlk : (leakTier2E (.fst (Expr.v0 (O := O)))
          (.add (pGet (gsEpochTier2E (.fst .v0)) (.fst (.snd .v0))) (.nat 1))).eval ρ₁ =
          tier2GsEnc Pt (d.leak (d.epoch P + 1)) := by
        rw [eval_leakTier2E _ _ ρ₁ d rfl]
        dsimp only [Expr.eval]
        rw [hepP]
      have hd1 : (Expr.ite (O := O) (.and (.snd (.snd .v0))
            (.not (safeChTier2E Δ (.fst .v0) (.fst (.snd .v0)))))
          (leakTier2E (.fst .v0)
            (.add (pGet (gsEpochTier2E (.fst .v0)) (.fst (.snd .v0))) (.nat 1)))
          (.fst .v0)).eval ρ₁ =
          tier2GsEnc Pt (if bad.eval ρ && !d.safeCh Δ P then d.leak (d.epoch P + 1) else d) := by
        rw [ite_eval, hlk]
        have hcond : (Expr.and (O := O) (.snd (.snd .v0))
            (.not (safeChTier2E Δ (.fst .v0) (.fst (.snd .v0))))).eval ρ₁ =
            (bad.eval ρ && !d.safeCh Δ P) := by
          dsimp only [Expr.eval]
          rw [hsc]
          rfl
        rw [hcond]
        split_ifs <;> rfl
      rw [hd1]
      set d1 := if bad.eval ρ && !d.safeCh Δ P then d.leak (d.epoch P + 1) else d
      cases P <;>
        simp [pSet, pGet, gsEpochTier2E, gsIdxTier2E, updParty, partyEnc, tier2GsEnc,
          ρ₁, Expr.eval, Expr.v0, Expr.v1]
  · simp only [hsIn, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval, hlt0]
    by_cases hq : qep < d.epoch P
    · simp [hq, Expr.eval]
    · simp [hq, tier2GsEnc, ρ₁, Expr.eval, Expr.v0]

theorem cost_epMgmtTier2E {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (bad : Expr O Γ .bool) :
    (epMgmtTier2E Δ qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + bits Δ + 2 * bits qep + 350 := by
  let t0 : Ty S := .prod (tier2GsTy ℓ Pt) (.prod .bool .bool)
  have hsc := cost_safeChTier2E (ℓ := ℓ) (Pt := Pt) (O := O) (Γ := t0 :: Γ) Δ
    (.fst .v0) (.fst (.snd .v0))
  have hlk := cost_leakTier2E (ℓ := ℓ) (Pt := Pt) (O := O) (Γ := t0 :: Γ)
    (.fst .v0) (.add (pGet (gsEpochTier2E (.fst .v0)) (.fst (.snd .v0))) (.nat 1))
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  simp only [epMgmtTier2E, sendsInE, pSet, pGet, gsEpochTier2E, gsIdxTier2E,
    Expr.cost, Expr.v0, Expr.v1, hb0, hb1, hb2] at hsc hlk ⊢
  omega

@[expose] def gsChallTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (pos : Expr O Γ posTy) :
    Expr O Γ .bool :=
  posTblGetE (gsChallTblTier2E s) pos

@[simp] theorem eval_gsChallTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) (ρ : Env Γ) (d : Tier2Gs ℓ) (p0 : Pos)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hpos : pos.eval ρ = posEnc p0) :
    (gsChallTier2E s pos).eval ρ = d.challContains p0 :=
  eval_posTblGetE (gsChallTblTier2E s) pos ρ d.challTbl p0
    (by simp [gsChallTblTier2E, hs, tier2GsEnc, Expr.eval]) hpos

theorem cost_gsChallTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) :
    (gsChallTier2E s pos).cost ≤ s.cost + pos.cost + 170 := by
  have hc := cost_posTblGetE (gsChallTblTier2E s) pos
  simp only [gsChallTier2E, gsChallTblTier2E, Expr.cost] at hc ⊢; omega

@[expose] def gsCompTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (pos : Expr O Γ posTy) :
    Expr O Γ .bool :=
  posTblGetE (gsCompTblTier2E s) pos

@[simp] theorem eval_gsCompTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) (ρ : Env Γ) (d : Tier2Gs ℓ) (p0 : Pos)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hpos : pos.eval ρ = posEnc p0) :
    (gsCompTier2E s pos).eval ρ = d.compContains p0 :=
  eval_posTblGetE (gsCompTblTier2E s) pos ρ d.compTbl p0
    (by simp [gsCompTblTier2E, hs, tier2GsEnc, Expr.eval]) hpos

theorem cost_gsCompTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) :
    (gsCompTier2E s pos).cost ≤ s.cost + pos.cost + 170 := by
  have hc := cost_posTblGetE (gsCompTblTier2E s) pos
  simp only [gsCompTier2E, gsCompTblTier2E, Expr.cost] at hc ⊢; omega

@[expose] def trivialTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) : Expr O Γ .bool :=
  .letE (.pair s pos)
    (let s0 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let pos0 : Expr O _ posTy := .snd .v0
     orE (gsCompTier2E s0 pos0)
       (.and (.eqN (posTblGetE (gsPosNodeTier2E s0) pos0) (.nat 0))
             (.not (healedByE (gsTLTier2E s0) Δ (posEpoch pos0)))))

private theorem nat_beq_zero_eq_decide (x : ℕ) : (x == 0) = decide (x = 0) := by
  cases h : (x == 0) <;> simp_all [beq_iff_eq]

@[simp] theorem eval_trivialTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) (ρ : Env Γ) (d : Tier2Gs ℓ) (p0 : Pos)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hpos : pos.eval ρ = posEnc p0) :
    (trivialTier2E Δ s pos).eval ρ = d.trivial Δ p0 := by
  unfold trivialTier2E Tier2Gs.trivial
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (tier2GsEnc Pt d, posEnc p0) := by
    simp [Expr.eval, hs, hpos]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) posTy) (tier2GsEnc Pt d, posEnc p0) ρ
  rw [CryptoGames.SM.orE_eval, eval_gsCompTier2E _ _ ρ₁ d p0 rfl rfl]
  dsimp only [Expr.eval]
  rw [eval_posTblGetE _ _ ρ₁ d.posNode p0 rfl rfl, healedByE_eval, nat_beq_zero_eq_decide]
  rcases p0 with ⟨_, ep, _⟩
  rfl

theorem cost_trivialTier2E {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O Γ (tier2GsTy ℓ Pt))
    (pos : Expr O Γ posTy) :
    (trivialTier2E Δ s pos).cost ≤ s.cost + pos.cost + bits Δ + 420 := by
  let t0 : Ty S := .prod (tier2GsTy ℓ Pt) posTy
  have hc := cost_gsCompTier2E (ℓ := ℓ) (Pt := Pt) (O := O) (Γ := t0 :: Γ) (.fst .v0) (.snd .v0)
  have hn := cost_posTblGetE (O := O) (Γ := t0 :: Γ) (gsPosNodeTier2E (.fst .v0)) (.snd .v0)
  have hb0 : bits 0 = 1 := by decide
  simp only [trivialTier2E, orE, healedByE, CryptoGames.SM.leN, gsPosNodeTier2E, gsTLTier2E,
    posEpoch, Expr.cost, Expr.v0, Expr.v1, hb0] at hc hn ⊢
  omega

@[expose] def corrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) : Expr O Γ .bool :=
  .letE (.pair s (.not p))
    (.and (.eqN (pGet (gsChallCountTier2E (.fst .v0)) (.snd .v0)) (.nat 0))
          (.eqN (pGet (gsUncompCountTier2E (.fst .v0)) (.snd .v0)) (.nat 0)))

@[simp] theorem eval_corrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (ρ : Env Γ) (d : Tier2Gs ℓ) (P : Party)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (corrAllowedTier2E s p).eval ρ = d.corrAllowed P := by
  cases P <;>
    simp [corrAllowedTier2E, Tier2Gs.corrAllowed, Party.other, pGet, gsChallCountTier2E,
      gsUncompCountTier2E, tier2GsEnc, partyEnc, nat_beq_zero_eq_decide, hs, hp,
      Expr.eval, Expr.v0]

theorem cost_corrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (corrAllowedTier2E s p).cost ≤ s.cost + p.cost + 50 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [corrAllowedTier2E, pGet, gsChallCountTier2E, gsUncompCountTier2E,
    Expr.cost, Expr.v0, hb0]
  omega

@[expose] def afterCorrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (_p : Expr O Γ .bool) : Expr O Γ (tier2GsTy ℓ Pt) :=
  .letE s
    (leakTier2E .v0 (maxN (.fst (gsEpochTier2E .v0)) (.snd (gsEpochTier2E .v0))))

@[simp] theorem eval_afterCorrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (ρ : Env Γ) (d : Tier2Gs ℓ) (P : Party)
    (hs : s.eval ρ = tier2GsEnc Pt d) :
    (afterCorrAllowedTier2E s p).eval ρ = tier2GsEnc Pt (d.afterCorrAllowed P) := by
  unfold afterCorrAllowedTier2E Tier2Gs.afterCorrAllowed
  rw [letE_eval, hs]
  set ρ₁ := Env.cons (t := tier2GsTy ℓ Pt) (tier2GsEnc Pt d) ρ
  rw [eval_leakTier2E _ _ ρ₁ d rfl, CryptoGames.SM.maxN_eval]
  rfl

theorem cost_afterCorrAllowedTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (afterCorrAllowedTier2E s p).cost ≤ s.cost + 120 := by
  have hlk := cost_leakTier2E (ℓ := ℓ) (Pt := Pt) (O := O) (Γ := tier2GsTy ℓ Pt :: Γ)
    .v0 (maxN (.fst (gsEpochTier2E .v0)) (.snd (gsEpochTier2E .v0)))
  simp only [afterCorrAllowedTier2E, maxN, CryptoGames.SM.leN, gsEpochTier2E,
    Expr.cost, Expr.v0] at hlk ⊢
  omega

@[expose] def inWindowTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool) :
    Expr O Γ .bool :=
  .letE (.pair s p)
    (.not (sendsInE (.snd .v0) (pGet (gsEpochTier2E (.fst .v0)) (.snd .v0))))

theorem eval_inWindowTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) (ρ : Env Γ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (d : Tier2Gs ℓ) (P : Party)
    (hrel : Tier2GsRel ℓ gs d)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (inWindowTier2E s p).eval ρ = inWindow gs P := by
  unfold inWindowTier2E inWindow
  rw [letE_eval]
  have hp0 : (Expr.pair s p).eval ρ = (tier2GsEnc Pt d, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (tier2GsTy ℓ Pt) .bool) (tier2GsEnc Pt d, partyEnc P) ρ
  dsimp only [Expr.eval]
  rw [sendsInE_eval (.snd (Expr.v0 (O := O))) _ ρ₁ P rfl,
      pGet_eval (gsEpochTier2E (.fst (Expr.v0 (O := O)))) (.snd .v0) ρ₁ d.epoch P rfl rfl,
      hrel.h_epoch]

theorem cost_inWindowTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (inWindowTier2E s p).cost ≤ s.cost + p.cost + 45 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  simp only [inWindowTier2E, sendsInE, pGet, gsEpochTier2E, Expr.cost, Expr.v0, hb0, hb1, hb2]
  omega

@[expose] def sendOKTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool) :
    Expr O Γ .bool :=
  .letE (.pair s p)
    (.not (.and (.snd .v0) (.eqN (.snd (gsEpochTier2E (.fst .v0))) (.nat 0))))

theorem eval_sendOKTier2E (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool) (ρ : Env Γ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (d : Tier2Gs ℓ) (P : Party)
    (hrel : Tier2GsRel ℓ gs d)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (sendOKTier2E s p).eval ρ = (configRefuseEarlyBobCorr decT encT).sendOK gs P := by
  cases P <;> simp [sendOKTier2E, configRefuseEarlyBobCorr, configR1OnCurve,
    CryptoGames.SM.configR1, noBobSendInEpoch0, gsEpochTier2E, tier2GsEnc, partyEnc,
    nat_beq_zero_eq_decide, hrel.h_epoch, hs, hp, Expr.eval, Expr.v0]

theorem cost_sendOKTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (sendOKTier2E s p).cost ≤ s.cost + p.cost + 25 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [sendOKTier2E, gsEpochTier2E, Expr.cost, Expr.v0, hb0]; omega

@[expose] def corrOKTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool) :
    Expr O Γ .bool :=
  .letE (.pair s p)
    (let s0 : Expr O _ (tier2GsTy ℓ Pt) := .fst .v0
     let p0 : Expr O _ .bool := .snd .v0
     let epA : Expr O _ .nat := .fst (gsEpochTier2E s0)
     let epB : Expr O _ .nat := .snd (gsEpochTier2E s0)
     let okA10 : Expr O _ .bool := .not (.and (.not p0) (.lt epA (.nat 10)))
     let okB0 : Expr O _ .bool := .not (.and p0 (.eqN epB (.nat 0)))
     let okB10 : Expr O _ .bool := .not (.and p0 (.lt epA (.nat 10)))
     .and (.and okA10 okB0) okB10)

theorem eval_corrOKTier2E (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt)) (p : Expr O Γ .bool) (ρ : Env Γ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (d : Tier2Gs ℓ) (P : Party)
    (hrel : Tier2GsRel ℓ gs d)
    (hs : s.eval ρ = tier2GsEnc Pt d) (hp : p.eval ρ = partyEnc P) :
    (corrOKTier2E s p).eval ρ = (configRefuseEarlyBobCorr decT encT).corrOK gs P := by
  have hAB : (Party.A == Party.B) = false := rfl
  have hBA : (Party.B == Party.A) = false := rfl
  cases P <;> simp [corrOKTier2E, configRefuseEarlyBobCorr, configR1OnCurve,
    CryptoGames.SM.configR1, noAliceCorrWhileAliceBelowEpoch10, noBobCorrInEpoch0,
    noBobCorrWhileAliceBelowEpoch10, gsEpochTier2E, tier2GsEnc, partyEnc,
    nat_beq_zero_eq_decide, hAB, hBA, hrel.h_epoch, hs, hp, Expr.eval, Expr.v0]

theorem cost_corrOKTier2E {Γ : List (Ty S)} (s : Expr O Γ (tier2GsTy ℓ Pt))
    (p : Expr O Γ .bool) :
    (corrOKTier2E s p).cost ≤ s.cost + p.cost + 60 := by
  have hb0 : bits 0 = 1 := by decide
  have hb10 : bits 10 = 4 := by decide
  simp only [corrOKTier2E, gsEpochTier2E, Expr.cost, Expr.v0, hb0, hb10]; omega

end GsMetadataOps

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
