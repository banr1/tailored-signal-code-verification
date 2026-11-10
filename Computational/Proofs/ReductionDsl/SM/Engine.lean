/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Proofs.ReductionDsl.SM.GameCosted
public import Computational.Proofs.GameHop.CompDedup
public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.SpecLemmas.Reductions.ReductionDsl.Core
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.CKA.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRNG.CostedTables
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed SM §5.3 simulation engine

Implements the SM §5.3 simulation engine (`CryptoGames.SM.Engine`) in `ReductionDsl` over `ckaSig`,
together with size-honesty of the CKA and PRNG operator/sampler tables, step-level and full
simulation evaluation agreement, and preservation of `SMEngineInv` and `SMVRInv`.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp
open Computational.Proofs.GameHop.CompDedup
  (CountLe countLe_dedup_of_subset dedupPrepend foldr_dedup_map_eq
   dedup_append_eq_dedupPrepend dedup_filter_eq length_dedup_le_of_subset)

/-! ## Size-honesty of CKA and PRNG tables -/

namespace CryptoGames.CKA

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

theorem ckaOps_sizeHonest
    (ckaInitA : KC → Γ)
    (ckaInitB : KC → Γ)
    (ckaSend : Γ → CCoins → Γ × T × I)
    (ckaReceive : Γ → T → Γ × I)
    (prngInit : KR → RSt)
    (prngUp : RSt → I → RSt × K)
    (fsInitSender : K → SS)
    (fsInitReceiver : K → RS)
    (fsSend : SS → SM.Construction.Header T → M → SS × E)
    (fsReceive : RS → SM.Construction.Header T → E → Option (RS × ℕ × M))
    (eqT : T → T → Bool)
    (eqI : I → I → Bool)
    (eqM : M → M → Bool)
    (eqE : E → E → Bool)
    (lam : I)
    (defaultE : E) :
    OpsSizeHonest
      (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) := by
  intro o x B _
  cases o with
  | ckaInitA => simp only [Ty.Fits]; omega
  | ckaInitB => simp only [Ty.Fits]; omega
  | ckaSend =>
    simp only [Ty.Fits]
    exact ⟨by omega, ⟨by omega, by omega⟩⟩
  | ckaReceive =>
    simp only [Ty.Fits]
    exact ⟨by omega, by omega⟩
  | prngInit => simp only [Ty.Fits]; omega
  | prngUp =>
    simp only [Ty.Fits]
    exact ⟨by omega, by omega⟩
  | fsInitSender => simp only [Ty.Fits]; omega
  | fsInitReceiver => simp only [Ty.Fits]; omega
  | fsSend =>
    simp only [Ty.Fits]
    exact ⟨by omega, by omega⟩
  | fsReceive B_idx =>
    rcases x with ⟨rs, h, e⟩
    dsimp only [ckaOps]
    rcases fsReceive rs h e with _ | ⟨rs', i', m'⟩
    · trivial
    · simp only [Option.map_some, Ty.Fits]
      have hb1 : 1 ≤ bits B_idx := one_le_bits B_idx
      have hi : bits (min i' B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      exact ⟨by omega, ⟨by omega, by omega⟩⟩
  | eqT => trivial
  | eqI => trivial
  | eqM => trivial
  | eqE => trivial
  | lamI => simp only [Ty.Fits]; omega
  | defaultE => simp only [Ty.Fits]; omega

theorem ckaSchemeOps_sizeHonest
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (SM.Construction.Header T) M E)
    (lam : I) :
    OpsSizeHonest (ckaSchemeOps cka prng fs lam) :=
  ckaOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem ckaSamplers_sizeHonest
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    SampSizeHonest
      (ckaSamplers (Γ := Γ) (T := T) (RSt := RSt) (SS := SS) (RS := RS) (M := M) (E := E)
        sampKR sampKC sampCCoins sampI sampK) := by
  intro s x B _ y _
  cases s <;> simp [Ty.Fits]

end CryptoGames.CKA

namespace CryptoGames.PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

theorem prngOps_sizeHonest
    (ckaInitA : KC → Γ)
    (ckaInitB : KC → Γ)
    (ckaSend : Γ → CCoins → Γ × T × I)
    (ckaReceive : Γ → T → Γ × I)
    (prngInit : KR → RSt)
    (prngUp : RSt → I → RSt × K)
    (fsInitSender : K → SS)
    (fsInitReceiver : K → RS)
    (fsSend : SS → SM.Construction.Header T → M → SS × E)
    (fsReceive : RS → SM.Construction.Header T → E → Option (RS × ℕ × M))
    (eqT : T → T → Bool)
    (eqI : I → I → Bool)
    (eqM : M → M → Bool)
    (eqE : E → E → Bool)
    (lam : I)
    (defaultE : E) :
    OpsSizeHonest
      (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) :=
  CKA.ckaOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem prngSchemeOps_sizeHonest
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (SM.Construction.Header T) M E)
    (lam : I) :
    OpsSizeHonest (prngSchemeOps cka prng fs lam) :=
  CKA.ckaSchemeOps_sizeHonest cka prng fs lam

theorem prngSamplers_sizeHonest
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    SampSizeHonest
      (prngSamplers (Γ := Γ) (T := T) (RSt := RSt) (SS := SS) (RS := RS) (M := M) (E := E)
        sampKR sampKC sampCCoins sampI sampK) :=
  CKA.ckaSamplers_sizeHonest sampKR sampKC sampCCoins sampI sampK

end CryptoGames.PRFPRNG

/-! ## State representations -/

namespace CryptoGames.SM.Engine

open Construction CKA
open scoped Computational.Proofs.ReductionDsl.Notation

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

section StateRepr

/-- Virtual party-state type in `ckaSig`: `(id, root, vS, vR, γ, curCkaMsg, tcur)`. -/
@[reducible] def vpTy (γvT svT ssvT vrT : Ty S) : Ty S :=
  .prod .bool
    (.prod svT
      (.prod (.opt ssvT)
        (.prod vrT
          (.prod γvT
            (.prod (.opt (.base .t)) .nat)))))

def vpEnc {γvT svT ssvT vrT : Ty S} {RSv : Type}
    (vrEnc : (ℕ → Option RSv) → vrT.denote)
    (p : VP γvT.denote T svT.denote ssvT.denote RSv) :
    (vpTy (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
      (K := K) (SS := SS) (RS := RS) (M := M) (E := E) γvT svT ssvT vrT).denote :=
  (partyEnc p.id, p.root, p.vS, vrEnc p.vR, p.γ, p.curCkaMsg, p.tcur)

def vpId
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' .bool := .fst s
def vpRoot
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' svT := .fst (.snd s)
def vpVS
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' (.opt ssvT) := .fst (.snd (.snd s))
def vpVR
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' vrT := .fst (.snd (.snd (.snd s)))
def vpΓ
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' γvT :=
  .fst (.snd (.snd (.snd (.snd s))))
def vpTcur
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' (.opt (.base .t)) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def vpTcurNat
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) : Expr O' Γ' .nat :=
  .snd (.snd (.snd (.snd (.snd (.snd s)))))

def vpMk
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (id : Expr O' Γ' .bool) (root : Expr O' Γ' svT) (vS : Expr O' Γ' (.opt ssvT))
    (vR : Expr O' Γ' vrT) (γ : Expr O' Γ' γvT) (curCkaMsg : Expr O' Γ' (.opt (.base .t)))
    (tcur : Expr O' Γ' .nat) : Expr O' Γ' (vpTy γvT svT ssvT vrT) :=
  .pair id (.pair root (.pair vS (.pair vR (.pair γ (.pair curCkaMsg tcur)))))

def vpSetVS
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) (vS : Expr O' Γ' (.opt ssvT)) :
    Expr O' Γ' (vpTy γvT svT ssvT vrT) :=
  rdslExpr =>
    letE (raw s, raw vS) (fun (s0, vS0) =>
      vpMk (vpId s0) (vpRoot s0) vS0 (vpVR s0) (vpΓ s0) (vpTcur s0) (vpTcurNat s0))

def vpSetVR
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) (vR : Expr O' Γ' vrT) :
    Expr O' Γ' (vpTy γvT svT ssvT vrT) :=
  rdslExpr =>
    letE (raw s, raw vR) (fun (s0, vR0) =>
      vpMk (vpId s0) (vpRoot s0) (vpVS s0) vR0 (vpΓ s0) (vpTcur s0) (vpTcurNat s0))

def vpSetΓ
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (s : Expr O' Γ' (vpTy γvT svT ssvT vrT)) (γ : Expr O' Γ' γvT) :
    Expr O' Γ' (vpTy γvT svT ssvT vrT) :=
  rdslExpr =>
    letE (raw s, raw γ) (fun (s0, γ0) =>
      vpMk (vpId s0) (vpRoot s0) (vpVS s0) (vpVR s0) γ0 (vpTcur s0) (vpTcurNat s0))

@[reducible] def cRecTy : Ty S := .prod posTy (.prod (.base .msg) hdrCtTy)

def cRecEnc (r : Record M (Header T × E)) : (Bool × ℕ × ℕ) × M × (Header T × E) :=
  (posEnc r.pos, r.msg, r.ct)

def cRecPos
    {O' : Ops S} {Γ'} (r : Expr O' Γ' cRecTy) : Expr O' Γ' posTy := .fst r
def cRecMsg
    {O' : Ops S} {Γ'} (r : Expr O' Γ' cRecTy) : Expr O' Γ' (.base .msg) := .fst (.snd r)
def cRecCt
    {O' : Ops S} {Γ'} (r : Expr O' Γ' cRecTy) : Expr O' Γ' hdrCtTy := .snd (.snd r)

/-- Virtual `GameState VPt M (Header T × E)` (`Ctx`) as a `ReductionDsl` type in `ckaSig`. -/
@[reducible] def cGsTy (vpT : Ty S) : Ty S :=
  .prod (.prod vpT vpT)
    (.prod .bool
      (.prod .bool
        (.prod (.prod .nat .nat)
          (.prod (.prod .nat .nat)
            (.prod (.opt .nat)
              (.prod (.list cRecTy)
                (.prod (.list posTy)
                  (.prod (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool)))
                    (.prod (.prod (.tbl .nat) (.tbl .nat))
                      (.prod (.list .nat)
                        (.list (.prod .bool .nat))))))))))))

def cGsEnc {vpT : Ty S} {VPt : Type} (vpEncFn : VPt → vpT.denote)
    (s : GameState VPt M (Header T × E)) :
    (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E vpT).denote :=
  ((vpEncFn (s.st .A), vpEncFn (s.st .B)),
   (s.b,
    (s.win,
     ((s.epoch .A, s.epoch .B),
      ((s.idx .A, s.idx .B),
       (s.tL,
        (s.trans.map cRecEnc,
         (s.chall.map posEnc,
          (((fun ep idx => s.comp.contains ⟨.A, ep, idx⟩),
            (fun ep idx => s.comp.contains ⟨.B, ep, idx⟩)),
           ((s.maxAcc .A, s.maxAcc .B),
            (s.leaks,
             s.corrs.map (fun pe => (partyEnc pe.1, pe.2)))))))))))))

def cGsSt
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.prod vpT vpT) := .fst s
def cGsB
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' .bool :=
  .fst (.snd s)
def cGsWin
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' .bool :=
  .fst (.snd (.snd s))
def cGsEpoch
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))
def cGsIdx
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))
def cGsTL
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def cGsTrans
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.list cRecTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def cGsChall
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def cGsComp
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def cGsMaxAcc
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def cGsLeaks
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))
def cGsCorrs
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def cGsMk
    {O' : Ops S} {vpT : Ty S} {Γ'}
    (st : Expr O' Γ' (.prod vpT vpT))
    (b win : Expr O' Γ' .bool)
    (epoch idx : Expr O' Γ' (.prod .nat .nat))
    (tL : Expr O' Γ' (.opt .nat))
    (trans : Expr O' Γ' (.list cRecTy))
    (chall : Expr O' Γ' (.list posTy))
    (comp : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (maxAcc : Expr O' Γ' (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ' (.list .nat))
    (corrs : Expr O' Γ' (.list (.prod .bool .nat))) : Expr O' Γ' (cGsTy vpT) :=
  .pair st
    (.pair b
      (.pair win
        (.pair epoch
          (.pair idx
            (.pair tL
              (.pair trans
                (.pair chall
                  (.pair comp
                    (.pair maxAcc
                      (.pair leaks corrs))))))))))

def cGsSetWin
    {O' : Ops S} {vpT : Ty S} {Γ'}
    (s : Expr O' Γ' (cGsTy vpT)) (w : Expr O' Γ' .bool) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw w) (fun (s0, w0) =>
      cGsMk (cGsSt s0) (cGsB s0) w0 (cGsEpoch s0) (cGsIdx s0) (cGsTL s0)
        (cGsTrans s0) (cGsChall s0) (cGsComp s0) (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0))

def cGsSetStP
    {O' : Ops S} {vpT : Ty S} {Γ'}
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) :
    Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw p, raw st') (fun (s0, p0, st0) =>
      cGsMk (pSet (cGsSt s0) p0 st0) (cGsB s0) (cGsWin s0) (cGsEpoch s0) (cGsIdx s0) (cGsTL s0)
        (cGsTrans s0) (cGsChall s0) (cGsComp s0) (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0))

def cGsInitE
    {O' : Ops S} {vpT : Ty S} {Γ'}
    (vA vB : Expr O' Γ' vpT) (b : Expr O' Γ' .bool) : Expr O' Γ' (cGsTy vpT) :=
  cGsMk (.pair vA vB) b (.bool false)
    (.pair (.nat 0) (.nat 0)) (.pair (.nat 0) (.nat 0)) .none
    .nil .nil
    (.pair (.tconst (.tconst (.bool false))) (.tconst (.tconst (.bool false))))
    (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .nil .nil

/-- Engine state `EState` encoded in `ckaSig` as `(g, (h, abort))`. -/
@[reducible] def esTy (vpT hsT : Ty S) : Ty S :=
  .prod (cGsTy vpT) (.prod hsT .bool)

def esEnc {vpT hsT : Ty S} {VPt HS : Type}
    (vpEncFn : VPt → vpT.denote) (hsEncFn : HS → hsT.denote)
    (es : EState VPt M (Header T × E) HS) :
    (@esTy KC Γ CCoins T I KR RSt K SS RS M E vpT hsT).denote :=
  (cGsEnc vpEncFn es.g, hsEncFn es.h, es.abort)

def esG
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) :
    Expr O' Γ' (cGsTy vpT) := .fst es
def esH
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) :
    Expr O' Γ' hsT := .fst (.snd es)
def esAbort
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) :
    Expr O' Γ' .bool := .snd (.snd es)
def esMk
    {O' : Ops S} {vpT hsT : Ty S} {Γ'}
    (g : Expr O' Γ' (cGsTy vpT)) (h : Expr O' Γ' hsT) (abort : Expr O' Γ' .bool) :
    Expr O' Γ' (esTy vpT hsT) :=
  .pair g (.pair h abort)

end StateRepr

/-! ## Pure bookkeeping and evaluation agreement -/

section Bookkeeping

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

def optNatLit
    {S' : Sig} {O' : Ops S'} {Γ'} : Option ℕ → Expr O' Γ' (.opt .nat)
  | none => .none
  | some n => .some (.nat n)

@[simp] theorem optNatLit_eval {S' : Sig} {O' : Ops S'} {Γ'} (o : Option ℕ) (ρ : Env Γ') :
    (optNatLit (O' := O') o).eval ρ = o := by
  cases o <;> rfl

def optTEqE {Γ'} (a b : Expr OO Γ' (.opt (.base .t))) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (raw a, raw b) (fun (x, y) =>
      match x with
      | none =>
        match y with
        | none => true
        | some _ => false
      | some xv =>
        match y with
        | none => false
        | some yv => Expr.op (O := OO) CKAOp.eqT (xv, yv))

def hdrCtEqE {Γ'} (c₁ c₂ : Expr OO Γ' hdrCtTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (raw c₁, raw c₂) (fun (a, b) =>
      ((a.1.1 == b.1.1) && optTEqE a.1.2 b.1.2) &&
        Expr.op (O := OO) CKAOp.eqE (a.2, b.2))

theorem optTEqE_eval [DecidableEq T] {Γ'}
    (a b : Expr OO Γ' (.opt (.base .t))) (ρ : Env Γ')
    (heqT : eqT = (· == ·)) :
    (optTEqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp only [optTEqE, ckaOps, heqT, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ]
  rcases a.eval ρ with _ | x <;> rcases b.eval ρ with _ | y <;> rfl

theorem hdrCtEqE_eval [DecidableEq T] [DecidableEq E] {Γ'}
    (c₁ c₂ : Expr OO Γ' hdrCtTy) (ρ : Env Γ')
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·)) :
    (hdrCtEqE c₁ c₂).eval ρ = (c₁.eval ρ == c₂.eval ρ) := by
  rcases h1 : c₁.eval ρ with ⟨⟨t₁, o₁⟩, e₁⟩
  rcases h2 : c₂.eval ρ with ⟨⟨t₂, o₂⟩, e₂⟩
  simp only [hdrCtEqE, ckaOps, heqE, Expr.eval, Expr.v0, Env.get_cons_zero, h1, h2]
  rw [optTEqE_eval _ _ _ heqT]
  simp only [Expr.eval, Env.get_cons_zero]
  by_cases ht : t₁ = t₂ <;> cases o₁ <;> cases o₂ <;> by_cases he : e₁ = e₂ <;>
    simp [ht, he, BEq.beq]

def cSafeChE
    {O' : Ops S} {vpT : Ty S} {Γ'} (Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s, raw p) (fun (s0, p0) =>
      healedByE (cGsTL s0) (raw Δ) (pGet (cGsEpoch s0) p0))

def cSafeInjE
    {O' : Ops S} {vpT : Ty S} {Γ'} (Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT)) :
    Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s) (fun s0 =>
      healedByE (cGsTL s0) (raw Δ) (minN (cGsEpoch s0).1 (cGsEpoch s0).2))

def cLeakE
    {O' : Ops S} {vpT : Ty S} {Γ'} (s : Expr O' Γ' (cGsTy vpT))
    (l : Expr O' Γ' .nat) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw l) (fun (s0, l0) =>
      let m := maxOptE (cGsTL s0) l0
      cGsMk (cGsSt s0) (cGsB s0) (cGsWin s0) (cGsEpoch s0) (cGsIdx s0)
        (some m) (cGsTrans s0) (cGsChall s0) (cGsComp s0) (cGsMaxAcc s0)
        (m :: cGsLeaks s0) (cGsCorrs s0))

def cEpMgmtE
    {O' : Ops S} {vpT : Ty S} {Γ'} (Δ qep : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (bad : Expr O' Γ' .bool) : Expr O' Γ' (.opt (cGsTy vpT)) :=
  rdslExpr =>
    letE (raw s, raw p, raw bad) (fun (s0, p0, bad0) =>
      let epP := pGet (cGsEpoch s0) p0
      let epNext := epP + 1
      if sendsInE p0 epNext then
        if nat qep < epNext then
          none
        else
          letE (if bad0 && !(cSafeChE (raw Δ) s0 p0) then cLeakE s0 epNext else s0) (fun s1 =>
            let ep1 := pGet (cGsEpoch s1) p0 + 1
            some (cGsMk (cGsSt s1) (cGsB s1) (cGsWin s1)
              (pSet (cGsEpoch s1) p0 ep1)
              (pSet (cGsIdx s1) p0 0)
              (cGsTL s1) (cGsTrans s1) (cGsChall s1) (cGsComp s1)
              (cGsMaxAcc s1) (cGsLeaks s1) (cGsCorrs s1)))
      else
        if nat qep < epP then none else some s0)

def cCompSetE
    {O' : Ops S} {Γ'}
    (m : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (pos : Expr O' Γ' posTy) (val : Expr O' Γ' .bool) :
    Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) :=
  .letE (.pair m (.pair pos val))
    (let m0 : Expr O' _ (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) := .fst .v0
     let pos0 : Expr O' _ posTy := .fst (.snd .v0)
     let val0 : Expr O' _ .bool := .snd (.snd .v0)
     let sub := pGet m0 (posSender pos0)
     let row := .tget sub (posEpoch pos0)
     pSet m0 (posSender pos0) (.tset sub (posEpoch pos0) (.tset row (posIdx pos0) val0)))

def cCompInsertE
    {O' : Ops S} {Γ'}
    (m : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (pos : Expr O' Γ' posTy) :
    Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) :=
  cCompSetE m pos (.bool true)

def cCompDeleteE
    {O' : Ops S} {Γ'}
    (m : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (pos : Expr O' Γ' posTy) :
    Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))) :=
  cCompSetE m pos (.bool false)

def cCompContainsE
    {O' : Ops S} {vpT : Ty S} {Γ'} (_L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) : Expr O' Γ' .bool :=
  .letE (.pair s pos)
    (let s0 : Expr O' _ (cGsTy vpT) := .fst .v0
     let pos0 : Expr O' _ posTy := .snd .v0
     .tget (.tget (pGet (cGsComp s0) (posSender pos0)) (posEpoch pos0)) (posIdx pos0))

def cRecordE
    {O' : Ops S} {vpT : Ty S} {Γ'} (_L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (r : Expr O' Γ' cRecTy)
    (isChall : Expr O' Γ' .bool) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw p, raw st', raw r, raw isChall) (fun (s0, p0, st0, r0, ch0) =>
      let pos := cRecPos r0
      cGsMk
        (pSet (cGsSt s0) p0 st0)
        (cGsB s0) (cGsWin s0) (cGsEpoch s0)
        (pSet (cGsIdx s0) p0 (posIdx pos))
        (cGsTL s0)
        (r0 :: cGsTrans s0)
        (if ch0 then pos :: cGsChall s0 else cGsChall s0)
        (if cSafeChE (raw Δ) s0 p0 then cGsComp s0 else cCompInsertE (cGsComp s0) pos)
        (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0))

def cInTransitE {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr OO Γ' (cGsTy vpT))
    (qParty : Expr OO Γ' .bool) (c : Expr OO Γ' hdrCtTy) : Expr OO Γ' (.opt cRecTy) :=
  rdslExpr =>
    letE (raw s, raw qParty, raw c) (fun (s0, q0, c0) =>
      findB L (cGsTrans s0) (fun r0 =>
        boolEq (posSender (cRecPos r0)) q0 && hdrCtEqE (cRecCt r0) c0))

def cDeleteE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw pos) (fun (s0, pos0) =>
      let trans' :=
        foldrB L (cGsTrans s0) [] (fun r0 acc =>
          if !(posEq (cRecPos r0) pos0) then r0 :: acc else acc)
      let chall' :=
        foldrB L (cGsChall s0) [] (fun x acc =>
          if !(posEq x pos0) then x :: acc else acc)
      let comp' := cCompDeleteE (cGsComp s0) pos0
      cGsMk (cGsSt s0) (cGsB s0) (cGsWin s0) (cGsEpoch s0) (cGsIdx s0) (cGsTL s0)
        trans' chall' comp' (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0))

def cAcceptE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (pos : Expr O' Γ' posTy) :
    Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (cDeleteE (raw L) (raw s) (raw pos), raw p, raw st', raw pos) (fun (s1, p0, st0, pos0) =>
      let pEpoch := posEpoch pos0
      let pIdx := posIdx pos0
      cGsMk
        (pSet (cGsSt s1) p0 st0)
        (cGsB s1) (cGsWin s1)
        (pSet (cGsEpoch s1) p0 (maxN (pGet (cGsEpoch s1) p0) pEpoch))
        (cGsIdx s1) (cGsTL s1) (cGsTrans s1) (cGsChall s1) (cGsComp s1)
        (maxAccSet (cGsMaxAcc s1) p0 pEpoch
          (maxN (maxAccGet (cGsMaxAcc s1) p0 pEpoch) pIdx))
        (cGsLeaks s1) (cGsCorrs s1))

def cChallContainsE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s, raw pos) (fun (s0, pos0) =>
      anyB L (cGsChall s0) (fun x => posEq x pos0))

def cMustBeCorrectE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L maxSkip : ℕ)
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (r : Expr O' Γ' cRecTy) :
    Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s, raw p, raw r) (fun (s0, p0, r0) =>
      let pos := cRecPos r0
      !(cCompContainsE (raw L) s0 pos) &&
        leN (posIdx pos)
          ((maxAccGet (cGsMaxAcc s0) p0 (posEpoch pos) + nat maxSkip) + 1))

def cTrivialE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s, raw pos) (fun (s0, pos0) =>
      orE (cCompContainsE (raw L) s0 pos0)
        (!(anyB L (cGsTrans s0) (fun r0 => posEq (cRecPos r0) pos0)) &&
          !(healedByE (cGsTL s0) (raw Δ) (posEpoch pos0))))

def cCorrAllowedE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw s, raw p) (fun (s0, p0) =>
      !(anyB L (cGsChall s0) (fun x => boolEq (posSender x) (otherE p0))) &&
        !(anyB L (cGsTrans s0) (fun r0 =>
          boolEq (posSender (cRecPos r0)) (otherE p0) &&
            !(cCompContainsE (raw L) s0 (cRecPos r0)))))

def cAfterCorrE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) : Expr O' Γ' (cGsTy vpT) :=
  rdslExpr =>
    letE (raw s, raw p) (fun (s0, p0) =>
      let comp' :=
        foldrB L (cGsTrans s0) (cGsComp s0) (fun r0 acc =>
          if boolEq (posSender (cRecPos r0)) (otherE p0)
          then cCompInsertE acc (cRecPos r0) else acc)
      let s1 :=
        cGsMk (cGsSt s0) (cGsB s0) (cGsWin s0) (cGsEpoch s0) (cGsIdx s0) (cGsTL s0)
          (cGsTrans s0) (cGsChall s0) comp' (cGsMaxAcc s0) (cGsLeaks s0) (cGsCorrs s0)
      let s2 :=
        cLeakE s1 (maxN (cGsEpoch s0).1 (cGsEpoch s0).2)
      cGsMk (cGsSt s2) (cGsB s2) (cGsWin s2) (cGsEpoch s2) (cGsIdx s2) (cGsTL s2)
        (cGsTrans s2) (cGsChall s2) (cGsComp s2) (cGsMaxAcc s2) (cGsLeaks s2)
        ((p0, pGet (cGsEpoch s0) p0) :: cGsCorrs s2))

def cCanonE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (tStar : Expr O' Γ' .nat)
    (s : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' (.opt .nat) :=
  rdslExpr =>
    letE (raw tStar, raw s) (fun (t0, s0) =>
      foldrB L (cGsLeaks s0) none (fun lk acc =>
        if lk < t0 then
          match acc with
          | none => some lk
          | some prev => some (maxN lk prev)
        else
          acc))

def cAuthOKE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L Δ : ℕ) (tLStar : Expr O' Γ' (.opt .nat))
    (tStar : Expr O' Γ' .nat) (s : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw tLStar, raw tStar, raw s) (fun (tL0, t0, s0) =>
      let leaksOK :=
        !(anyB L (cGsLeaks s0) (fun lk => ltOptE tL0 lk && (lk < t0)))
      let corrsOK :=
        !(anyB L (cGsCorrs s0) (fun pe =>
          boolEq pe.1 (receiverOfE t0) && ltOptE tL0 pe.2))
      ((validGuessE (raw Δ) tL0 t0 && optNatEqE (cCanonE (raw L) t0 s0) tL0) && leaksOK) &&
        corrsOK)

def leakDoomE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (π : Policy)
    (g g' : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw g, raw g') (fun (g0, g1) =>
      let ev1 :=
        anyB L (cGsLeaks g1) (fun lk =>
          ltOptE (optNatLit (raw π.tL)) lk && (lk < nat π.tStar))
      let ev2 :=
        anyB L (cGsLeaks g1) (fun lk => leN (nat π.tStar) lk) &&
          (pGet (cGsEpoch g0) (bool (partyEnc (Party.senderOf π.tStar))) < nat π.tStar)
      orE ev1 ev2)

def corrDoomE
    {O' : Ops S} {vpT : Ty S} {Γ'} (π : Policy)
    (g : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw g, raw p) (fun (g0, p0) =>
      let epP := pGet (cGsEpoch g0) p0
      let authBr := ltOptE (optNatLit (raw π.tL)) epP
      let privBr := (epP < nat π.tStar) &&
        leN (nat π.tStar) (maxN (cGsEpoch g0).1 (cGsEpoch g0).2)
      boolEq p0 (bool (partyEnc (Party.receiverOf π.tStar))) &&
        raw (if π.auth then authBr else privBr))

def authOutE
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (L Δ : ℕ) (π : Policy)
    (es : Expr O' Γ' (esTy vpT hsT)) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw es) (fun es0 =>
      (!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw Δ) (optNatLit (raw π.tL)) (nat π.tStar) (esG es0))

def privValidE
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (L Δ : ℕ) (π : Policy)
    (es : Expr O' Γ' (esTy vpT hsT)) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (raw es) (fun es0 =>
      (!(esAbort es0) && validGuessE (raw Δ) (optNatLit (raw π.tL)) (nat π.tStar)) &&
        optNatEqE (cCanonE (raw L) (nat π.tStar) (esG es0)) (optNatLit (raw π.tL)))

def privOutC
    {O' : Ops S} {ι : Type} {TSpec : OracleSpec ι} {I' : Iface S TSpec}
    {vpT hsT : Ty S} (L Δ : ℕ) (π : Policy)
    (drawBit : ∀ {Γ''}, Comp O' I' Γ'' .bool)
    {Γ'} (b b' : Expr O' Γ' .bool) (es : Expr O' Γ' (esTy vpT hsT)) : Comp O' I' Γ' .bool :=
  rdsl do
    if privValidE (raw L) (raw Δ) (raw π) (raw es) then
      return boolEq (raw b) (raw b')
    else
      raw (drawBit (Γ'' := Γ'))

variable {vpT : Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E)} {VPt : Type}
  (vpEncFn : VPt → vpT.denote)

theorem cSafeChE_eval {O' : Ops S} {Γ'} (Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (P : Party)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (cSafeChE Δ s p).eval ρ = st.safeCh Δ P := by
  simp only [cSafeChE, Expr.eval, hs, hp, healedByE_eval]
  cases P <;> simp [GameState.safeCh, cGsTL, cGsEpoch, pGet, Expr.eval, Expr.v0, cGsEnc, partyEnc]

theorem cSafeInjE_eval {O' : Ops S} {Γ'} (Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (ρ : Env Γ') (st : GameState VPt M (Header T × E))
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) :
    (cSafeInjE Δ s).eval ρ = st.safeInj Δ := by
  simp only [cSafeInjE, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, cGsTL, cGsEpoch, Expr.eval, Expr.v0, cGsEnc]

theorem cLeakE_eval {O' : Ops S} {Γ'} (s : Expr O' Γ' (cGsTy vpT))
    (l : Expr O' Γ' .nat) (ρ : Env Γ') (st : GameState VPt M (Header T × E))
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) :
    (cLeakE s l).eval ρ = cGsEnc (vpT := vpT) vpEncFn (st.leak (l.eval ρ)) := by
  simp only [cLeakE, cGsMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL, cGsTrans, cGsChall,
    cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs, Expr.eval, Expr.v0, cGsEnc]

theorem cEpMgmtE_eval {O' : Ops S} {Γ'} (Δ qep : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (bad : Expr O' Γ' .bool) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (cEpMgmtE Δ qep s p bad).eval ρ =
      (st.epMgmt Δ qep P (bad.eval ρ)).map (cGsEnc (vpT := vpT) vpEncFn) := by
  unfold cEpMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ =
      (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) (.prod .bool .bool))
    (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = P.sendsIn (st.epoch P + 1) := by
    rw [sendsInE_eval _ _ ρ₁ P rfl]
    congr 1
    cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : P.sendsIn (st.epoch P + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (cGsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch P + 1) := by
      cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch P + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (cSafeChE Δ (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh Δ P)) := by
        have hsafe := cSafeChE_eval vpEncFn Δ (.fst (Expr.v0 (O := O')))
          (.fst (.snd (Expr.v0 (O := O')))) ρ₁ st P rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (cLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (cGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = cGsEnc (vpT := vpT) vpEncFn (st.leak (st.epoch P + 1)) := by
        rw [cLeakE_eval vpEncFn (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = cGsEnc (vpT := vpT) vpEncFn st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh Δ P)) = true then st.leak (st.epoch P + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh Δ P)) = true
          then cGsEnc (vpT := vpT) vpEncFn (st.leak (st.epoch P + 1))
          else cGsEnc (vpT := vpT) vpEncFn st) = cGsEnc (vpT := vpT) vpEncFn st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases P <;>
        simp [ρ₁, cGsMk, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL, cGsTrans, cGsChall, cGsComp,
          cGsMaxAcc, cGsLeaks, cGsCorrs, pGet, pSet, cGsEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (cGsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch P) := by
      cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch P <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

def compTblEnc (l : List Pos) : (ℕ → ℕ → Bool) × (ℕ → ℕ → Bool) :=
  ((fun ep idx => l.contains ⟨.A, ep, idx⟩),
   (fun ep idx => l.contains ⟨.B, ep, idx⟩))

theorem cCompInsertE_eval {O' : Ops S} {Γ'}
    (m : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (l : List Pos) (p₀ : Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = posEnc p₀) :
    (cCompInsertE m pos).eval ρ = compTblEnc (p₀ :: l) := by
  rcases p₀ with ⟨sender, ep₀, idx₀⟩
  cases sender
  · simp only [cCompInsertE, cCompSetE, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq]
    constructor
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
  · simp only [cCompInsertE, cCompSetE, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero, ↓reduceIte, Prod.mk.injEq]
    constructor
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]

theorem cCompDeleteE_eval {O' : Ops S} {Γ'}
    (m : Expr O' Γ' (.prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (l : List Pos) (p₀ : Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = posEnc p₀) :
    (cCompDeleteE m pos).eval ρ = compTblEnc (l.filter (· != p₀)) := by
  rcases p₀ with ⟨sender, ep₀, idx₀⟩
  cases sender
  · simp only [cCompDeleteE, cCompSetE, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq]
    constructor
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
  · simp only [cCompDeleteE, cCompSetE, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0,
      Env.get_cons_zero, ↓reduceIte, Prod.mk.injEq]
    constructor
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]

theorem cCompContainsE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (pos₀ : Pos)
    (_hComp : st.comp.dedup.length ≤ L) (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (cCompContainsE L s pos).eval ρ = st.comp.contains pos₀ := by
  rcases pos₀ with ⟨sender, ep, idx⟩
  cases sender <;>
    simp [cCompContainsE, cGsComp, posSender, posEpoch, posIdx, pGet,
      hs, hpos, cGsEnc, posEnc, partyEnc, Expr.eval, Expr.v0]

theorem cRecordE_eval {O' : Ops S} {Γ'} (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (r : Expr O' Γ' cRecTy)
    (isChall : Expr O' Γ' .bool) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party) (st₀ : VPt)
    (rec_ : Record M (Header T × E))
    (_hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P)
    (hst : st'.eval ρ = vpEncFn st₀) (hr : r.eval ρ = cRecEnc rec_) :
    (cRecordE L Δ s p st' r isChall).eval ρ =
      cGsEnc (vpT := vpT) vpEncFn (st.record Δ P st₀ rec_ (isChall.eval ρ)) := by
  unfold cRecordE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p (.pair st' (.pair r isChall)))).eval ρ =
      (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P, vpEncFn st₀, cRecEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hst, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) (.prod .bool (.prod vpT (.prod cRecTy .bool))))
    (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P, vpEncFn st₀, cRecEnc rec_, isChall.eval ρ) ρ
  have hSafe : (cSafeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh Δ P :=
    cSafeChE_eval vpEncFn Δ (.fst .v0) (.fst (.snd .v0)) ρ₁ st P rfl rfl
  have hIns : (cCompInsertE (cGsComp (.fst (Expr.v0 (O := O'))))
      (cRecPos (.fst (.snd (.snd (.snd .v0)))))).eval ρ₁ =
      compTblEnc (rec_.pos :: st.comp) :=
    cCompInsertE_eval (cGsComp (.fst .v0)) (cRecPos (.fst (.snd (.snd (.snd .v0)))))
      ρ₁ st.comp rec_.pos rfl rfl
  simp only [cGsMk, Expr.eval, hSafe, hIns]
  cases P <;> cases hch : isChall.eval ρ <;> cases hsafe : st.safeCh Δ _ <;>
    simp [ρ₁, GameState.record, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL, cGsTrans,
      cGsChall, cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs, cRecPos, posIdx, pSet,
      hch, hsafe, cGsEnc, compTblEnc, cRecEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]

theorem cGsSetWin_eval {O' : Ops S} {Γ'} (s : Expr O' Γ' (cGsTy vpT))
    (w : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E))
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) :
    (cGsSetWin s w).eval ρ = cGsEnc (vpT := vpT) vpEncFn { st with win := w.eval ρ } := by
  simp [cGsSetWin, cGsMk, cGsSt, cGsB, cGsEpoch, cGsIdx, cGsTL, cGsTrans, cGsChall, cGsComp,
    cGsMaxAcc, cGsLeaks, cGsCorrs, hs, cGsEnc, Expr.eval, Expr.v0]

theorem cGsSetStP_eval {O' : Ops S} {Γ'} (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party) (st₀ : VPt)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P)
    (hst : st'.eval ρ = vpEncFn st₀) :
    (cGsSetStP s p st').eval ρ =
      cGsEnc (vpT := vpT) vpEncFn { st with st := Function.update st.st P st₀ } := by
  cases P <;>
    simp [cGsSetStP, cGsMk, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL, cGsTrans,
      cGsChall, cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs, pSet, hs, hp, hst, cGsEnc,
      partyEnc, Function.update, Expr.eval, Expr.v0]

theorem cInTransitE_eval [DecidableEq T] [DecidableEq E] {Γ'} (L : ℕ)
    (s : Expr OO Γ' (cGsTy vpT)) (qParty : Expr OO Γ' .bool) (c : Expr OO Γ' hdrCtTy)
    (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (Q : Party)
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·))
    (hL : st.trans.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hq : qParty.eval ρ = partyEnc Q) :
    (cInTransitE L s qParty c).eval ρ = (st.inTransit Q (c.eval ρ)).map cRecEnc := by
  have htake : ((st.trans.map cRecEnc).take L) = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hL)
  simp only [cInTransitE, GameState.inTransit, cGsTrans, cRecPos, posSender, cRecCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, hs, hq, cGsEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  rw [hdrCtEqE_eval _ _ _ heqT heqE]
  cases sender <;> cases Q <;>
  · by_cases h : ct = c.eval ρ <;>
      simp [cRecEnc, posEnc, partyEnc, Expr.eval, Env.get_cons_zero, Env.get_cons_succ, h]

theorem cDeleteE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (p : Pos)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (_hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : pos.eval ρ = posEnc p) :
    (cDeleteE L s pos).eval ρ = cGsEnc (vpT := vpT) vpEncFn (st.delete p) := by
  have ht1 : (st.trans.map cRecEnc).take L = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  unfold cDeleteE
  rw [letE_eval]
  have h0 : (Expr.pair s pos).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, posEnc p) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) posTy) (cGsEnc (vpT := vpT) vpEncFn st, posEnc p) ρ
  have hdel := cCompDeleteE_eval (cGsComp (.fst (Expr.v0 (O := O')))) (.snd .v0)
    ρ₁ st.comp p rfl rfl
  simp only [GameState.delete, cGsMk, Expr.eval, hdel]
  simp only [ρ₁, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL,
    cGsTrans, cGsChall, cGsMaxAcc, cGsLeaks, cGsCorrs, cRecPos, compTblEnc,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, cGsEnc, ht1, ht2]
  rw [foldr_filter_map, foldr_filter_map]
  simp [cRecEnc, posDec_posEnc, bne]

theorem cAcceptE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (st' : Expr O' Γ' vpT) (pos : Expr O' Γ' posTy) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party) (st₀ : VPt) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P)
    (hst : st'.eval ρ = vpEncFn st₀) (hpos : pos.eval ρ = posEnc pos₀) :
    (cAcceptE L s p st' pos).eval ρ = cGsEnc (vpT := vpT) vpEncFn (st.accept P st₀ pos₀) := by
  have hdel := cDeleteE_eval vpEncFn L s pos ρ st pos₀ hTrans hChall hComp hs hpos
  simp only [cAcceptE, cGsMk, Expr.eval, hdel, hp, hst, hpos]
  cases P <;>
  · simp [GameState.accept, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL, cGsTrans,
      cGsChall, cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, cGsEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

theorem cChallContainsE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (pos₀ : Pos)
    (hChall : st.chall.length ≤ L) (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (cChallContainsE L s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [cChallContainsE, cGsChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, cGsEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

theorem cMustBeCorrectE_eval {O' : Ops S} {Γ'} (L maxSkip : ℕ)
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (r : Expr O' Γ' cRecTy) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party) (rec_ : Record M (Header T × E))
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P)
    (hr : r.eval ρ = cRecEnc rec_) :
    (cMustBeCorrectE L maxSkip s p r).eval ρ = st.mustBeCorrect maxSkip P rec_ := by
  simp only [cMustBeCorrectE, Expr.eval, hs, hp, hr, leN_eval]
  rw [cCompContainsE_eval vpEncFn L _ _ _ st rec_.pos hComp rfl rfl]
  cases P <;>
  simp [GameState.mustBeCorrect, cRecPos, posIdx, posEpoch, maxAccGet, pGet,
    cGsMaxAcc, cGsEnc, cRecEnc, posEnc, partyEnc, Expr.eval, Expr.v0]

theorem cTrivialE_eval {O' : Ops S} {Γ'} (L Δ : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ L) (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hpos : pos.eval ρ = posEnc pos₀) :
    (cTrivialE L Δ s pos).eval ρ = st.trivial Δ pos₀ := by
  have ht : (st.trans.map cRecEnc).take L = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [cTrivialE, Expr.eval, hs, hpos, orE_eval, healedByE_eval]
  rw [cCompContainsE_eval vpEncFn L _ _ _ st pos₀ hComp rfl rfl]
  simp only [GameState.trivial, cGsTrans, cGsTL, cRecPos, posEpoch,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    posEq_eval, cGsEnc, ht]
  rw [any_map_eq]
  simp [cRecEnc, posEnc, posDec]

theorem cCorrAllowedE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (P : Party)
    (hTrans : st.trans.length ≤ L) (hChall : st.chall.length ≤ L)
    (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (cCorrAllowedE L s p).eval ρ = st.corrAllowed P := by
  unfold cCorrAllowedE GameState.corrAllowed
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) .bool) (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) ρ
  have htCh : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map cRecEnc).take L = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (cGsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  have hTr0 : (cGsTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.trans.map cRecEnc := rfl
  simp only [Expr.eval, hCh0, hTr0, htCh, htTr]
  congr 1
  · congr 1
    rw [any_map_eq]
    congr 1; funext pos
    simp [ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval,
      Expr.v0, Expr.v1]
  · congr 1
    rw [any_map_eq]
    congr 1; funext r
    have hcomp := cCompContainsE_eval vpEncFn (O' := O') L (.fst .v1) (cRecPos .v0)
      (Env.cons (t := cRecTy) (cRecEnc r) ρ₁) st r.pos hComp rfl rfl
    simp only [hcomp]
    simp [ρ₁, cRecPos, posSender, otherE, cRecEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v1]

theorem foldr_cCompInsert_map {O' : Ops S} {Γ'}
    (pE : Expr O' (cRecTy :: .prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool)) :: Γ') .bool)
    (ρ₁ : Env Γ') (P : Party)
    (hpE : ∀ x acc, pE.eval (Env.cons x (Env.cons acc ρ₁)) = partyEnc P)
    (trs : List (Record M (Header T × E))) (l₀ : List Pos) :
    List.foldr
      (fun x acc =>
        if (boolEq (posSender (cRecPos .v0)) (otherE pE)).eval
            (Env.cons x (Env.cons acc ρ₁)) = true then
          (cCompInsertE (O' := O') .v1 (cRecPos .v0)).eval (Env.cons x (Env.cons acc ρ₁))
        else
          (Expr.v1 (O := O')).eval (Env.cons x (Env.cons acc ρ₁)))
      (compTblEnc l₀) (trs.map cRecEnc) =
    compTblEnc ((trs.filter (fun r => r.pos.sender == P.other)).map Record.pos ++ l₀) := by
  induction trs with
  | nil => rfl
  | cons r trs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    have hcond : (boolEq (posSender (cRecPos .v0)) (otherE pE)).eval
        (Env.cons (cRecEnc r) (Env.cons
          (compTblEnc ((trs.filter (fun r => r.pos.sender == P.other)).map Record.pos ++ l₀))
          ρ₁)) = (r.pos.sender == P.other) := by
      simp [boolEq_eval, otherE, hpE, cRecPos, posSender, cRecEnc, posEnc,
        ← partyEnc_other, partyEnc_beq, Expr.eval, Expr.v0]
    rw [hcond]
    by_cases hr : (r.pos.sender == P.other) = true
    · simp only [hr, ↓reduceIte, List.filter_cons_of_pos, List.map_cons, List.cons_append]
      exact cCompInsertE_eval (O' := O') .v1 (cRecPos .v0) _ _ r.pos rfl rfl
    · simp [hr, Expr.eval, Expr.v1]

theorem cAfterCorrE_eval {O' : Ops S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (P : Party)
    (hTrans : st.trans.length ≤ L)
    (_hCompU : ∃ U : List Pos, U.length ≤ L ∧ (∀ r ∈ st.trans, r.pos ∈ U) ∧ (∀ p ∈ st.comp, p ∈ U))
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (cAfterCorrE L s p).eval ρ = cGsEnc (vpT := vpT) vpEncFn (st.afterCorr P) := by
  unfold cAfterCorrE
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) .bool) (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) ρ
  have ht : (st.trans.map cRecEnc).take L = st.trans.map cRecEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hfold := foldr_cCompInsert_map (O' := O') (.snd .v2) ρ₁ P
    (fun _ _ => rfl) st.trans st.comp
  simp only [cLeakE, maxOptE, cGsMk, cGsSt, cGsB, cGsWin, cGsEpoch, cGsIdx, cGsTL,
    cGsTrans, cGsChall, cGsComp, cGsMaxAcc, cGsLeaks, cGsCorrs,
    Expr.eval, maxN_eval]
  have hTr0 : ((Expr.v0 (O := O')).eval ρ₁).1.2.2.2.2.2.2.1 = st.trans.map cRecEnc := rfl
  have hCp0 : ((Expr.v0 (O := O')).eval ρ₁).1.2.2.2.2.2.2.2.2.1 = compTblEnc st.comp := rfl
  rw [hTr0, ht, hCp0, hfold]
  cases P <;>
  · simp only [ρ₁, GameState.afterCorr, GameState.leak, maxOpt, pGet, partyEnc, cGsEnc, compTblEnc,
      Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    cases st.tL <;> rfl

theorem cCanonE_eval {O' : Ops S} {Γ'} (L : ℕ) (tStar : Expr O' Γ' .nat)
    (s : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ') (st : GameState VPt M (Header T × E))
    (hLeaks : st.leaks.length ≤ L) (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) :
    (cCanonE L tStar s).eval ρ = canon (tStar.eval ρ) st := by
  have ht : st.leaks.take L = st.leaks := List.take_of_length_le hLeaks
  simp only [cCanonE, canon, cGsLeaks, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, hs, cGsEnc, ht]
  rw [← foldr_filter_max? (tStar.eval ρ) st.leaks]
  congr 1; funext x acc
  by_cases h : x < tStar.eval ρ
  · cases acc <;> simp [h, maxN_eval, Expr.eval]
  · simp [h]

theorem cAuthOKE_eval {O' : Ops S} {Γ'} (L Δ : ℕ) (tLStar : Expr O' Γ' (.opt .nat))
    (tStar : Expr O' Γ' .nat) (s : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E))
    (hLeaks : st.leaks.length ≤ L) (hCorrs : st.corrs.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) :
    (cAuthOKE L Δ tLStar tStar s).eval ρ = authLosingConditionsAvoided Δ (tLStar.eval ρ) (tStar.eval ρ) st := by
  unfold cAuthOKE authLosingConditionsAvoided
  rw [letE_eval]
  have h0 : (Expr.pair tLStar (.pair tStar s)).eval ρ =
      (tLStar.eval ρ, tStar.eval ρ, cGsEnc (vpT := vpT) vpEncFn st) := by simp [Expr.eval, hs]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod (.opt .nat) (.prod .nat (cGsTy vpT)) : Ty S))
    (tLStar.eval ρ, tStar.eval ρ, cGsEnc (vpT := vpT) vpEncFn st) ρ
  have hvg : (validGuessE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd .v0))).eval ρ₁ =
      lastLeakGuessAdmissible Δ (tLStar.eval ρ) (tStar.eval ρ) :=
    validGuessE_eval Δ (.fst .v0) (.fst (.snd .v0)) ρ₁
  have hcan : (optNatEqE (cCanonE L (.fst (.snd (Expr.v0 (O := O')))) (.snd (.snd .v0)))
      (.fst .v0)).eval ρ₁ = (canon (tStar.eval ρ) st == tLStar.eval ρ) := by
    rw [optNatEqE_eval, cCanonE_eval vpEncFn L _ _ ρ₁ st hLeaks rfl]
    rfl
  have htL : st.leaks.take L = st.leaks := List.take_of_length_le hLeaks
  have htC : (st.corrs.map (fun pe => (partyEnc pe.1, pe.2))).take L =
      st.corrs.map (fun pe => (partyEnc pe.1, pe.2)) :=
    List.take_of_length_le (by simpa using hCorrs)
  have hL0 : (cGsLeaks (.snd (.snd (Expr.v0 (O := O'))))).eval ρ₁ = st.leaks := rfl
  have hC0 : (cGsCorrs (.snd (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.corrs.map (fun pe => (partyEnc pe.1, pe.2)) := rfl
  have hleaks : (Expr.not (.anyB L (cGsLeaks (.snd (.snd (Expr.v0 (O := O')))))
      (.and (ltOptE (.fst .v1) .v0) (.lt .v0 (.fst (.snd .v1)))))).eval ρ₁ =
      st.leaks.all (fun l => !(ltOpt (tLStar.eval ρ) l && decide (l < tStar.eval ρ))) := by
    rw [not_eval, anyB_eval, hL0, htL]
    refine not_any_eq_all_not st.leaks _ _ (fun l => ?_)
    rw [and_eval, ltOptE_eval]
    rfl
  have hcorrs : (Expr.not (.anyB L (cGsCorrs (.snd (.snd (Expr.v0 (O := O')))))
      (.and (boolEq (.fst .v0) (receiverOfE (.fst (.snd .v1))))
        (ltOptE (.fst .v1) (.snd .v0))))).eval ρ₁ =
      st.corrs.all (fun pc => !(pc.1 == Party.receiverOf (tStar.eval ρ) &&
        ltOpt (tLStar.eval ρ) pc.2)) := by
    rw [not_eval, anyB_eval, hC0, htC]
    refine not_any_map_eq_all_not (fun pe : Party × ℕ => (partyEnc pe.1, pe.2)) st.corrs _ _
      (fun ⟨P, e⟩ => ?_)
    rw [and_eval, boolEq_eval, receiverOfE_eval, ltOptE_eval]
    simp [ρ₁, partyEnc_beq, Expr.eval, Expr.v0, Expr.v1]
  rw [and_eval, and_eval, and_eval, hvg, hcan, hleaks, hcorrs]

theorem leakDoomE_eval {O' : Ops S} {Γ'} (L : ℕ) (π : Policy)
    (g g' : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ')
    (st st' : GameState VPt M (Header T × E))
    (hLeaks : st'.leaks.length ≤ L)
    (hg : g.eval ρ = cGsEnc (vpT := vpT) vpEncFn st)
    (hg' : g'.eval ρ = cGsEnc (vpT := vpT) vpEncFn st') :
    (leakDoomE L π g g').eval ρ = π.leakDoom st st' := by
  have ht : st'.leaks.take L = st'.leaks := List.take_of_length_le hLeaks
  unfold leakDoomE Policy.leakDoom
  rw [letE_eval]
  have h0 : (Expr.pair g g').eval ρ =
      (cGsEnc (vpT := vpT) vpEncFn st, cGsEnc (vpT := vpT) vpEncFn st') := by
    simp [Expr.eval, hg, hg']
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) (cGsTy vpT))
    (cGsEnc (vpT := vpT) vpEncFn st, cGsEnc (vpT := vpT) vpEncFn st') ρ
  rw [orE_eval, and_eval, anyB_eval, anyB_eval]
  have hL1 : (cGsLeaks (.snd (Expr.v0 (O := O')))).eval ρ₁ = st'.leaks := rfl
  rw [hL1, ht]
  congr 1
  · congr 1; funext l
    rw [and_eval, ltOptE_eval, optNatLit_eval]
    rfl
  · congr 1
    · congr 1; funext l
      rw [leN_eval]; rfl
    · cases Party.senderOf π.tStar <;>
        simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]

theorem corrDoomE_eval {O' : Ops S} {Γ'} (π : Policy)
    (g : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) (ρ : Env Γ')
    (st : GameState VPt M (Header T × E)) (P : Party)
    (hg : g.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (corrDoomE π g p).eval ρ = π.corrDoom st P := by
  unfold corrDoomE Policy.corrDoom
  rw [letE_eval]
  have h0 : (Expr.pair g p).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) := by
    simp [Expr.eval, hg, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) .bool) (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) ρ
  rw [and_eval, boolEq_eval]
  have hP : (Expr.snd (Expr.v0 (O := O'))).eval ρ₁ = partyEnc P := rfl
  have hR : (Expr.bool (O := O') (partyEnc (Party.receiverOf π.tStar))).eval ρ₁ =
      partyEnc (Party.receiverOf π.tStar) := rfl
  rw [hP, hR, partyEnc_beq]
  congr 1
  cases hAuth : π.auth
  · simp only [Bool.false_eq_true, ↓reduceIte, and_eval, leN_eval, maxN_eval]
    cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]
  · simp only [↓reduceIte, ltOptE_eval, optNatLit_eval]
    cases P <;> simp [ρ₁, pGet, cGsEpoch, cGsEnc, partyEnc, Expr.eval, Expr.v0]

theorem authOutE_eval {O' : Ops S} {hsT : Ty S} {HS : Type} (hsEncFn : HS → hsT.denote)
    {Γ'} (L Δ : ℕ) (π : Policy) (es : Expr O' Γ' (esTy vpT hsT)) (ρ : Env Γ')
    (es₀ : EState VPt M (Header T × E) HS)
    (hLeaks : es₀.g.leaks.length ≤ L) (hCorrs : es₀.g.corrs.length ≤ L)
    (hes : es.eval ρ = esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀) :
    (authOutE L Δ π es).eval ρ = authOut Δ π es₀ := by
  unfold authOutE authOut
  rw [letE_eval, hes]
  set ρ₁ := Env.cons (t := esTy vpT hsT)
    (esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀) ρ
  rw [and_eval, and_eval]
  have hAuth := cAuthOKE_eval vpEncFn (O' := O') L Δ (optNatLit π.tL) (.nat π.tStar)
    (esG .v0) ρ₁ es₀.g hLeaks hCorrs rfl
  rw [hAuth]
  simp [ρ₁, optNatLit_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0]

theorem privValidE_eval {O' : Ops S} {hsT : Ty S} {HS : Type} (hsEncFn : HS → hsT.denote)
    {Γ'} (L Δ : ℕ) (π : Policy) (es : Expr O' Γ' (esTy vpT hsT)) (ρ : Env Γ')
    (es₀ : EState VPt M (Header T × E) HS)
    (hLeaks : es₀.g.leaks.length ≤ L)
    (hes : es.eval ρ = esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀) :
    (privValidE L Δ π es).eval ρ = privValid Δ π es₀ := by
  unfold privValidE privValid
  rw [letE_eval, hes]
  set ρ₁ := Env.cons (t := esTy vpT hsT)
    (esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀) ρ
  rw [and_eval, and_eval, validGuessE_eval, optNatEqE_eval]
  rw [cCanonE_eval vpEncFn (O' := O') L (.nat π.tStar) (esG .v0) ρ₁ es₀.g hLeaks rfl]
  simp [ρ₁, optNatLit_eval, esAbort, esEnc, Expr.eval, Expr.v0]

end Bookkeeping

/-! ## Costed hooks and engine handlers -/

section Handlers

@[reducible] def vpTblTy {γvT svT ssvT rsvT : Ty S} : Ty S :=
  vpTy γvT svT ssvT (.tbl (.opt rsvT))

def vpTblEnc {γvT svT ssvT rsvT : Ty S}
    (p : VP γvT.denote T svT.denote ssvT.denote rsvT.denote) :
    (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT).denote :=
  vpEnc (vrT := .tbl (.opt rsvT)) id p

def esSetG
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT))
    (g : Expr O' Γ' (cGsTy vpT)) : Expr O' Γ' (esTy vpT hsT) :=
  rdslExpr =>
    letE (raw es, raw g) (fun (es0, g0) => esMk g0 (esH es0) (esAbort es0))

def esSetH
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT))
    (h : Expr O' Γ' hsT) : Expr O' Γ' (esTy vpT hsT) :=
  rdslExpr =>
    letE (raw es, raw h) (fun (es0, h0) => esMk (esG es0) h0 (esAbort es0))

def esSetAbort
    {O' : Ops S} {vpT hsT : Ty S} {Γ'} (es : Expr O' Γ' (esTy vpT hsT))
    (abort : Expr O' Γ' .bool) : Expr O' Γ' (esTy vpT hsT) :=
  rdslExpr =>
    letE (raw es, raw abort) (fun (es0, ab0) => esMk (esG es0) (esH es0) ab0)

def mkPartiesE
    {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (γA γB : Expr O' Γ' γvT) (σ : Expr O' Γ' svT) (ssB : Expr O' Γ' ssvT)
    (rsA : Expr O' Γ' rsvT) :
    Expr O' Γ'
      (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
        (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) :=
  rdslExpr =>
    letE (raw γA, raw γB, raw σ, raw ssB, raw rsA) (fun (γA0, γB0, σ0, ssB0, rsA0) =>
      (vpMk (bool (partyEnc .A)) σ0 none (tset (tconst none) 0 (some rsA0)) γA0 none 0,
       vpMk (bool (partyEnc .B)) σ0 (some ssB0) (tconst none) γB0 none 0))

def realPartyE
    {O' : Ops S} {γvT svT ssvT vrT : Ty S} {Γ'}
    (vp : Expr O' Γ' (vpTy γvT svT ssvT vrT))
    (γ : Expr O' Γ' (.base .γ)) (σ : Expr O' Γ' (.base .sig))
    (vS : Expr O' Γ' (.opt (.base .ss))) (vR : Expr O' Γ' (.tbl (.opt (.base .rs)))) :
    Expr O' Γ' psTy :=
  rdslExpr =>
    letE (raw vp, raw γ, raw σ, raw vS, raw vR) (fun (vp0, γ0, σ0, vS0, vR0) =>
      vpMk (vpId vp0) σ0 vS0 vR0 γ0 (vpTcur vp0) (vpTcurNat vp0))

/-- Costed hooks bundle for `CryptoGames.SM.Engine.Hooks`. -/
structure HooksC (O' : Ops S) {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    (I' : Iface S (unifSpec + TSpec)) (γvT svT ssvT rsvT hsT : Ty S) where
  startSend : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' .nat →
    Expr O' Γ' γvT →
    Expr O' Γ' svT →
    Expr O' Γ' (.opt (.base .ccoins)) →
    Comp O' I' Γ' (.prod (.opt (.prod γvT (.prod (.base .t) (.prod svT ssvT)))) hsT)
  startRecv : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' .nat →
    Expr O' Γ' γvT →
    Expr O' Γ' svT →
    Expr O' Γ' (.base .t) →
    Comp O' I' Γ' (.prod (.opt (.opt (.prod γvT (.prod svT rsvT)))) hsT)
  fsSend : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' .nat →
    Expr O' Γ' ssvT →
    Expr O' Γ' hdrTy →
    Expr O' Γ' (.base .msg) →
    Expr O' Γ' (.opt (.prod (.base .msg) (.base .msg))) →
    Comp O' I' Γ' (.prod (.opt (.prod ssvT (.base .ct))) hsT)
  fsRecv : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' .nat →
    Expr O' Γ' rsvT →
    Expr O' Γ' hdrTy →
    Expr O' Γ' (.base .ct) →
    Expr O' Γ' (.opt cRecTy) →
    Comp O' I' Γ' (.prod (.opt (.opt (.prod rsvT (.prod .nat (.base .msg))))) hsT)
  commit : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) →
    Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) →
    Comp O' I' Γ'
      (.prod (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) hsT)
  reveal : ∀ {Γ'},
    Expr O' Γ' hsT →
    Expr O' Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) →
    Expr O' Γ' .bool →
    Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) →
    Comp O' I' Γ' (.prod (.opt psTy) hsT)

/-- Expression bundle for `SM.Config M` in the costed SM engine. -/
structure ConfigEC (O' : Ops S) where
  deliverWin : Bool
  injectFullE : ∀ {Γ'}, Expr O' Γ' .nat → Expr O' Γ' .bool
  challOKE : ∀ {Γ'}, Expr O' Γ' .nat → Expr O' Γ' .bool
  challMsgE : ∀ {Γ'}, Expr O' Γ' .nat → Expr O' Γ' .bool →
    Expr O' Γ' (.base .msg) → Expr O' Γ' (.base .msg) → Expr O' Γ' (.base .msg)

def modeCfgEC
    (O' : Ops S) (mo : Mode) : ConfigEC O' where
  deliverWin := false
  injectFullE e := if mo.auth then .eqN e (.nat mo.tStar) else .bool false
  challOKE e := if mo.auth then .bool false else .eqN e (.nat mo.tStar)
  challMsgE _ b m₀ m₁ := .ite b m₁ m₀

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

def vSendStep1C
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    {Γ'} (h : Expr OO Γ' hsT)
    (ctx : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (r : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO I' Γ'
      (.prod (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) hsT) :=
  rdsl do
    (h0, ctx0, p0, s0, r0) ← return (raw h, raw ctx, raw p, raw s, raw r)
    if sendsInE (vpId s0) (vpTcurNat s0 + 1) then
      (res, h1) ← hk.startSend h0 ctx0 p0 (vpTcurNat s0 + 1) (vpΓ s0) (vpRoot s0) r0
      match res with
      | none => return (none, h1)
      | some (γ', T', σ', ss) =>
        let s1 := vpMk (vpId s0) σ' (some ss) (vpVR s0) γ' (some T') (vpTcurNat s0 + 1)
        return (some s1, h1)
    else
      return (some s0, h0)

def vSendC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    {Γ'} (h : Expr OO Γ' hsT)
    (ctx : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO Γ' (.base .msg))
    (pair : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO I' Γ'
      (.prod
        (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hdrCtTy))
        hsT) :=
  rdsl do
    (h0, ctx0, p0, s0, m0, pair0, r0) ←
      return (raw h, raw ctx, raw p, raw s, raw m, raw pair, raw r)
    (step1, h1) ← vSendStep1C hk h0 ctx0 p0 s0 r0
    match step1 with
    | none => return (none, h1)
    | some s1 =>
      let hdr := (vpTcurNat s1, vpTcur s1)
      match vpVS s1 with
      | none =>
        return (some (s1, hdr, Expr.op (O := OO) CKAOp.defaultE ()), h1)
      | some v =>
        (res, h2) ← hk.fsSend h1 ctx0 p0 (vpTcurNat s1) v hdr m0 pair0
        match res with
        | none => return (none, h2)
        | some (v', ct) =>
          return (some (vpSetVS s1 (some v'), hdr, ct), h2)

def vRecvStep1C
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    {Γ'} (h : Expr OO Γ' hsT)
    (ctx : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : Expr OO Γ' hdrCtTy) :
    Comp OO I' Γ'
      (.prod
        (.opt (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
        hsT) :=
  rdsl do
    (h0, ctx0, p0, s0, c0) ← return (raw h, raw ctx, raw p, raw s, raw c)
    let t0 := c0.1.1
    if t0 == vpTcurNat s0 + 1 then
      match c0.1.2 with
      | none => return (some none, h0)
      | some Tn =>
        (res, h1) ← hk.startRecv h0 ctx0 p0 t0 (vpΓ s0) (vpRoot s0) Tn
        match res with
        | none => return (none, h1)
        | some inner =>
          match inner with
          | none => return (some none, h1)
          | some (γ', σ', rs) =>
            let s1 := vpMk (vpId s0) σ' (vpVS s0) (tset (vpVR s0) t0 (some rs)) γ' (vpTcur s0) t0
            return (some (some s1), h1)
    else
      return (some (some s0), h0)

def vRecvC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    {Γ'} (h : Expr OO Γ' hsT)
    (ctx : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : Expr OO Γ' hdrCtTy)
    (rec_ : Expr OO Γ' (.opt cRecTy)) :
    Comp OO I' Γ'
      (.prod
        (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          (.prod .nat (.prod .nat (.base .msg))))))
        hsT) :=
  rdsl do
    (h0, ctx0, p0, s0, c0, rec0) ← return (raw h, raw ctx, raw p, raw s, raw c, raw rec_)
    let t0 := c0.1.1
    if orE (sendsInE (vpId s0) t0) (vpTcurNat s0 + 1 < t0) then
      return (some none, h0)
    else
      (step1, h1) ← vRecvStep1C hk h0 ctx0 p0 s0 c0
      match step1 with
      | none => return (none, h1)
      | some step1Inner =>
        match step1Inner with
        | none => return (some none, h1)
        | some s1 =>
          match tget (vpVR s1) t0 with
          | none => return (some none, h1)
          | some v =>
            (res, h2) ← hk.fsRecv h1 ctx0 p0 t0 v c0.1 c0.2 rec0
            match res with
            | none => return (none, h2)
            | some resInner =>
              match resInner with
              | none => return (some none, h2)
              | some (v', idx, mOut) =>
                let s2 := vpSetVR s1 (tset (vpVR s1) t0 (some v'))
                return (some (some (s2, t0, idx, mOut)), h2)

def commitEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L : ℕ)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (s : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO Γ' .bool)
    (old new : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (pos : Expr OO Γ' posTy) :
    Comp OO I' Γ'
      (.prod (.opt (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, s1, p0, old0, new0) ←
      return (raw es, cAcceptE (raw L) (raw s) (raw p) (raw new) (raw pos), raw p, raw old, raw new)
    (res, h') ← hk.commit (esH es0) s1 p0 old0 new0
    match res with
    | none => return (none, esMk (esG es0) h' true)
    | some new' =>
      return (some (cGsSetStP s1 p0 new'), esMk (esG es0) h' (esAbort es0))

def transmitEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep : ℕ) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    Comp OO I' Γ'
      (.prod (.opt hdrCtTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, (p0, m0, r0)) ← return (raw es, raw arg)
    if orE (esAbort es0) (cGsWin (esG es0)) then
      return (none, es0)
    else
      match cEpMgmtE (raw Δ) (raw qep) (esG es0) p0 (isSomeE r0) with
      | none => return (none, es0)
      | some s1 =>
        if leakDoomE (raw L) (raw π) (esG es0) s1 then
          return (none, esSetAbort es0 true)
        else
          (res, h') ← vSendC hk (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
          match res with
          | none => return (none, esMk (esG es0) h' true)
          | some (st', ct) =>
            let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
            let g' := cRecordE (raw L) (raw Δ) s1 p0 st' recE false
            return (some ct, esMk g' h' (esAbort es0))

def challEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    Comp OO I' Γ'
      (.prod (.opt hdrCtTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, (p0, m0_0, m1_0, r0)) ← return (raw es, raw arg)
    if orE (esAbort es0) (cGsWin (esG es0)) then
      return (none, es0)
    else
      match cEpMgmtE (raw Δ) (raw qep) (esG es0) p0 (isSomeE r0) with
      | none => return (none, es0)
      | some s1 =>
        if orE (!(cSafeChE (raw Δ) s1 p0)) (!(cfg.challOKE (pGet (cGsEpoch s1) p0))) then
          return (none, es0)
        else if leakDoomE (raw L) (raw π) (esG es0) s1 then
          return (none, esSetAbort es0 true)
        else
          let mChall := cfg.challMsgE (pGet (cGsEpoch s1) p0) (cGsB (esG es0)) m0_0 m1_0
          (res, h') ← vSendC hk (esH es0) s1 p0 (pGet (cGsSt s1) p0) mChall (some (m0_0, m1_0)) r0
          match res with
          | none => return (none, esMk (esG es0) h' true)
          | some (st', ct) =>
            let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), mChall, ct)
            let g' := cRecordE (raw L) (raw Δ) s1 p0 st' recE true
            return (some ct, esMk g' h' (esAbort es0))

def deliverEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L maxSkip : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool hdrCtTy)) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, (p0, c0)) ← return (raw es, raw arg)
    let s0 := esG es0
    if orE (esAbort es0) (cGsWin s0) then
      return (none, es0)
    else
      match cInTransitE (raw L) s0 (otherE p0) c0 with
      | none => return (none, es0)
      | some r1 =>
        (res, h') ← vRecvC hk (esH es0) s0 p0 (pGet (cGsSt s0) p0) c0 (some r1)
        match res with
        | none => return (none, esMk s0 h' true)
        | some resInner =>
          match resInner with
          | none =>
            let must := bool cfg.deliverWin && cMustBeCorrectE (raw L) (raw maxSkip) s0 p0 r1
            let g' := if must then cGsSetWin s0 true else s0
            return (some (inl ()), esMk g' h' (esAbort es0))
          | some (st', t', i', m') =>
            let es' := esSetH es0 h'
            (accRes, es_acc) ← commitEC hk (raw L) es' s0 p0 (pGet (cGsSt s0) p0) st' (cRecPos r1)
            match accRes with
            | none => return (none, es_acc)
            | some s_acc =>
              let rPos := cRecPos r1
              let must := bool cfg.deliverWin && cMustBeCorrectE (raw L) (raw maxSkip) s0 p0 r1
              let eqOut :=
                (t' == posEpoch rPos) &&
                  ((i' == posIdx rPos) && Expr.op (O := OO) CKAOp.eqM (m', cRecMsg r1))
              let bad := must && !eqOut
              let gFinal := if bad then cGsSetWin s_acc true else s_acc
              let mOut := if cChallContainsE (raw L) s0 rPos then none else some m'
              return (some (inr (t', i', mOut)), esSetG es_acc gFinal)

def injectEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool hdrCtTy)) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, (p0, c0)) ← return (raw es, raw arg)
    let s0 := esG es0
    let refuse :=
      orE (esAbort es0)
        (orE (cGsWin s0)
          (orE (isSomeE (cInTransitE (raw L) s0 (otherE p0) c0))
            (!(cSafeInjE (raw Δ) s0))))
    if refuse then
      return (none, es0)
    else
      (res, h') ← vRecvC hk (esH es0) s0 p0 (pGet (cGsSt s0) p0) c0 none
      match res with
      | none => return (none, esMk s0 h' true)
      | some resInner =>
        match resInner with
        | none => return (some (inl ()), esSetH es0 h')
        | some (st', t', i', m') =>
          let es' := esSetH es0 h'
          if nat (qep + 1) < t' then
            return (some (inl ()), es')
          else
            let pos := (otherE p0, t', i')
            if cTrivialE (raw L) (raw Δ) s0 pos then
              (accRes, es_acc) ← commitEC hk (raw L) es' s0 p0 (pGet (cGsSt s0) p0) st' pos
              match accRes with
              | none => return (none, es_acc)
              | some s_acc =>
                return (some (inr (t', i', some m')), esSetG es_acc s_acc)
            else
              let g' := if cfg.injectFullE t' then cGsSetWin s0 true else s0
              return (some (inl ()), esSetG es' g')

def corrEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L : ℕ) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    Comp OO I' Γ'
      (.prod (.opt psTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0) ← return (raw es, raw p)
    let s0 := esG es0
    let refuse := orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0)))
    if refuse then
      return (none, es0)
    else
      let s1 := cAfterCorrE (raw L) s0 p0
      if orE (leakDoomE (raw L) (raw π) s0 s1) (corrDoomE (raw π) s0 p0) then
        return (none, esSetAbort es0 true)
      else
        (res, h') ← hk.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match res with
        | none => return (none, esMk s0 h' true)
        | some st =>
          return (some st, esMk s1 h' (esAbort es0))

local macro_rules
  | `(rdsl_pat| .transmit $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term) => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term) => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term) => `(rdsl_pat| .inr $p)

/-- Combined five-oracle costed dispatcher for `Engine.implE`. -/
def implEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (raw es, raw q)
    match q0 with
    | .transmit x =>
      (out, es') ← transmitEC hk (raw L) (raw Δ) (raw qep) (raw π) es0 x
      return (inl (inl (inl (inl out))), es')
    | .challenge x =>
      (out, es') ← challEC hk (raw L) (raw Δ) (raw qep) cfg (raw π) es0 x
      return (inl (inl (inl (inr out))), es')
    | .deliver x =>
      (out, es') ← deliverEC hk (raw L) (raw maxSkip) cfg es0 x
      return (inl (inl (inr out)), es')
    | .inject x =>
      (out, es') ← injectEC hk (raw L) (raw Δ) (raw qep) cfg es0 x
      return (inl (inr out), es')
    | .corrupt x =>
      (out, es') ← corrEC hk (raw L) (raw π) es0 x
      return (inr out, es')

end Handlers

/-! ## Engine evaluation agreement and invariants -/

section HandlerEval

@[simp] theorem eval_bind {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b : Ty S'}
    (c₁ : Comp O' I' Γ' a) (c₂ : Comp O' I' (a :: Γ') b) (ρ : Env Γ') :
    (Comp.bind c₁ c₂).eval ρ = (c₁.eval ρ >>= fun v => c₂.eval (.cons v ρ)) := rfl

@[simp] theorem eval_ret {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a : Ty S'}
    (e : Expr O' Γ' a) (ρ : Env Γ') :
    (Comp.ret (I := I') e).eval ρ = pure (e.eval ρ) := rfl

@[simp] theorem eval_ite {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a : Ty S'}
    (c : Expr O' Γ' .bool) (t e : Comp O' I' Γ' a) (ρ : Env Γ') :
    (Comp.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl

@[simp] theorem eval_caseOpt {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (noneBranch : Comp O' I' Γ' b)
    (someBranch : Comp O' I' (a :: Γ') b) (ρ : Env Γ') :
    (Comp.caseOpt e noneBranch someBranch).eval ρ =
      match e.eval ρ with
      | none => noneBranch.eval ρ
      | some v => someBranch.eval (.cons v ρ) := rfl

@[simp] theorem eval_bind_ret {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' a) (c : Comp O' I' (a :: Γ') b) (ρ : Env Γ') :
    (Comp.bind (.ret e) c).eval ρ = c.eval (.cons (e.eval ρ) ρ) := by
  simp [Comp.eval]

theorem inl_eval {S' : Sig} {O' : Ops S'} {Γ'} {t u : Ty S'}
    (e : Expr O' Γ' t) (ρ : Env Γ') :
    (Expr.inl (u := u) e).eval ρ = Sum.inl (e.eval ρ) := rfl

theorem tset_eval_eq_update {S' : Sig} {O' : Ops S'} {a : Ty S'} {Γ'}
    (t : Expr O' Γ' (.tbl a)) (i : Expr O' Γ' .nat) (v : Expr O' Γ' a) (ρ : Env Γ') :
    (Expr.tset t i v).eval ρ = Function.update (t.eval ρ) (i.eval ρ) (v.eval ρ) := by
  funext j
  by_cases hj : j = i.eval ρ <;> simp [Expr.eval, Function.update, hj]

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

theorem vpSetVS_eval {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (s : Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (vS : Expr O' Γ' (.opt ssvT)) (ρ : Env Γ')
    (p : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (hs : s.eval ρ = vpTblEnc p) :
    (vpSetVS s vS).eval ρ = vpTblEnc { p with vS := vS.eval ρ } := by
  simp [vpSetVS, vpMk, vpId, vpRoot, vpVR, vpΓ, vpTcur, vpTcurNat,
    hs, vpTblEnc, vpEnc, Expr.eval, Expr.v0]

theorem vpSetVR_eval {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (s : Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (vR : Expr O' Γ' (.tbl (.opt rsvT))) (ρ : Env Γ')
    (p : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (hs : s.eval ρ = vpTblEnc p) :
    (vpSetVR s vR).eval ρ = vpTblEnc { p with vR := vR.eval ρ } := by
  simp [vpSetVR, vpMk, vpId, vpRoot, vpVS, vpΓ, vpTcur, vpTcurNat,
    hs, vpTblEnc, vpEnc, Expr.eval, Expr.v0]

theorem vpSetΓ_eval {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (s : Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (γ : Expr O' Γ' γvT) (ρ : Env Γ')
    (p : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (hs : s.eval ρ = vpTblEnc p) :
    (vpSetΓ s γ).eval ρ = vpTblEnc { p with γ := γ.eval ρ } := by
  simp [vpSetΓ, vpMk, vpId, vpRoot, vpVS, vpVR, vpTcur, vpTcurNat,
    hs, vpTblEnc, vpEnc, Expr.eval, Expr.v0]

theorem esSetG_eval {O' : Ops S} {vpT hsT : Ty S} {VPt HS : Type}
    (vpEncFn : VPt → vpT.denote) (hsEncFn : HS → hsT.denote)
    {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) (g : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ')
    (es₀ : EState VPt M (Header T × E) HS) (g₀ : GameState VPt M (Header T × E))
    (hes : es.eval ρ = esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀)
    (hg : g.eval ρ = cGsEnc (vpT := vpT) vpEncFn g₀) :
    (esSetG es g).eval ρ =
      esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn { es₀ with g := g₀ } := by
  simp [esSetG, esMk, esH, esAbort, hes, hg, esEnc, Expr.eval, Expr.v0]

theorem esSetH_eval {O' : Ops S} {vpT hsT : Ty S} {VPt HS : Type}
    (vpEncFn : VPt → vpT.denote) (hsEncFn : HS → hsT.denote)
    {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) (h : Expr O' Γ' hsT) (ρ : Env Γ')
    (es₀ : EState VPt M (Header T × E) HS) (h₀ : HS)
    (hes : es.eval ρ = esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀)
    (hh : h.eval ρ = hsEncFn h₀) :
    (esSetH es h).eval ρ =
      esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn { es₀ with h := h₀ } := by
  simp [esSetH, esMk, esG, esAbort, hes, hh, esEnc, Expr.eval, Expr.v0]

theorem esSetAbort_eval {O' : Ops S} {vpT hsT : Ty S} {VPt HS : Type}
    (vpEncFn : VPt → vpT.denote) (hsEncFn : HS → hsT.denote)
    {Γ'} (es : Expr O' Γ' (esTy vpT hsT)) (a : Expr O' Γ' .bool) (ρ : Env Γ')
    (es₀ : EState VPt M (Header T × E) HS)
    (hes : es.eval ρ = esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn es₀) :
    (esSetAbort es a).eval ρ =
      esEnc (vpT := vpT) (hsT := hsT) vpEncFn hsEncFn { es₀ with abort := a.eval ρ } := by
  simp [esSetAbort, esMk, esG, esH, hes, esEnc, Expr.eval, Expr.v0]

theorem cGsInitE_eval {O' : Ops S} {vpT : Ty S} {VPt : Type}
    (vpEncFn : VPt → vpT.denote)
    {Γ'} (vA vB : Expr O' Γ' vpT) (b : Expr O' Γ' .bool) (ρ : Env Γ')
    (vA₀ vB₀ : VPt) (hvA : vA.eval ρ = vpEncFn vA₀) (hvB : vB.eval ρ = vpEncFn vB₀) :
    (cGsInitE vA vB b).eval ρ =
      cGsEnc (vpT := vpT) vpEncFn
        { st := fun | .A => vA₀ | .B => vB₀
          b := b.eval ρ } := by
  simp [cGsInitE, cGsMk, hvA, hvB, cGsEnc, Expr.eval]

theorem mkPartiesE_eval {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (γA γB : Expr O' Γ' γvT) (σ : Expr O' Γ' svT) (ssB : Expr O' Γ' ssvT)
    (rsA : Expr O' Γ' rsvT) (ρ : Env Γ') :
    (mkPartiesE (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR)
      (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) γA γB σ ssB rsA).eval ρ =
      Prod.map vpTblEnc vpTblEnc
        (mkParties (T := T) (γA.eval ρ) (γB.eval ρ) (σ.eval ρ) (ssB.eval ρ) (rsA.eval ρ)) := by
  simp [mkPartiesE, mkParties, vpMk, vpTblEnc, vpEnc, partyEnc, Prod.map, Expr.eval, Expr.v0]
  funext j
  by_cases h : j = 0 <;> simp [h]

theorem realPartyE_eval {O' : Ops S} {γvT svT ssvT rsvT : Ty S} {Γ'}
    (vp : Expr O' Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (γ : Expr O' Γ' (.base .γ)) (σ : Expr O' Γ' (.base .sig))
    (vS : Expr O' Γ' (.opt (.base .ss))) (vR : Expr O' Γ' (.tbl (.opt (.base .rs))))
    (ρ : Env Γ') (vp₀ : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (hvp : vp.eval ρ = vpTblEnc vp₀) :
    (realPartyE vp γ σ vS vR).eval ρ =
      ckaPsEnc (realParty vp₀ (γ.eval ρ) (σ.eval ρ) (vS.eval ρ) (vR.eval ρ)) := by
  simp [realPartyE, realParty, vpMk, vpId, vpTcur, vpTcurNat, hvp,
    vpTblEnc, vpEnc, ckaPsEnc, Expr.eval, Expr.v0]

/-- Agreement predicate linking a `ConfigEC` expression bundle to a shallow `SM.Config M`. -/
structure ConfigECAgrees (cfgC : ConfigEC OO) (cfg : Config M) : Prop where
  deliverWin_eq : cfgC.deliverWin = cfg.deliverWin
  injectFull_eq : ∀ {Γ'} (e : Expr OO Γ' .nat) (ρ : Env Γ'),
    (cfgC.injectFullE e).eval ρ = cfg.injectFull (e.eval ρ)
  challOK_eq : ∀ {Γ'} (e : Expr OO Γ' .nat) (ρ : Env Γ'),
    (cfgC.challOKE e).eval ρ = cfg.challAllowedIn (e.eval ρ)
  challMsg_eq : ∀ {Γ'} (ep : Expr OO Γ' .nat) (b : Expr OO Γ' .bool)
    (m₀ m₁ : Expr OO Γ' (.base .msg)) (ρ : Env Γ'),
    (cfgC.challMsgE ep b m₀ m₁).eval ρ =
      (cfg.challMsg (ep.eval ρ)).getD (if b.eval ρ then m₁.eval ρ else m₀.eval ρ)

theorem modeCfgEC_agrees (mo : Mode) :
    ConfigECAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (modeCfgEC OO mo) mo.cfg where
  deliverWin_eq := by cases h : mo.auth <;> simp [modeCfgEC, Mode.cfg, Config.auth, Config.priv, h]
  injectFull_eq e ρ := by
    cases h : mo.auth <;> simp only [modeCfgEC, Mode.cfg, Config.auth, Config.priv, h,
      ↓reduceIte, Bool.false_eq_true, Expr.eval]
    by_cases h2 : e.eval ρ = mo.tStar <;> simp [h2]
  challOK_eq e ρ := by
    cases h : mo.auth <;> simp only [modeCfgEC, Mode.cfg, Config.auth, Config.priv, h,
      ↓reduceIte, Bool.false_eq_true, Expr.eval]
    by_cases h2 : e.eval ρ = mo.tStar <;> simp [h2]
  challMsg_eq ep b m₀ m₁ ρ := by
    cases h : mo.auth <;>
      simp [modeCfgEC, Mode.cfg, Config.auth, Config.priv, h, Expr.eval]

/-- Single-step list-length invariant on `SM.GameState` with scan bound `L` and one-leak headroom. -/
structure SMStateBoundedEngine {St Msg C : Type} (L : ℕ) (s : GameState St Msg C) : Prop where
  trans_le : s.trans.length ≤ L
  chall_le : s.chall.length ≤ L
  comp_u : ∃ U : List Pos, U.length ≤ L ∧ (∀ r ∈ s.trans, r.pos ∈ U) ∧ (∀ p ∈ s.comp, p ∈ U)
  leaks_succ_le : s.leaks.length + 1 ≤ L
  corrs_le : s.corrs.length ≤ L

theorem SMStateBoundedEngine.comp_le {St Msg C : Type} {L : ℕ} {s : GameState St Msg C}
    (h : SMStateBoundedEngine L s) : s.comp.dedup.length ≤ L := by
  obtain ⟨U, hU, _, hSub⟩ := h.comp_u
  exact (length_dedup_le_of_subset hSub).trans hU

theorem SMStateBoundedEngine.leaks_le {St Msg C : Type} {L : ℕ} {s : GameState St Msg C}
    (h : SMStateBoundedEngine L s) : s.leaks.length ≤ L := by
  have := h.leaks_succ_le; omega

theorem epMgmt_lists_eq {St Msg C : Type} {Δ qep : ℕ} {s s₁ : GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.trans = s.trans ∧ s₁.chall = s.chall ∧ s₁.comp = s.comp ∧ s₁.corrs = s.corrs := by
  unfold GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at h
    · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at h
      subst h; simp

theorem epMgmt_leaks_le_succ {St Msg C : Type} {Δ qep : ℕ} {s s₁ : GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.leaks.length ≤ s.leaks.length + 1 := by
  unfold GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at h
    · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at h
      subst h; omega

theorem epMgmt_leaks_le {St Msg C : Type} {L Δ qep : ℕ} {s s₁ : GameState St Msg C}
    {P : Party} {bad : Bool} (hBound : SMStateBoundedEngine L s)
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.leaks.length ≤ L :=
  (epMgmt_leaks_le_succ h).trans hBound.leaks_succ_le

theorem afterCorr_leaks_eq {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    (s.afterCorr P).leaks.length = s.leaks.length + 1 := by
  simp [GameState.afterCorr, GameState.leak]

theorem afterCorr_leaks_le {St Msg C : Type} {L : ℕ} {s : GameState St Msg C}
    (hBound : SMStateBoundedEngine L s) (P : Party) :
    (s.afterCorr P).leaks.length ≤ L := by
  rw [afterCorr_leaks_eq]
  exact hBound.leaks_succ_le

/-- Step-indexed list-length invariant on `SM.GameState` across `q` remaining queries out of `B`. -/
structure SMEngineInv {St Msg C : Type} (L B q : ℕ) (s : GameState St Msg C) : Prop where
  trans_le : s.trans.length + q ≤ B
  chall_le : s.chall.length + q ≤ B
  leaks_le : s.leaks.length + q ≤ B
  corrs_le : s.corrs.length + q ≤ B
  comp_u : ∃ U : List Pos, U.length + q ≤ B ∧ (∀ r ∈ s.trans, r.pos ∈ U) ∧ (∀ p ∈ s.comp, p ∈ U)
  b_succ_le : B + 1 ≤ L
  bb_le : B * B ≤ L * L

theorem SMEngineInv.toBoundedEngine {St Msg C : Type} {L B q : ℕ} {s : GameState St Msg C}
    (h : SMEngineInv L B q s) : SMStateBoundedEngine L s where
  trans_le := by have := h.trans_le; have := h.b_succ_le; omega
  chall_le := by have := h.chall_le; have := h.b_succ_le; omega
  comp_u := by
    obtain ⟨U, hU, hTr, hCp⟩ := h.comp_u
    exact ⟨U, by have := h.b_succ_le; omega, hTr, hCp⟩
  leaks_succ_le := by have := h.leaks_le; have := h.b_succ_le; omega
  corrs_le := by have := h.corrs_le; have := h.b_succ_le; omega

theorem SMEngineInv.mono {St Msg C : Type} {L B m n : ℕ} {s : GameState St Msg C}
    (hmn : m ≤ n) (h : SMEngineInv L B n s) : SMEngineInv L B m s where
  trans_le := by have := h.trans_le; omega
  chall_le := by have := h.chall_le; omega
  leaks_le := by have := h.leaks_le; omega
  corrs_le := by have := h.corrs_le; omega
  comp_u := by
    obtain ⟨U, hU, hTr, hCp⟩ := h.comp_u
    exact ⟨U, by omega, hTr, hCp⟩
  b_succ_le := h.b_succ_le
  bb_le := h.bb_le

theorem SMEngineInv.init {St Msg C : Type} {L B : ℕ} (st : Party → St) (b : Bool)
    (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    SMEngineInv L B B ({ st := st, b := b } : GameState St Msg C) where
  trans_le := by simp
  chall_le := by simp
  leaks_le := by simp
  corrs_le := by simp
  comp_u := ⟨[], by simp, by simp, by simp⟩
  b_succ_le := hB1
  bb_le := hBB

/-- Agreement predicate linking `HooksC` to `Engine.Hooks` under hook-state invariants. -/
structure HooksCAgrees {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote) : Prop where
  hBounded_post : ∀ h, HBounded h → HBoundedPost h
  startSend_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' γvT) (σE : Expr OO Γ' svT)
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party),
    HBounded h →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    (hkC.startSend hE ctxE pE tE γE σE rE).eval ρ =
      Prod.map id hsEncFn <$>
        (hk.startSend ctx P (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h
  startSend_bounded : ∀ ctx P t γ σ r h, HBounded h →
    ∀ res ∈ support ((hk.startSend ctx P t γ σ r).run h), HBoundedPost res.2
  startRecv_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' γvT) (σE : Expr OO Γ' svT)
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party),
    HBounded h →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    (hkC.startRecv hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsEncFn <$>
        (hk.startRecv ctx P (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h
  startRecv_bounded : ∀ ctx P t γ σ Tn h, HBounded h →
    ∀ res ∈ support ((hk.startRecv ctx P t γ σ Tn).run h), HBoundedPost res.2
  startRecv_vrOk : ∀ ctx P t γ σ Tn h, HBounded h →
    ∀ res ∈ support ((hk.startRecv ctx P t γ σ Tn).run h),
    ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs
  fsSend_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' ssvT) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party),
    HBoundedPost h →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    (hkC.fsSend hE ctxE pE tE ssE hdrE mE pairE).eval ρ =
      Prod.map id hsEncFn <$>
        (hk.fsSend ctx P (tE.eval ρ) (ssE.eval ρ) (hdrE.eval ρ) (mE.eval ρ) (pairE.eval ρ)).run h
  fsRecv_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' rsvT) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party)
    (rec_ : Option (Record M (Header T × E))),
    HBoundedPost h → VROk (rsE.eval ρ) →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    recE.eval ρ = rec_.map cRecEnc →
    (hkC.fsRecv hE ctxE pE tE rsE hdrE eE recE).eval ρ =
      Prod.map id hsEncFn <$>
        (hk.fsRecv ctx P (tE.eval ρ) (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h
  fsRecv_bounded : ∀ ctx P t rs hdr e rec_ h, HBoundedPost h →
    ∀ res ∈ support ((hk.fsRecv ctx P t rs hdr e rec_).run h), HBoundedPost res.2
  commit_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party)
    (old new : VP γvT.denote T svT.denote ssvT.denote rsvT.denote),
    HBoundedPost h →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    oldE.eval ρ = vpTblEnc old → newE.eval ρ = vpTblEnc new →
    (hkC.commit hE ctxE pE oldE newE).eval ρ =
      Prod.map (Option.map vpTblEnc) hsEncFn <$> (hk.commit ctx P old new).run h
  reveal_eval : ∀ {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E) (P : Party)
    (vp : VP γvT.denote T svT.denote ssvT.denote rsvT.denote),
    HBounded h →
    hE.eval ρ = hsEncFn h → ctxE.eval ρ = cGsEnc vpTblEnc ctx → pE.eval ρ = partyEnc P →
    vpE.eval ρ = vpTblEnc vp →
    (hkC.reveal hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsEncFn <$> (hk.reveal ctx P vp).run h

def vSendStep1 {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (r : Option CCoins) :
    HM TSpec HS (Option (VP γV T σV ssV rsV)) :=
  if s.id.sendsIn (s.tcur + 1) then do
    match ← hk.startSend ctx P (s.tcur + 1) s.γ s.root r with
    | none => pure none
    | some (γ', T', σ', ss) =>
      pure (some { s with tcur := s.tcur + 1, γ := γ', curCkaMsg := some T', root := σ',
                          vS := some ss })
  else pure (some s)

def vRecvStep1 {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E) :
    HM TSpec HS (Option (Option (VP γV T σV ssV rsV))) :=
  if c.1.1 = s.tcur + 1 then
    match c.1.2 with
    | none => pure (some none)
    | some Tn => do
      match ← hk.startRecv ctx P c.1.1 s.γ s.root Tn with
      | none => pure none
      | some none => pure (some none)
      | some (some (γ', σ', rs)) =>
        pure (some (some { s with tcur := c.1.1, γ := γ', root := σ',
                                  vR := Function.update s.vR c.1.1 (some rs) }))
  else pure (some (some s))

theorem run_liftH_bind {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS α β : Type}
    (mx : HM TSpec HS α)
    (k : α → EM TSpec γV T σV ssV rsV M E HS β)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS) :
    (liftH mx >>= k).run es =
      (mx.run es.h >>= fun p => (k p.1).run { es with h := p.2 }) := by
  change (mx.run es.h >>= fun x => pure (x.1, { es with h := x.2 })) >>=
    (fun p => (k p.1).run p.2) = _
  simp only [bind_assoc, pure_bind]

theorem vSendStep1C_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (r : Option CCoins) (hHB : HBounded h)
    (hh : hE.eval ρ = hsEncFn h) (hctx : ctxE.eval ρ = cGsEnc vpTblEnc ctx)
    (hp : pE.eval ρ = partyEnc P) (hs : sE.eval ρ = vpTblEnc s) (hr : rE.eval ρ = r) :
    (vSendStep1C hkC hE ctxE pE sE rE).eval ρ =
      Prod.map (Option.map vpTblEnc) hsEncFn <$> (vSendStep1 hk ctx P s r).run h := by
  unfold vSendStep1C vSendStep1
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair sE rE)))).eval ρ =
      (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, r) := by
    simp [Expr.eval, hh, hctx, hp, hs, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsT (.prod (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (.prod .bool (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
        (.opt (.base .ccoins))))))
    (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, r) ρ
  rw [eval_ite]
  have hSends : (sendsInE (vpId (.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))))
      (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))).eval ρ₁ =
      s.id.sendsIn (s.tcur + 1) := by
    rw [sendsInE_eval _ _ ρ₁ s.id rfl]
    rfl
  rw [hSends]
  by_cases hsends : s.id.sendsIn (s.tcur + 1)
  · simp only [hsends, ↓reduceIte, eval_bind, StateT.run_bind, map_bind]
    have hStart := hHk.startSend_eval (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
      (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
      (vpΓ (.fst (.snd (.snd (.snd .v0)))))
      (vpRoot (.fst (.snd (.snd (.snd .v0)))))
      (.snd (.snd (.snd (.snd .v0)))) ρ₁ h ctx P hHB rfl rfl rfl
    change (hkC.startSend _ _ _ _ _ _ _).eval ρ₁ =
      Prod.map id hsEncFn <$> (hk.startSend ctx P (s.tcur + 1) s.γ s.root r).run h at hStart
    rw [hStart, bind_map_left]
    refine bind_congr fun ⟨res, h₁⟩ => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, vpMk, vpId, vpVR, vpTcurNat,
        vpTblEnc, vpEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
  · simp [ρ₁, hsends, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]

theorem vSendStep1_bounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (r : Option CCoins) (h : HS) (hHB : HBounded h) :
    ∀ res ∈ support ((vSendStep1 hk ctx P s r).run h), HBoundedPost res.2 := by
  intro ⟨s₁?, h₁⟩ hmem
  unfold vSendStep1 at hmem
  by_cases hsends : s.id.sendsIn (s.tcur + 1)
  · simp only [hsends, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, h'⟩, hans, hmem⟩ := hmem
    have hHB' := hHk.startSend_bounded ctx P (s.tcur + 1) s.γ s.root r h hHB (ans, h') hans
    rcases ans with _ | ⟨γ', T', σ', ss⟩ <;>
      (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
       rcases hmem with ⟨_, rfl⟩; exact hHB')
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hHk.hBounded_post _ hHB

theorem vSend_eq_bind [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (pair : Option (M × M)) (r : Option CCoins) :
    vSend hk ctx P s m pair r =
      (vSendStep1 hk ctx P s r >>= fun s₁? =>
        match s₁? with
        | none => pure none
        | some s₁ =>
          match s₁.vS with
          | none => pure (some (s₁, ((s₁.tcur, s₁.curCkaMsg), default)))
          | some v => do
            match ← hk.fsSend ctx P s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair with
            | none => pure none
            | some (v', e) =>
              pure (some ({ s₁ with vS := some v' }, ((s₁.tcur, s₁.curCkaMsg), e)))) := by
  unfold vSend vSendStep1
  by_cases hs : s.id.sendsIn (s.tcur + 1)
  · simp only [hs, ↓reduceIte, bind_assoc]
    refine bind_congr fun res => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩ <;> rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rfl

theorem vSendC_eval [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hHB : HBounded h)
    (hh : hE.eval ρ = hsEncFn h) (hctx : ctxE.eval ρ = cGsEnc vpTblEnc ctx)
    (hp : pE.eval ρ = partyEnc P) (hs : sE.eval ρ = vpTblEnc s)
    (hm : mE.eval ρ = m) (hpair : pairE.eval ρ = pair) (hr : rE.eval ρ = r) :
    (vSendC hkC hE ctxE pE sE mE pairE rE).eval ρ =
      Prod.map (Option.map (Prod.map vpTblEnc id)) hsEncFn <$>
        (vSend hk ctx P s m pair r).run h := by
  unfold vSendC
  rw [vSend_eq_bind, eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair sE (.pair mE (.pair pairE rE)))))).eval ρ =
      (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, m, pair, r) := by
    simp [Expr.eval, hh, hctx, hp, hs, hm, hpair, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsT (.prod (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (.prod .bool (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
        (.prod (.base .msg) (.prod (.opt (.prod (.base .msg) (.base .msg)))
          (.opt (.base .ccoins))))))))
    (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, m, pair, r) ρ
  rw [eval_bind, StateT.run_bind, map_bind]
  rw [vSendStep1C_eval hsEncFn HBounded hkC hk hHk (.fst .v0) (.fst (.snd .v0))
        (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
        (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) ρ₁ h ctx P s r hHB rfl rfl rfl rfl rfl,
      bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ (fun ⟨s₁?, h₁⟩ hmem => ?_)
  have hHB₁ := vSendStep1_bounded hsEncFn HBounded hkC hk hHk ctx P s r h hHB (s₁?, h₁) hmem
  rcases s₁? with _ | s₁
  · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [Prod.map, Option.map_some]
    set ρ₂ := Env.cons (t := (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (vpTblEnc s₁)
      (Env.cons (t := .prod
        (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) hsT)
        (some (vpTblEnc s₁), hsEncFn h₁) ρ₁)
    change (Comp.caseOpt (vpVS .v0) _ _).eval ρ₂ = _
    rw [eval_caseOpt]
    have hvS : (vpVS (Expr.v0 (O := OO))).eval ρ₂ = s₁.vS := rfl
    rw [hvS]
    rcases hs1vS : s₁.vS with _ | v
    · simp [ρ₂, ρ₁, eval_ret, StateT.run_pure, ckaOps, hDefaultE, vpTcurNat, vpTcur,
        vpTblEnc, vpEnc, Expr.eval, Expr.v0, Expr.v1]
    · simp only [eval_bind]
      set ρ₃ := Env.cons (t := ssvT) v ρ₂
      have hFs := hHk.fsSend_eval (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
        (vpTcurNat .v1) .v0 (.pair (vpTcurNat .v1) (vpTcur .v1))
        (.fst (.snd (.snd (.snd (.snd .v3)))))
        (.fst (.snd (.snd (.snd (.snd (.snd .v3)))))) ρ₃ h₁ ctx P hHB₁ rfl rfl rfl
      change (hkC.fsSend _ _ _ _ _ _ _ _).eval ρ₃ =
        Prod.map id hsEncFn <$> (hk.fsSend ctx P s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair).run h₁ at hFs
      rw [hFs, StateT.run_bind, map_bind, bind_map_left]
      refine bind_congr fun ⟨fsRes, h₂⟩ => ?_
      rcases fsRes with _ | ⟨v', e⟩
      · simp [ρ₃, ρ₂, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
      · simp only [Prod.map, id_eq, Option.map_some, StateT.run_pure, map_pure]
        set ρ₄ := Env.cons (t := .prod ssvT (.base .ct)) (v', e)
          (Env.cons (t := .prod (.opt (.prod ssvT (.base .ct))) hsT)
            (some (v', e), hsEncFn h₂) ρ₃)
        change (Comp.ret _).eval ρ₄ = _
        have hSetVS := vpSetVS_eval (O' := OO) (Expr.v3 (O := OO)) (.some (.fst .v0)) ρ₄ s₁ rfl
        simp only [eval_ret, pair_eval, some_eval, hSetVS]
        rfl

theorem vRecvStep1C_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (c : Header T × E) (hHB : HBounded h)
    (hh : hE.eval ρ = hsEncFn h) (hctx : ctxE.eval ρ = cGsEnc vpTblEnc ctx)
    (hp : pE.eval ρ = partyEnc P) (hs : sE.eval ρ = vpTblEnc s) (hc : cE.eval ρ = c) :
    (vRecvStep1C hkC hE ctxE pE sE cE).eval ρ =
      Prod.map (Option.map (Option.map vpTblEnc)) hsEncFn <$>
        (vRecvStep1 hk ctx P s c).run h := by
  unfold vRecvStep1C vRecvStep1
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair sE cE)))).eval ρ =
      (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, c) := by
    simp [Expr.eval, hh, hctx, hp, hs, hc]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsT (.prod (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (.prod .bool (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
        hdrCtTy))))
    (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, c) ρ
  rw [eval_ite]
  have hEq : (Expr.eqN (.fst (.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OO))))))))
      (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))).eval ρ₁ =
      decide (c.1.1 = s.tcur + 1) := rfl
  rw [hEq]
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, decide_true, ↓reduceIte, eval_caseOpt]
    have hTn : (Expr.snd (.fst (.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))))).eval ρ₁ =
        c.1.2 := rfl
    rw [hTn]
    rcases hTopt : c.1.2 with _ | Tn
    · simp [ρ₁, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [eval_bind, StateT.run_bind, map_bind]
      set ρ₂ := Env.cons (t := (.base .t : Ty S)) Tn ρ₁
      have hStart := hHk.startRecv_eval (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
        (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
        (vpΓ (.fst (.snd (.snd (.snd .v1)))))
        (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0 ρ₂ h ctx P hHB rfl rfl rfl
      change (hkC.startRecv _ _ _ _ _ _ _).eval ρ₂ =
        Prod.map id hsEncFn <$> (hk.startRecv ctx P c.1.1 s.γ s.root Tn).run h at hStart
      rw [hStart, ht, bind_map_left]
      refine bind_congr fun ⟨res, h₁⟩ => ?_
      rcases res with _ | _ | ⟨γ', σ', rs⟩
      · simp [ρ₂, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
      · simp [ρ₂, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · simp only [Prod.map, id_eq, StateT.run_pure, map_pure, Option.map_some]
        set ρ₃ := Env.cons (t := .prod γvT (.prod svT rsvT)) (γ', σ', rs)
          (Env.cons (t := .opt (.prod γvT (.prod svT rsvT))) (some (γ', σ', rs))
            (Env.cons (t := .prod (.opt (.opt (.prod γvT (.prod svT rsvT)))) hsT)
              (some (some (γ', σ', rs)), hsEncFn h₁) ρ₂))
        change (Comp.ret _).eval ρ₃ = _
        simp [ρ₃, ρ₂, ρ₁, ht, vpMk, vpId, vpVS, vpVR, vpTcur, vpTblEnc, vpEnc,
          Expr.eval, Expr.v0, Expr.v2, Expr.v4]
        funext j
        by_cases hj : j = s.tcur + 1 <;> simp [Function.update, hj]
  · simp [ρ₁, ht, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]

theorem vRecvStep1_bounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (c : Header T × E) (h : HS) (hHB : HBounded h) :
    ∀ res ∈ support ((vRecvStep1 hk ctx P s c).run h), HBoundedPost res.2 := by
  intro ⟨s₁?, h₁⟩ hmem
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hT : c.1.2 with _ | Tn
    · simp only [hT, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hHk.hBounded_post _ hHB
    · simp only [hT, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨ans, h'⟩, hans, hmem⟩ := hmem
      have hHB' := hHk.startRecv_bounded ctx P (s.tcur + 1) s.γ s.root Tn h hHB (ans, h') hans
      rcases ans with _ | _ | ⟨γ', σ', rs⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩; exact hHB')
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hHk.hBounded_post _ hHB

theorem vRecvStep1_vrOk {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (c : Header T × E) (h : HS) (hHB : HBounded h)
    (hVR : ∀ t v, s.vR t = some v → VROk v) :
    ∀ res ∈ support ((vRecvStep1 hk ctx P s c).run h),
      ∀ s₁, res.1 = some (some s₁) → ∀ t v, s₁.vR t = some v → VROk v := by
  intro ⟨s₁?, h₁⟩ hmem s₁ hs₁ t v hv
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hT : c.1.2 with _ | Tn
    · simp only [hT, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, _⟩; cases hs₁
    · simp only [hT, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨ans, h'⟩, hans, hmem⟩ := hmem
      rcases ans with _ | _ | ⟨γ', σ', rs⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩
        cases hs₁
        dsimp only at hv
        by_cases hjt : t = s.tcur + 1
        · subst hjt
          simp only [Function.update_self, Option.some.injEq] at hv
          subst hv
          exact hHk.startRecv_vrOk ctx P (s.tcur + 1) s.γ s.root Tn h hHB _ hans γ' σ' rs rfl
        · simp only [Function.update_of_ne hjt] at hv
          exact hVR t v hv
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩
    cases hs₁
    exact hVR t v hv

theorem vRecv_eq_bind {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E) (rec_ : Option (Record M (Header T × E))) :
    vRecv hk ctx P s c rec_ =
      if s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1) then pure (some none)
      else
        (vRecvStep1 hk ctx P s c >>= fun s₁? =>
          match s₁? with
          | none => pure none
          | some none => pure (some none)
          | some (some s₁) =>
            match s₁.vR c.1.1 with
            | none => pure (some none)
            | some v => do
              match ← hk.fsRecv ctx P c.1.1 v c.1 c.2 rec_ with
              | none => pure none
              | some none => pure (some none)
              | some (some (v', i, m)) =>
                pure (some (some ({ s₁ with vR := Function.update s₁.vR c.1.1 (some v') },
                                  c.1.1, i, m)))) := by
  unfold vRecv vRecvStep1
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases ht : c.1.1 = s.tcur + 1
    · simp only [ht, ↓reduceIte]
      rcases c.1.2 with _ | Tn
      · rfl
      · simp only [bind_assoc]
        refine bind_congr fun res => ?_
        rcases res with _ | _ | ⟨γ', σ', rs⟩ <;> rfl
    · simp only [ht, ↓reduceIte, pure_bind]
      rfl

theorem vRecvC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    {Γ'} (hE : Expr OO Γ' hsT)
    (ctxE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (cE : Expr OO Γ' hdrCtTy)
    (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : HS) (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (c : Header T × E) (rec_ : Option (Record M (Header T × E)))
    (hHB : HBounded h) (hVR : ∀ t v, s.vR t = some v → VROk v)
    (hh : hE.eval ρ = hsEncFn h) (hctx : ctxE.eval ρ = cGsEnc vpTblEnc ctx)
    (hp : pE.eval ρ = partyEnc P) (hs : sE.eval ρ = vpTblEnc s)
    (hc : cE.eval ρ = c) (hrec : recE.eval ρ = rec_.map cRecEnc) :
    (vRecvC hkC hE ctxE pE sE cE recE).eval ρ =
      Prod.map (Option.map (Option.map (Prod.map vpTblEnc id))) hsEncFn <$>
        (vRecv hk ctx P s c rec_).run h := by
  unfold vRecvC
  rw [vRecv_eq_bind, eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair sE (.pair cE recE))))).eval ρ =
      (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, c, rec_.map cRecEnc) := by
    simp [Expr.eval, hh, hctx, hp, hs, hc, hrec]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsT (.prod (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (.prod .bool (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
        (.prod hdrCtTy (.opt cRecTy))))))
    (hsEncFn h, cGsEnc vpTblEnc ctx, partyEnc P, vpTblEnc s, c, rec_.map cRecEnc) ρ
  rw [eval_ite]
  have hRef : (orE (sendsInE (vpId (.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))))
        (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v0))))))))
      (.lt (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
        (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v0))))))))).eval ρ₁ =
      (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) := by
    rw [orE_eval, sendsInE_eval _ _ ρ₁ s.id rfl]
    rfl
  rw [hRef]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [ρ₁, href, eval_ret, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind, StateT.run_bind, map_bind]
    rw [vRecvStep1C_eval hsEncFn HBounded hkC hk hHk (.fst .v0) (.fst (.snd .v0))
          (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
          (.fst (.snd (.snd (.snd (.snd .v0))))) ρ₁ h ctx P s c hHB rfl rfl rfl rfl rfl,
        bind_map_left]
    refine OracleComp.bind_congr_of_forall_mem_support _ (fun ⟨s₁?, h₁⟩ hmem => ?_)
    have hHB₁ := vRecvStep1_bounded hsEncFn HBounded hkC hk hHk ctx P s c h hHB (s₁?, h₁) hmem
    rcases s₁? with _ | _ | s₁
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · simp only [Prod.map, Option.map_some]
      have hVR₁ := vRecvStep1_vrOk hsEncFn HBounded hkC hk hHk ctx P s c h hHB hVR
        (some (some s₁), h₁) hmem s₁ rfl
      set ρ₂ := Env.cons (t := (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
        (vpTblEnc s₁)
        (Env.cons (t := .opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
          (some (vpTblEnc s₁))
          (Env.cons (t := .prod
            (.opt (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))) hsT)
            (some (some (vpTblEnc s₁)), hsEncFn h₁) ρ₁))
      change (Comp.caseOpt (.tget (vpVR .v0) (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v3))))))))
        _ _).eval ρ₂ = _
      rw [eval_caseOpt]
      have hvR : (Expr.tget (vpVR (Expr.v0 (O := OO)))
          (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v3)))))))).eval ρ₂ = s₁.vR c.1.1 := rfl
      rw [hvR]
      rcases hs1vR : s₁.vR c.1.1 with _ | v
      · simp [ρ₂, ρ₁, eval_ret, StateT.run_pure, Expr.eval, Expr.v2]
      · simp only [eval_bind]
        set ρ₃ := Env.cons (t := rsvT) v ρ₂
        have hvOk : VROk ((Expr.v0 (O := OO)).eval ρ₃) := hVR₁ c.1.1 v hs1vR
        have hFs := hHk.fsRecv_eval (.snd .v3) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
          (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
          (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))
          (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
          (.snd (.snd (.snd (.snd (.snd .v4))))) ρ₃ h₁ ctx P rec_ hHB₁ hvOk rfl rfl rfl rfl
        change (hkC.fsRecv _ _ _ _ _ _ _ _).eval ρ₃ =
          Prod.map id hsEncFn <$> (hk.fsRecv ctx P c.1.1 v c.1 c.2 rec_).run h₁ at hFs
        rw [hFs, StateT.run_bind, map_bind, bind_map_left]
        refine bind_congr fun ⟨fsRes, h₂⟩ => ?_
        rcases fsRes with _ | _ | ⟨v', i, m⟩
        · simp [ρ₃, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
        · simp [ρ₃, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · simp only [Prod.map, id_eq, Option.map_some, StateT.run_pure, map_pure]
          set ρ₄ := Env.cons (t := .prod rsvT (.prod .nat (.base .msg))) (v', i, m)
            (Env.cons (t := .opt (.prod rsvT (.prod .nat (.base .msg)))) (some (v', i, m))
              (Env.cons (t := .prod (.opt (.opt (.prod rsvT (.prod .nat (.base .msg))))) hsT)
                (some (some (v', i, m)), hsEncFn h₂) ρ₃))
          change (Comp.ret _).eval ρ₄ = _
          have hSetVR := vpSetVR_eval (O' := OO) (Expr.v4 (O := OO))
            (.tset (vpVR .v4) (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v7)))))))
              (.some (.fst .v0))) ρ₄ s₁ rfl
          simp only [eval_ret, pair_eval, some_eval, hSetVR, tset_eval_eq_update]
          rfl

theorem vRecv_bounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (ctx : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (s : VP γvT.denote T svT.denote ssvT.denote rsvT.denote)
    (c : Header T × E) (rec_ : Option (Record M (Header T × E)))
    (h : HS) (hHB : HBounded h) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec_).run h), HBoundedPost res.2 := by
  intro ⟨res, h₂⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hHk.hBounded_post _ hHB
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hs₁, hmem⟩ := hmem
    have hHB₁ := vRecvStep1_bounded hsEncFn HBounded hkC hk hHk ctx P s c h hHB (s₁?, h₁) hs₁
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hHB₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hHB₁
    · rcases hv : s₁.vR c.1.1 with _ | v
      · simp only [hv, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hHB₁
      · simp only [hv, StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨fsRes, h'⟩, hfs, hmem⟩ := hmem
        have hHB' := hHk.fsRecv_bounded ctx P c.1.1 v c.1 c.2 rec_ h₁ hHB₁ (fsRes, h') hfs
        rcases fsRes with _ | _ | ⟨v', i, m⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩; exact hHB')

theorem commitEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L : ℕ)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (sE : Expr OO Γ' (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (posE : Expr OO Γ' posTy) (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (s : Ctx γvT.denote T svT.denote ssvT.denote rsvT.denote M E)
    (P : Party) (old new : VP γvT.denote T svT.denote ssvT.denote rsvT.denote) (pos : Pos)
    (hHB : HBoundedPost es.h) (hBound : SMStateBoundedEngine L s)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hs : sE.eval ρ = cGsEnc vpTblEnc s) (hp : pE.eval ρ = partyEnc P)
    (hold : oldE.eval ρ = vpTblEnc old) (hnew : newE.eval ρ = vpTblEnc new)
    (hpos : posE.eval ρ = posEnc pos) :
    (commitEC hkC L esE sE pE oldE newE posE).eval ρ =
      Prod.map (Option.map (cGsEnc vpTblEnc)) (esEnc vpTblEnc hsEncFn) <$>
        (commitE hk s P old new pos).run es := by
  unfold commitEC commitE abortE
  rw [eval_bind_ret]
  have hAcc := cAcceptE_eval vpTblEnc L sE pE newE posE ρ s P new pos
    hBound.trans_le hBound.chall_le hBound.comp_le hs hp hnew hpos
  have h0 : (Expr.pair esE (.pair (cAcceptE L sE pE newE posE)
      (.pair pE (.pair oldE newE)))).eval ρ =
      (esEnc vpTblEnc hsEncFn es, cGsEnc vpTblEnc (s.accept P new pos),
       partyEnc P, vpTblEnc old, vpTblEnc new) := by
    simp [Expr.eval, hes, hAcc, hp, hold, hnew]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
        (.prod .bool
          (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))))
    (esEnc vpTblEnc hsEncFn es, cGsEnc vpTblEnc (s.accept P new pos),
     partyEnc P, vpTblEnc old, vpTblEnc new) ρ
  rw [eval_bind]
  have hCom := hHk.commit_eval (esH (.fst .v0)) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    ρ₁ es.h (s.accept P new pos) P old new hHB rfl rfl rfl rfl rfl
  rw [hCom, bind_map_left, run_liftH_bind, map_bind]
  refine bind_congr fun ⟨res, h'⟩ => ?_
  rcases res with _ | new'
  · simp [ρ₁, Comp.eval, StateT.run_modify, Prod.map, esMk, esG, esEnc,
      Expr.eval, Expr.v0, Expr.v1]
  · simp only [Prod.map, Option.map_some, StateT.run_pure, map_pure]
    set ρ₂ := Env.cons (t := (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
      (vpTblEnc new')
      (Env.cons (t := .prod
        (.opt (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)) hsT)
        (some (vpTblEnc new'), hsEncFn h') ρ₁)
    change (Comp.ret _).eval ρ₂ = _
    have hSetSt := cGsSetStP_eval vpTblEnc (O' := OO)
      (.fst (.snd .v2)) (.fst (.snd (.snd .v2))) .v0 ρ₂ (s.accept P new pos) P new' rfl rfl rfl
    simp only [eval_ret, pair_eval, some_eval, hSetSt]
    rfl

theorem transmitEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep : ℕ) (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (m : M) (r : Option CCoins)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, m, r)) :
    (transmitEC hkC L Δ qep π esE argE).eval ρ =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (transmitE hk Δ qep π (P, m, r)).run es := by
  unfold transmitEC transmitE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, m, r) := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, m, r) ρ
  rw [eval_ite]
  have hCond1 : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (cGsWin (esG (.fst .v0)))).eval ρ₁ = (es.abort || es.g.win) := by
    simp [ρ₁, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0]
  rw [hCond1]
  by_cases hab : (es.abort || es.g.win)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hab, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_caseOpt]
    have hEp : (cEpMgmtE Δ qep (esG (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd .v0))))).eval ρ₁ =
        (es.g.epMgmt Δ qep P r.isSome).map (cGsEnc vpTblEnc) := by
      have := cEpMgmtE_eval vpTblEnc (O' := OO) Δ qep
        (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd .v0))))
        ρ₁ es.g P rfl rfl
      simpa [ρ₁, isSomeE_eval, Expr.eval, Expr.v0] using this
    rw [hEp]
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some]
      set ρ₂ := Env.cons
        (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
        (cGsEnc vpTblEnc s₁) ρ₁
      rw [eval_ite]
      have hs₁Leaks : s₁.leaks.length ≤ L := epMgmt_leaks_le hBound hep
      have hDoom : (leakDoomE L π (esG (.fst (Expr.v1 (O := OO)))) .v0).eval ρ₂ =
          π.leakDoom es.g s₁ :=
        leakDoomE_eval vpTblEnc (O' := OO) L π (esG (.fst .v1)) .v0 ρ₂ es.g s₁
          hs₁Leaks rfl rfl
      rw [hDoom]
      by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, eval_ret, pair_eval,
          StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure, Prod.map]
        have hSetAb := esSetAbort_eval vpTblEnc hsEncFn (O' := OO)
          (.fst .v1) (.bool true) ρ₂ es rfl
        simp only [Expr.eval] at hSetAb ⊢
        rw [hSetAb]; rfl
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, eval_bind]
        have hStP : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst (.snd .v1))).eval ρ₂ =
            vpTblEnc (s₁.st P) :=
          pGet_eval (cGsSt .v0) (.fst (.snd .v1)) ρ₂ (fun Q => vpTblEnc (s₁.st Q)) P rfl rfl
        have hVSend := vSendC_eval hDefaultE hsEncFn HBounded hkC hk hHk
          (esH (.fst .v1)) .v0 (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1)))
          (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
          ρ₂ es.h s₁ P (s₁.st P) m none r hHB rfl rfl rfl hStP rfl rfl rfl
        rw [hVSend, bind_map_left, run_liftH_bind, map_bind]
        refine bind_congr fun ⟨vsRes, h'⟩ => ?_
        rcases vsRes with _ | ⟨st', c⟩
        · simp [ρ₂, ρ₁, Comp.eval, StateT.run_modify,
            Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v2]
        · simp only [Prod.map, Option.map_some, id_eq,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
          set ρ₃ := Env.cons
            (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hdrCtTy)
            (vpTblEnc st', c)
            (Env.cons
              (t := .prod
                (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                  hdrCtTy)) hsT)
              (some (vpTblEnc st', c), hsEncFn h') ρ₂)
          change (Comp.ret _).eval ρ₃ = _
          have hEp3 : (pGet (cGsEpoch (Expr.v2 (O := OO))) (.fst (.snd .v3))).eval ρ₃ =
              s₁.epoch P :=
            pGet_eval (cGsEpoch .v2) (.fst (.snd .v3)) ρ₃ s₁.epoch P rfl rfl
          have hIdx3 : (pGet (cGsIdx (Expr.v2 (O := OO))) (.fst (.snd .v3))).eval ρ₃ =
              s₁.idx P :=
            pGet_eval (cGsIdx .v2) (.fst (.snd .v3)) ρ₃ s₁.idx P rfl rfl
          have hRecE : (Expr.pair
              (.pair (.fst (.snd (Expr.v3 (O := OO))))
                (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
              (.pair (.fst (.snd (.snd .v3))) (.snd .v0))).eval ρ₃ =
              cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ := by
            simp only [Expr.eval, hEp3, hIdx3]
            rfl
          have hRecord := cRecordE_eval vpTblEnc (O' := OO) L Δ
            (Expr.v2 (O := OO)) (.fst (.snd .v3)) (.fst .v0)
            (.pair (.pair (.fst (.snd .v3))
              (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
              (.pair (.fst (.snd (.snd .v3))) (.snd .v0)))
            (.bool false) ρ₃ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩
            ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
            rfl rfl rfl hRecE
          simp only [eval_ret, esMk, pair_eval, some_eval, hRecord]
          rfl

theorem challEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (challEC hkC L Δ qep cfgC π esE argE).eval ρ =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (challE hk Δ qep cfg π (P, m₀, m₁, r)).run es := by
  unfold challEC challE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, m₀, m₁, r) := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, m₀, m₁, r) ρ
  rw [eval_ite]
  have hCond1 : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (cGsWin (esG (.fst .v0)))).eval ρ₁ = (es.abort || es.g.win) := by
    simp [ρ₁, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0]
  rw [hCond1]
  by_cases hab : (es.abort || es.g.win)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hab, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_caseOpt]
    have hEp : (cEpMgmtE Δ qep (esG (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0))
        (isSomeE (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
        (es.g.epMgmt Δ qep P r.isSome).map (cGsEnc vpTblEnc) := by
      have := cEpMgmtE_eval vpTblEnc (O' := OO) Δ qep
        (esG (.fst .v0)) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
        ρ₁ es.g P rfl rfl
      simpa [ρ₁, isSomeE_eval, Expr.eval, Expr.v0] using this
    rw [hEp]
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some]
      set ρ₂ := Env.cons
        (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
        (cGsEnc vpTblEnc s₁) ρ₁
      rw [eval_ite]
      have hSafe : (cSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v1))).eval ρ₂ = s₁.safeCh Δ P :=
        cSafeChE_eval vpTblEnc (O' := OO) Δ .v0 (.fst (.snd .v1)) ρ₂ s₁ P rfl rfl
      have hEp2 : (pGet (cGsEpoch (Expr.v0 (O := OO))) (.fst (.snd .v1))).eval ρ₂ = s₁.epoch P :=
        pGet_eval (cGsEpoch .v0) (.fst (.snd .v1)) ρ₂ s₁.epoch P rfl rfl
      have hChOK : (cfgC.challOKE (pGet (cGsEpoch .v0) (.fst (.snd .v1)))).eval ρ₂ =
          cfg.challAllowedIn (s₁.epoch P) := by
        rw [hCfg.challOK_eq, hEp2]
      have hCondCh : (orE (.not (cSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v1))))
          (.not (cfgC.challOKE (pGet (cGsEpoch .v0) (.fst (.snd .v1)))))).eval ρ₂ =
          (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P))) := by
        simp [orE_eval, Expr.eval, hSafe, hChOK]
      rw [hCondCh]
      by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, eval_ret, StateT.run_pure, map_pure, Prod.map]
        simp [ρ₂, ρ₁, Expr.eval, Expr.v1]
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hs₁Leaks : s₁.leaks.length ≤ L := epMgmt_leaks_le hBound hep
        have hDoom : (leakDoomE L π (esG (.fst (Expr.v1 (O := OO)))) .v0).eval ρ₂ =
            π.leakDoom es.g s₁ :=
          leakDoomE_eval vpTblEnc (O' := OO) L π (esG (.fst .v1)) .v0 ρ₂ es.g s₁
            hs₁Leaks rfl rfl
        rw [hDoom]
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, eval_ret, pair_eval,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure, Prod.map]
          have hSetAb := esSetAbort_eval vpTblEnc hsEncFn (O' := OO)
            (.fst .v1) (.bool true) ρ₂ es rfl
          simp only [Expr.eval] at hSetAb ⊢
          rw [hSetAb]; rfl
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, eval_bind]
          set mChall := (cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)
          have hStP : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst (.snd .v1))).eval ρ₂ =
              vpTblEnc (s₁.st P) :=
            pGet_eval (cGsSt .v0) (.fst (.snd .v1)) ρ₂ (fun Q => vpTblEnc (s₁.st Q)) P rfl rfl
          have hmChall2 : (cfgC.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1)))
              (cGsB (esG (.fst .v1))) (.fst (.snd (.snd .v1)))
              (.fst (.snd (.snd (.snd .v1))))).eval ρ₂ = mChall := by
            rw [hCfg.challMsg_eq, hEp2]
            rfl
          have hVSend := vSendC_eval hDefaultE hsEncFn HBounded hkC hk hHk
            (esH (.fst .v1)) .v0 (.fst (.snd .v1)) (pGet (cGsSt .v0) (.fst (.snd .v1)))
            (cfgC.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1))) (cGsB (esG (.fst .v1)))
              (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
            (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
            (.snd (.snd (.snd (.snd .v1))))
            ρ₂ es.h s₁ P (s₁.st P) mChall (some (m₀, m₁)) r hHB rfl rfl rfl hStP hmChall2 rfl rfl
          rw [hVSend, bind_map_left, run_liftH_bind, map_bind]
          refine bind_congr fun ⟨vsRes, h'⟩ => ?_
          rcases vsRes with _ | ⟨st', c⟩
          · simp [ρ₂, ρ₁, Comp.eval, StateT.run_modify,
              Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v2]
          · simp only [Prod.map, Option.map_some, id_eq,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
            set ρ₃ := Env.cons
              (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hdrCtTy)
              (vpTblEnc st', c)
              (Env.cons
                (t := .prod
                  (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                    hdrCtTy)) hsT)
                (some (vpTblEnc st', c), hsEncFn h') ρ₂)
            change (Comp.ret _).eval ρ₃ = _
            have hEp3 : (pGet (cGsEpoch (Expr.v2 (O := OO))) (.fst (.snd .v3))).eval ρ₃ =
                s₁.epoch P :=
              pGet_eval (cGsEpoch .v2) (.fst (.snd .v3)) ρ₃ s₁.epoch P rfl rfl
            have hIdx3 : (pGet (cGsIdx (Expr.v2 (O := OO))) (.fst (.snd .v3))).eval ρ₃ =
                s₁.idx P :=
              pGet_eval (cGsIdx .v2) (.fst (.snd .v3)) ρ₃ s₁.idx P rfl rfl
            have hmChall3 : (cfgC.challMsgE (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                (cGsB (esG (.fst .v3))) (.fst (.snd (.snd .v3)))
                (.fst (.snd (.snd (.snd .v3))))).eval ρ₃ = mChall := by
              rw [hCfg.challMsg_eq, hEp3]
              rfl
            have hRecE : (Expr.pair
                (.pair (.fst (.snd (Expr.v3 (O := OO))))
                  (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                    (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
                (.pair (cfgC.challMsgE (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (cGsB (esG (.fst .v3))) (.fst (.snd (.snd .v3)))
                  (.fst (.snd (.snd (.snd .v3))))) (.snd .v0))).eval ρ₃ =
                cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mChall, c⟩ := by
              simp only [Expr.eval, hEp3, hIdx3, hmChall3]
              rfl
            have hRecord := cRecordE_eval vpTblEnc (O' := OO) L Δ
              (Expr.v2 (O := OO)) (.fst (.snd .v3)) (.fst .v0)
              (.pair (.pair (.fst (.snd .v3))
                (.pair (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (.add (pGet (cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
                (.pair (cfgC.challMsgE (pGet (cGsEpoch .v2) (.fst (.snd .v3)))
                  (cGsB (esG (.fst .v3))) (.fst (.snd (.snd .v3)))
                  (.fst (.snd (.snd (.snd .v3))))) (.snd .v0)))
              (.bool true) ρ₃ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mChall, c⟩
              ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
              rfl rfl rfl hRecE
            simp only [eval_ret, esMk, pair_eval, some_eval, hRecord]
            rfl

theorem deliverEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c)) :
    (deliverEC hkC L maxSkip cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (deliverE hk maxSkip cfg (P, c)).run es := by
  unfold deliverEC deliverE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, c) := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool hdrCtTy))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, c) ρ
  rw [eval_ite]
  have hCond1 : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (cGsWin (esG (.fst .v0)))).eval ρ₁ = (es.abort || es.g.win) := by
    simp [ρ₁, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0]
  rw [hCond1]
  by_cases hab : (es.abort || es.g.win)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hab, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_caseOpt]
    have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc P.other := by
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    have hInTr : (cInTransitE L (esG (.fst (Expr.v0 (O := OO))))
        (otherE (.fst (.snd .v0))) (.snd (.snd .v0))).eval ρ₁ =
        (es.g.inTransit P.other c).map cRecEnc :=
      cInTransitE_eval vpTblEnc L (esG (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
        ρ₁ es.g P.other heqT heqE hBound.trans_le rfl hOther
    rw [hInTr]
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some, eval_bind]
      set ρ₂ := Env.cons (t := cRecTy) (cRecEnc r) ρ₁
      have hStP : (pGet (cGsSt (esG (.fst (Expr.v1 (O := OO)))))
          (.fst (.snd .v1))).eval ρ₂ = vpTblEnc (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v1))) (.fst (.snd .v1)) ρ₂
          (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
      have hVRecv := vRecvC_eval hsEncFn HBounded hkC hk hHk
        (esH (.fst .v1)) (esG (.fst .v1)) (.fst (.snd .v1))
        (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
        ρ₂ es.h es.g P (es.g.st P) c (some r) hHB hVR rfl rfl rfl hStP rfl rfl
      rw [hVRecv, bind_map_left, run_liftH_bind, map_bind]
      refine OracleComp.bind_congr_of_forall_mem_support
        ((vRecv hk es.g P (es.g.st P) c (some r)).run es.h)
        fun ⟨vrRes, h'⟩ hvrMem => ?_
      have hHB' : HBoundedPost h' :=
        vRecv_bounded hsEncFn HBounded hkC hk hHk es.g P (es.g.st P) c (some r) es.h hHB
          (vrRes, h') hvrMem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp [ρ₂, ρ₁, Comp.eval, StateT.run_modify,
          Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v2]
      · simp only [Prod.map, Option.map_some, Option.map_none]
        set ρ₃ := Env.cons
          (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (.prod .nat (.prod .nat (.base .msg)))))
          none
          (Env.cons
            (t := .prod
              (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                (.prod .nat (.prod .nat (.base .msg)))))) hsT)
            (some none, hsEncFn h') ρ₂)
        change (Comp.ret _).eval ρ₃ = _
        have hMust3 : (Expr.and (O := OO) (.bool cfgC.deliverWin)
            (cMustBeCorrectE L maxSkip (esG (.fst .v3)) (.fst (.snd .v3)) .v2)).eval ρ₃ =
            (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) := by
          rw [and_eval, cMustBeCorrectE_eval vpTblEnc (O' := OO) L maxSkip
            (esG (.fst .v3)) (.fst (.snd .v3)) .v2 ρ₃ es.g P r hBound.comp_le rfl rfl rfl]
          simp [Expr.eval, hCfg.deliverWin_eq]
        have hSetWin3 := cGsSetWin_eval vpTblEnc (O' := OO)
          (esG (.fst .v3)) (.bool true) ρ₃ es.g rfl
        simp only [eval_ret, pair_eval, some_eval, inl_eval, esMk, ite_eval, hMust3, hSetWin3]
        by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
        · simp [ρ₃, ρ₂, ρ₁, hmust, StateT.run_modify,
            esAbort, esEnc, smRrEnc, Expr.eval, Expr.v1, Expr.v3]
        · simp [ρ₃, ρ₂, ρ₁, hmust, StateT.run_pure,
            esG, esAbort, esEnc, smRrEnc, Expr.eval, Expr.v1, Expr.v3]
      · simp only [Prod.map, Option.map_some, id_eq]
        change (Comp.bind (commitEC hkC L (esSetH (.fst .v4) (.snd .v2))
            (esG (.fst .v4)) (.fst (.snd .v4))
            (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (cRecPos .v3)) _).eval
          (Env.cons
            (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg))))
            (vpTblEnc st', t', i', m')
            (Env.cons
              (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                (.prod .nat (.prod .nat (.base .msg)))))
              (some (vpTblEnc st', t', i', m'))
              (Env.cons
                (t := .prod
                  (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                    (.prod .nat (.prod .nat (.base .msg)))))) hsT)
                (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₂))) = _
        set ρ₄ := Env.cons
          (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (.prod .nat (.prod .nat (.base .msg))))
          (vpTblEnc st', t', i', m')
          (Env.cons
            (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg)))))
            (some (vpTblEnc st', t', i', m'))
            (Env.cons
              (t := .prod
                (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                  (.prod .nat (.prod .nat (.base .msg)))))) hsT)
              (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₂))
        rw [eval_bind]
        have hes4' : (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2)).eval ρ₄ =
            esEnc vpTblEnc hsEncFn { es with h := h' } :=
          esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v4) (.snd .v2) ρ₄ es h' rfl rfl
        have hSt4 : (pGet (cGsSt (esG (.fst (Expr.v4 (O := OO)))))
            (.fst (.snd .v4))).eval ρ₄ = vpTblEnc (es.g.st P) :=
          pGet_eval (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)) ρ₄
            (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
        have hCom := commitEC_eval hsEncFn HBounded hkC hk hHk L
          (esSetH (.fst .v4) (.snd .v2)) (esG (.fst .v4)) (.fst (.snd .v4))
          (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (cRecPos .v3)
          ρ₄ { es with h := h' } es.g P (es.g.st P) st' r.pos hHB' hBound
          hes4' rfl rfl hSt4 rfl rfl
        rw [hCom, StateT.run_bind, bind_map_left, map_bind]
        refine bind_congr fun ⟨cmRes, es''⟩ => ?_
        rcases cmRes with _ | s_acc
        · simp [ρ₄, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
        · simp only [Prod.map, Option.map_some,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
          set ρ₅ := Env.cons
            (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
            (cGsEnc vpTblEnc s_acc)
            (Env.cons
              (t := .prod
                (.opt (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
                (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
              (some (cGsEnc vpTblEnc s_acc), esEnc vpTblEnc hsEncFn es'') ρ₄)
          change (Comp.ret _).eval ρ₅ = _
          have hMust6 : (Expr.and (O := OO) (.bool cfgC.deliverWin)
              (cMustBeCorrectE L maxSkip (esG (.fst .v6)) (.fst (.snd .v6)) .v5)).eval ρ₅ =
              (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) := by
            rw [and_eval, cMustBeCorrectE_eval vpTblEnc (O' := OO) L maxSkip
              (esG (.fst .v6)) (.fst (.snd .v6)) .v5 ρ₅ es.g P r hBound.comp_le rfl rfl rfl]
            simp [Expr.eval, hCfg.deliverWin_eq]
          have hEqOut : (Expr.and (O := OO) (.eqN (.fst (.snd .v2)) (posEpoch (cRecPos .v5)))
              (.and (.eqN (.fst (.snd (.snd .v2))) (posIdx (cRecPos .v5)))
                (Expr.op (O := OO) CKAOp.eqM
                  (.pair (.snd (.snd (.snd .v2))) (cRecMsg .v5))))).eval ρ₅ =
              decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg)) := by
            simp only [ρ₅, ρ₄, ρ₂, cRecPos, posEpoch, posIdx, cRecMsg, ckaOps, heqM,
              cRecEnc, posEnc, Expr.eval, Expr.v2, Expr.v5,
              Env.get_cons_zero, Env.get_cons_succ, BEq.beq]
            by_cases ht : t' = r.pos.epoch <;>
            by_cases hi : i' = r.pos.idx <;>
            by_cases hm : m' = r.msg <;>
            simp [ht, hi, hm]
          have hBad : (Expr.and (O := OO)
              (.and (.bool cfgC.deliverWin)
                (cMustBeCorrectE L maxSkip (esG (.fst .v6)) (.fst (.snd .v6)) .v5))
              (.not (.and (.eqN (.fst (.snd .v2)) (posEpoch (cRecPos .v5)))
                (.and (.eqN (.fst (.snd (.snd .v2))) (posIdx (cRecPos .v5)))
                  (Expr.op (O := OO) CKAOp.eqM
                    (.pair (.snd (.snd (.snd .v2))) (cRecMsg .v5))))))).eval ρ₅ =
              ((cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) &&
                !decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) := by
            rw [and_eval, not_eval, hMust6, hEqOut]
          have hChall : (cChallContainsE L (esG (.fst (Expr.v6 (O := OO))))
              (cRecPos .v5)).eval ρ₅ = es.g.chall.contains r.pos :=
            cChallContainsE_eval vpTblEnc (O' := OO) L (esG (.fst .v6)) (cRecPos .v5)
              ρ₅ es.g r.pos hBound.chall_le rfl rfl
          have hSetWin := cGsSetWin_eval vpTblEnc (O' := OO) .v0 (.bool true) ρ₅ s_acc rfl
          set bad := (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) &&
            !decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))
          have hgFinal : (Expr.ite (O := OO)
              (.and (.and (.bool cfgC.deliverWin)
                (cMustBeCorrectE L maxSkip (esG (.fst .v6)) (.fst (.snd .v6)) .v5))
                (.not (.and (.eqN (.fst (.snd .v2)) (posEpoch (cRecPos .v5)))
                   (.and (.eqN (.fst (.snd (.snd .v2))) (posIdx (cRecPos .v5)))
                     (Expr.op (O := OO) CKAOp.eqM
                       (.pair (.snd (.snd (.snd .v2))) (cRecMsg .v5)))))))
              (cGsSetWin .v0 (.bool true)) .v0).eval ρ₅ =
              cGsEnc vpTblEnc (if bad then { s_acc with win := true } else s_acc) := by
            rw [ite_eval, hBad, hSetWin]
            by_cases hb : bad <;> simp [hb, ρ₅, Expr.eval, Expr.v0]
          have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO) (.snd .v1)
            (.ite (.and (.and (.bool cfgC.deliverWin)
                (cMustBeCorrectE L maxSkip (esG (.fst .v6)) (.fst (.snd .v6)) .v5))
                (.not (.and (.eqN (.fst (.snd .v2)) (posEpoch (cRecPos .v5)))
                  (.and (.eqN (.fst (.snd (.snd .v2))) (posIdx (cRecPos .v5)))
                    (Expr.op (O := OO) CKAOp.eqM
                      (.pair (.snd (.snd (.snd .v2))) (cRecMsg .v5)))))))
              (cGsSetWin .v0 (.bool true)) .v0)
            ρ₅ es'' (if bad then { s_acc with win := true } else s_acc) rfl hgFinal
          simp only [eval_ret, pair_eval, some_eval, inr_eval, ite_eval, hChall, hSetG]
          cases es.g.chall.contains r.pos <;> rfl

theorem injectEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c)) :
    (injectEC hkC L Δ qep cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (injectE hk Δ qep cfg (P, c)).run es := by
  unfold injectEC injectE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, c) := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool hdrCtTy))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, c) ρ
  rw [eval_ite]
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc P.other := by
    simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
  have hInTr : (cInTransitE L (esG (.fst (Expr.v0 (O := OO))))
      (otherE (.fst (.snd .v0))) (.snd (.snd .v0))).eval ρ₁ =
      (es.g.inTransit P.other c).map cRecEnc :=
    cInTransitE_eval vpTblEnc L (esG (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
      ρ₁ es.g P.other heqT heqE hBound.trans_le rfl hOther
  have hSafeInj : (cSafeInjE Δ (esG (.fst (Expr.v0 (O := OO))))).eval ρ₁ = es.g.safeInj Δ :=
    cSafeInjE_eval vpTblEnc (O' := OO) Δ (esG (.fst .v0)) ρ₁ es.g rfl
  have hRefuse : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (orE (cGsWin (esG (.fst .v0)))
        (orE (isSomeE (cInTransitE L (esG (.fst .v0))
            (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (.not (cSafeInjE Δ (esG (.fst .v0))))))).eval ρ₁ =
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) := by
    simp only [orE_eval, isSomeE_eval, not_eval, hInTr, Option.isSome_map, hSafeInj]
    simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
    have hStP : (pGet (cGsSt (esG (.fst (Expr.v0 (O := OO)))))
        (.fst (.snd .v0))).eval ρ₁ = vpTblEnc (es.g.st P) :=
      pGet_eval (cGsSt (esG (.fst .v0))) (.fst (.snd .v0)) ρ₁
        (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
    have hVRecv := vRecvC_eval hsEncFn HBounded hkC hk hHk
      (esH (.fst .v0)) (esG (.fst .v0)) (.fst (.snd .v0))
      (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
      ρ₁ es.h es.g P (es.g.st P) c none hHB hVR rfl rfl rfl hStP rfl rfl
    rw [hVRecv, bind_map_left, run_liftH_bind, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support
      ((vRecv hk es.g P (es.g.st P) c none).run es.h)
      fun ⟨vrRes, h'⟩ hvrMem => ?_
    have hHB' : HBoundedPost h' :=
      vRecv_bounded hsEncFn HBounded hkC hk hHk es.g P (es.g.st P) c none es.h hHB
        (vrRes, h') hvrMem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp [ρ₁, Comp.eval, StateT.run_modify,
        Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v1]
    · simp only [Prod.map, Option.map_some, Option.map_none,
        StateT.run_pure, map_pure]
      set ρ₂ := Env.cons
        (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          (.prod .nat (.prod .nat (.base .msg)))))
        none
        (Env.cons
          (t := .prod
            (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg)))))) hsT)
          (some none, hsEncFn h') ρ₁)
      change (Comp.ret _).eval ρ₂ = _
      have hSetH := esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v2) (.snd .v1) ρ₂ es h' rfl rfl
      simp only [eval_ret, pair_eval, some_eval, inl_eval, hSetH]
      rfl
    · simp only [Prod.map, Option.map_some, id_eq]
      change (Comp.ite (.lt (.nat (qep + 1)) (.fst (.snd .v0))) _ _).eval
        (Env.cons
          (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (.prod .nat (.prod .nat (.base .msg))))
          (vpTblEnc st', t', i', m')
          (Env.cons
            (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg)))))
            (some (vpTblEnc st', t', i', m'))
            (Env.cons
              (t := .prod
                (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                  (.prod .nat (.prod .nat (.base .msg)))))) hsT)
              (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₁))) = _
      set ρ₃ := Env.cons
        (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          (.prod .nat (.prod .nat (.base .msg))))
        (vpTblEnc st', t', i', m')
        (Env.cons
          (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (.prod .nat (.prod .nat (.base .msg)))))
          (some (vpTblEnc st', t', i', m'))
          (Env.cons
            (t := .prod
              (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                (.prod .nat (.prod .nat (.base .msg)))))) hsT)
            (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₁))
      have hes3' : (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2)).eval ρ₃ =
          esEnc vpTblEnc hsEncFn { es with h := h' } :=
        esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v3) (.snd .v2) ρ₃ es h' rfl rfl
      rw [eval_ite]
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, eval_ret, pair_eval, some_eval, inl_eval, hes3',
          StateT.run_pure, map_pure]
        rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
        have hPos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₃ =
            posEnc ⟨P.other, t', i'⟩ := by
          simp [ρ₃, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
        have hTriv : (cTrivialE L Δ (esG (.fst (Expr.v3 (O := OO))))
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₃ =
            es.g.trivial Δ ⟨P.other, t', i'⟩ :=
          cTrivialE_eval vpTblEnc (O' := OO) L Δ (esG (.fst .v3)) _
            ρ₃ es.g ⟨P.other, t', i'⟩ hBound.trans_le hBound.comp_le rfl hPos
        rw [hTriv]
        by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, eval_bind]
          have hSt3 : (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO)))))
              (.fst (.snd .v3))).eval ρ₃ = vpTblEnc (es.g.st P) :=
            pGet_eval (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)) ρ₃
              (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
          have hCom := commitEC_eval hsEncFn HBounded hkC hk hHk L
            (esSetH (.fst .v3) (.snd .v2)) (esG (.fst .v3)) (.fst (.snd .v3))
            (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0)
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₃ { es with h := h' } es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ hHB' hBound
            hes3' rfl rfl hSt3 rfl hPos
          rw [hCom, StateT.run_bind, bind_map_left, map_bind]
          refine bind_congr fun ⟨cmRes, es''⟩ => ?_
          rcases cmRes with _ | s_acc
          · simp [ρ₃, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
          · simp only [Prod.map, Option.map_some,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
            set ρ₄ := Env.cons
              (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
              (cGsEnc vpTblEnc s_acc)
              (Env.cons
                (t := .prod
                   (.opt (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
                   (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
                (some (cGsEnc vpTblEnc s_acc), esEnc vpTblEnc hsEncFn es'') ρ₃)
            change (Comp.ret _).eval ρ₄ = _
            have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO) (.snd .v1) .v0
              ρ₄ es'' s_acc rfl rfl
            simp only [eval_ret, pair_eval, some_eval, inr_eval, hSetG]
            rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval, some_eval]
          have hInjFull : (cfgC.injectFullE (.fst (.snd .v0))).eval ρ₃ = cfg.injectFull t' :=
            hCfg.injectFull_eq (.fst (.snd .v0)) ρ₃
          have hSetWin := cGsSetWin_eval vpTblEnc (O' := OO)
            (esG (.fst .v3)) (.bool true) ρ₃ es.g rfl
          have hg3 : (Expr.ite (cfgC.injectFullE (.fst (.snd .v0)))
              (cGsSetWin (esG (.fst .v3)) (.bool true)) (esG (.fst .v3))).eval ρ₃ =
              cGsEnc vpTblEnc (if cfg.injectFull t' then { es.g with win := true } else es.g) := by
            rw [ite_eval, hInjFull, hSetWin]
            by_cases hf : cfg.injectFull t' <;> simp [hf, ρ₃, ρ₁, esG, esEnc, Expr.eval, Expr.v3]
          have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO)
            (esSetH (.fst .v3) (.snd .v2))
            (.ite (cfgC.injectFullE (.fst (.snd .v0)))
              (cGsSetWin (esG (.fst .v3)) (.bool true)) (esG (.fst .v3)))
            ρ₃ { es with h := h' }
            (if cfg.injectFull t' then { es.g with win := true } else es.g) hes3' hg3
          rw [hSetG]
          by_cases hf : cfg.injectFull t' <;>
            simp [hf, StateT.run_modify, StateT.run_pure, smRrEnc, Expr.eval]

theorem corrEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L : ℕ) (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (pE : Expr OO Γ' .bool)
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hp : pE.eval ρ = partyEnc P) :
    (corrEC hkC L π esE pE).eval ρ =
      Prod.map (Option.map ckaPsEnc) (esEnc vpTblEnc hsEncFn) <$>
        (corrE hk π P).run es := by
  unfold corrEC corrE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE pE).eval ρ = (esEnc vpTblEnc hsEncFn es, partyEnc P) := by
    simp [Expr.eval, hes, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) .bool)
    (esEnc vpTblEnc hsEncFn es, partyEnc P) ρ
  rw [eval_ite]
  have hCorrOk : (cCorrAllowedE L (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
      es.g.corrAllowed P :=
    cCorrAllowedE_eval vpTblEnc (O' := OO) L (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
      hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl
  have hRefuse : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (orE (cGsWin (esG (.fst .v0)))
        (.not (cCorrAllowedE L (esG (.fst .v0)) (.snd .v0))))).eval ρ₁ =
      (es.abort || es.g.win || !(es.g.corrAllowed P)) := by
    simp only [orE_eval, not_eval, hCorrOk]
    simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    have hAfter : (cAfterCorrE L (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        cGsEnc vpTblEnc (es.g.afterCorr P) :=
      cAfterCorrE_eval vpTblEnc (O' := OO) L (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
        hBound.trans_le hBound.comp_u rfl rfl
    have hAfterLeaks : (es.g.afterCorr P).leaks.length ≤ L := afterCorr_leaks_le hBound P
    have hLeakDoom : (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0))).eval ρ₁ =
        π.leakDoom es.g (es.g.afterCorr P) :=
      leakDoomE_eval vpTblEnc (O' := OO) L π (esG (.fst .v0))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0)) ρ₁ es.g (es.g.afterCorr P)
        hAfterLeaks rfl hAfter
    have hCorrDoom : (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        π.corrDoom es.g P :=
      corrDoomE_eval vpTblEnc (O' := OO) π (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P rfl rfl
    have hDoom : (orE (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0)))
        (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0))).eval ρ₁ =
        (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) := by
      rw [orE_eval, hLeakDoom, hCorrDoom]
    rw [hDoom]
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, eval_ret, pair_eval,
        StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure, Prod.map]
      have hSetAb := esSetAbort_eval vpTblEnc hsEncFn (O' := OO) (.fst .v0) (.bool true) ρ₁ es rfl
      simp only [Expr.eval] at hSetAb ⊢
      rw [hSetAb]; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, eval_bind]
      have hStP : (pGet (cGsSt (esG (.fst (Expr.v0 (O := OO))))) (.snd .v0)).eval ρ₁ =
          vpTblEnc (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v0))) (.snd .v0) ρ₁
          (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
      have hRev := hHk.reveal_eval (esH (.fst .v0)) (esG (.fst .v0)) (.snd .v0)
        (pGet (cGsSt (esG (.fst .v0))) (.snd .v0)) ρ₁ es.h es.g P (es.g.st P) hHB
        rfl rfl rfl hStP
      rw [hRev, bind_map_left, run_liftH_bind, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | st
      · simp [ρ₁, Comp.eval, StateT.run_modify,
          Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v1]
      · simp only [Prod.map, Option.map_some]
        set ρ₂ := Env.cons (t := psTy) (ckaPsEnc st)
          (Env.cons (t := .prod (.opt psTy) hsT) (some (ckaPsEnc st), hsEncFn h') ρ₁)
        change (Comp.ret _).eval ρ₂ = _
        have hAfter2 : (cAfterCorrE L (esG (.fst (Expr.v2 (O := OO)))) (.snd .v2)).eval ρ₂ =
            cGsEnc vpTblEnc (es.g.afterCorr P) :=
          cAfterCorrE_eval vpTblEnc (O' := OO) L (esG (.fst .v2)) (.snd .v2) ρ₂ es.g P
            hBound.trans_le hBound.comp_u rfl rfl
        simp only [eval_ret, esMk, pair_eval, some_eval, hAfter2]
        rfl

/-- Step-level evaluation agreement between decoded `implEC` and `Engine.implE`. -/
theorem rdec_implEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (q : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hq : qE.eval ρ = (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (implEC hkC L Δ qep maxSkip cfgC π esE qE).eval ρ) =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (implE hk Δ qep maxSkip cfg π (.inr q)).run es := by
  unfold implEC implE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE qE).eval ρ =
      (esEnc vpTblEnc hsEncFn es,
       (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hes, hq]
  rw [h0]; clear h0
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [transmitEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep π
          _ _ _ es P m r hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [challEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg π
          _ _ _ es P m₀ m₁ r hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [deliverEC_eval hsEncFn HBounded hkC hk hHk L maxSkip cfgC cfg hCfg heqT heqM heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [injectEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [corrEC_eval hsEncFn HBounded hkC hk hHk L π
          _ _ _ es P hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | st
    · rfl
    · simp [Prod.map]

theorem privOutC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq M]
    (hsEncFn : HS → hsT.denote)
    (L Δ : ℕ) (π : Policy)
    (drawBit : ∀ {Γ''}, Comp OO I' Γ'' .bool)
    (hDrawBit : ∀ {Γ''} (ρ' : Env Γ''), (drawBit (Γ'' := Γ'')).eval ρ' =
      (liftM ($ᵗ Bool : ProbComp Bool) : TComp TSpec Bool))
    {Γ'} (bE b'E : Expr OO Γ' .bool)
    (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (ρ : Env Γ')
    (b b' : Bool)
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (hLeaks : es.g.leaks.length ≤ L)
    (hb : bE.eval ρ = b) (hb' : b'E.eval ρ = b')
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es) :
    (privOutC L Δ π drawBit bE b'E esE).eval ρ = privOut Δ π b b' es := by
  unfold privOutC privOut
  rw [eval_ite]
  have hPV : (privValidE L Δ π esE).eval ρ = privValid Δ π es :=
    privValidE_eval vpTblEnc hsEncFn (O' := OO) L Δ π esE ρ es hLeaks hes
  rw [hPV]
  unfold privValid
  by_cases hpv : (!es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL)
  · simp [hpv, eval_ret, boolEq_eval, hb, hb']
  · simp [hpv, hDrawBit]

/-! ### `SMEngineInv` preservation -/

theorem SMEngineInv.of_lists_eq {St Msg C : Type} {L B q : ℕ} {s s' : GameState St Msg C}
    (h : SMEngineInv L B q s) (hTr : s'.trans = s.trans) (hCh : s'.chall = s.chall)
    (hLk : s'.leaks = s.leaks) (hCr : s'.corrs = s.corrs) (hCp : s'.comp = s.comp) :
    SMEngineInv L B q s' := by
  rcases h with ⟨h1, h2, h3, h4, ⟨U, hU, hTrU, hCpU⟩, h6, h7⟩
  rw [← hTr] at h1; rw [← hCh] at h2; rw [← hLk] at h3; rw [← hCr] at h4
  exact ⟨h1, h2, h3, h4, ⟨U, hU, hTr ▸ hTrU, hCp ▸ hCpU⟩, h6, h7⟩

theorem SMEngineInv.epMgmt_record {St Msg C : Type} {L B q Δ qep : ℕ}
    {s s₁ : GameState St Msg C} {P : Party} {bad : Bool}
    (hInv : SMEngineInv L B (q + 1) s)
    (hep : s.epMgmt Δ qep P bad = some s₁)
    (st' : St) (r : Record Msg C) (isChall : Bool) :
    SMEngineInv L B q (s₁.record Δ P st' r isChall) := by
  obtain ⟨hTr, hCh, hCp, hCr⟩ := epMgmt_lists_eq hep
  have hLk := epMgmt_leaks_le_succ hep
  obtain ⟨U, hU, hTrU, hCpU⟩ := hInv.comp_u
  have hChallLen : (s₁.record Δ P st' r isChall).chall.length ≤ s.chall.length + 1 := by
    cases isChall <;> simp [GameState.record, hCh]
  refine ⟨?_, ?_, ?_, ?_, ?_, hInv.b_succ_le, hInv.bb_le⟩
  · simp only [GameState.record, List.length_cons, hTr]
    have := hInv.trans_le; omega
  · have := hInv.chall_le; omega
  · simp only [GameState.record]
    have := hInv.leaks_le; omega
  · simp only [GameState.record, hCr]
    have := hInv.corrs_le; omega
  · refine ⟨r.pos :: U, by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro r' hr'
      simp only [GameState.record, hTr, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hTrU r' hr')
    · intro p hp
      simp only [GameState.record, hCp] at hp
      split_ifs at hp with hsafe
      · exact List.mem_cons_of_mem _ (hCpU p hp)
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hCpU p hp)

theorem SMEngineInv.accept {St Msg C : Type} {L B q : ℕ} {s : GameState St Msg C}
    (hInv : SMEngineInv L B q s) (P : Party) (st' : St) (pos : Pos) :
    SMEngineInv L B q (s.accept P st' pos) where
  trans_le := by
    have h1 : (s.accept P st' pos).trans.length ≤ s.trans.length := List.length_filter_le _ _
    have := hInv.trans_le; omega
  chall_le := by
    have h1 : (s.accept P st' pos).chall.length ≤ s.chall.length := List.length_filter_le _ _
    have := hInv.chall_le; omega
  leaks_le := hInv.leaks_le
  corrs_le := hInv.corrs_le
  comp_u := by
    obtain ⟨U, hU, hTrU, hCpU⟩ := hInv.comp_u
    refine ⟨U, hU, ?_, ?_⟩
    · intro r hr
      exact hTrU r (List.mem_of_mem_filter hr)
    · intro p hp
      exact hCpU p (List.mem_of_mem_filter hp)
  b_succ_le := hInv.b_succ_le
  bb_le := hInv.bb_le

theorem SMEngineInv.afterCorr {St Msg C : Type} {L B q : ℕ} {s : GameState St Msg C}
    (hInv : SMEngineInv L B (q + 1) s) (P : Party) :
    SMEngineInv L B q (s.afterCorr P) := by
  obtain ⟨U, hU, hTrU, hCpU⟩ := hInv.comp_u
  refine ⟨?_, ?_, ?_, ?_, ?_, hInv.b_succ_le, hInv.bb_le⟩
  · simp only [GameState.afterCorr, GameState.leak]; have := hInv.trans_le; omega
  · simp only [GameState.afterCorr, GameState.leak]; have := hInv.chall_le; omega
  · simp only [GameState.afterCorr, GameState.leak, List.length_cons]
    have := hInv.leaks_le; omega
  · simp only [GameState.afterCorr, List.length_cons]
    have := hInv.corrs_le; omega
  · refine ⟨U, by omega, ?_, ?_⟩
    · intro r hr
      exact hTrU r hr
    · intro p hp
      simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨r, hr, rfl⟩ | hp
      · exact hTrU r (List.mem_of_mem_filter hr)
      · exact hCpU p hp

theorem commitE_inv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q : ℕ}
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (s : Ctx γV T σV ssV rsV M E) (P : Party)
    (old new : VP γV T σV ssV rsV) (pos : Pos)
    (hEs : SMEngineInv L B q es.g) (hS : SMEngineInv L B q s) :
    ∀ res ∈ support ((commitE hk s P old new pos).run es),
      SMEngineInv L B q res.2.g ∧
      (∀ s₁, res.1 = some s₁ → SMEngineInv L B q s₁) := by
  intro ⟨cmRes, es'⟩ hmem
  unfold commitE abortE at hmem
  rw [run_liftH_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨ans, h'⟩, _, hmem⟩ := hmem
  rcases ans with _ | new'
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hEs, fun _ h => by cases h⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    refine ⟨hEs, fun s₁ hs₁ => ?_⟩
    cases hs₁
    exact (hS.accept P new pos).of_lists_eq rfl rfl rfl rfl rfl

theorem transmitE_inv [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep : ℕ} (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × M × Option CCoins)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((transmitE hk Δ qep π arg).run es), SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, m, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold transmitE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact hInv.epMgmt_record hep st' _ false

theorem challE_inv [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × M × M × Option CCoins)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((challE hk Δ qep cfg π arg).run es), SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, m₀, m₁, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold challE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
          rw [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, _, hmem⟩ := hmem
          rcases vsRes with _ | ⟨st', c⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInvQ
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact hInv.epMgmt_record hep st' _ true

theorem deliverE_inv [DecidableEq T] [DecidableEq M] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((deliverE hk maxSkip cfg arg).run es), SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ.of_lists_eq rfl rfl rfl rfl rfl
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
        have ⟨hEs'', hAcc⟩ := commitE_inv hk { es with h := h' } es.g P (es.g.st P) st' r.pos
          hInvQ hInvQ (cmRes, es'') hcm
        rcases cmRes with _ | s₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hEs''
        · have hs₁ : SMEngineInv L B q s₁ := hAcc s₁ rfl
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          split_ifs
          · exact hs₁.of_lists_eq rfl rfl rfl rfl rfl
          · exact hs₁

theorem injectE_inv [DecidableEq T] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((injectE hk Δ qep cfg arg).run es), SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold injectE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have ⟨hEs'', hAcc⟩ := commitE_inv hk { es with h := h' } es.g P (es.g.st P) st'
            ⟨P.other, t', i'⟩ hInvQ hInvQ (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hEs''
          · have hs₁ : SMEngineInv L B q s₁ := hAcc s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hs₁
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hf : cfg.injectFull t'
          · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInvQ.of_lists_eq rfl rfl rfl rfl rfl
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInvQ

theorem corrE_inv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q : ℕ} (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((corrE hk π P).run es), SMEngineInv L B q res.2.g := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold corrE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact hInv.afterCorr P

theorem implE_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((implE hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_inv hk π es arg hInv
  · exact challE_inv hk cfg π es arg hInv
  · exact deliverE_inv hk cfg es arg hInv
  · exact injectE_inv hk cfg es arg hInv
  · exact corrE_inv hk π es P hInv

/-! ### Receiver-state reachability (`RSReach` and `SMVRInv`) -/

/-- Reachability bound on `FSAEAD.fromAEADPRG` receiver states after at most `k` `receive` calls. -/
def RSReach {CK MK : Type} (maxSkip k : ℕ) (v : FSAEAD.RatchetReceiverState CK MK) : Prop :=
  v.lastIndex ≤ k * (maxSkip + 1) ∧ ∀ kv ∈ v.skippedKeys, kv.1 ≤ v.lastIndex

theorem RSReach.init {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (k : CK) :
    RSReach maxSkip 0 ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver k) :=
  ⟨by simp [FSAEAD.fromAEADPRG], by simp [FSAEAD.fromAEADPRG]⟩

theorem RSReach.mono {CK MK : Type} {maxSkip k k' : ℕ}
    {v : FSAEAD.RatchetReceiverState CK MK}
    (hk : k ≤ k') (h : RSReach maxSkip k v) : RSReach maxSkip k' v :=
  ⟨h.1.trans (Nat.mul_le_mul_right _ hk), h.2⟩

theorem skipKeys_mem {CK MK : Type} (G : ℕ → PRGScheme CK (CK × MK)) :
    ∀ (n : ℕ) (w : CK) (p : ℕ) (acc : List (ℕ × MK)) {kv : ℕ × MK},
      kv ∈ (FSAEAD.skipKeys G n w p acc).2 → kv ∈ acc ∨ kv.1 ≤ p + n
  | 0, _, _, _, _, h => Or.inl h
  | n + 1, w, p, acc, kv, h => by
    rcases skipKeys_mem G n ((G p).gen w).1 (p + 1)
      ((p + 1, ((G p).gen w).2) :: acc) h with h' | h'
    · rcases List.mem_cons.mp h' with rfl | hacc
      · exact Or.inr (by omega)
      · exact Or.inl hacc
    · exact Or.inr (by omega)

theorem lookup_eq_some_mem {MK : Type} :
    ∀ (sk : List (ℕ × MK)) {i : ℕ} {k : MK}, sk.lookup i = some k → (i, k) ∈ sk
  | [], _, _, h => by cases h
  | (j, v) :: sk, i, k, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      have hij : i = j := beq_iff_eq.mp heq
      subst hij
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_eq_some_mem sk h)

theorem RSReach.receive {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip k : ℕ)
    {v v' : FSAEAD.RatchetReceiverState CK MK} {a : AD} {c : ℕ × C} {i : ℕ} {m : M}
    (hv : RSReach maxSkip k v)
    (hrec : (FSAEAD.fromAEADPRG ae G maxSkip).receive v a c = some (v', i, m)) :
    i ≤ (k + 1) * (maxSkip + 1) ∧ RSReach maxSkip (k + 1) v' := by
  rcases c with ⟨idx, e⟩
  dsimp only [FSAEAD.fromAEADPRG] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ maxSkip < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hdec : ae.dec ((G (idx - 1)).gen
        (FSAEAD.skipKeys G (idx - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys).1).2
        (idx, a) e with _ | m'
    · simp [hdec] at hrec
    · simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      have h1 := hv.1
      have hmul : (k + 1) * (maxSkip + 1) = k * (maxSkip + 1) + (maxSkip + 1) :=
        Nat.succ_mul k (maxSkip + 1)
      have hidx : idx ≤ (k + 1) * (maxSkip + 1) := by omega
      refine ⟨hidx, hidx, fun kv hkv => ?_⟩
      change kv ∈
        (FSAEAD.skipKeys G (idx - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys).2 at hkv
      change kv.1 ≤ idx
      rcases skipKeys_mem G (idx - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys hkv
        with hacc | hstep
      · have := hv.2 kv hacc; omega
      · omega
  · rw [hlk] at hrec
    rcases hdec : ae.dec key (idx, a) e with _ | m'
    · simp [hdec] at hrec
    · simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      have hmem := lookup_eq_some_mem v.skippedKeys hlk
      have hidx_le : idx ≤ v.lastIndex := hv.2 (idx, key) hmem
      have h1 := hv.1
      have hle : k * (maxSkip + 1) ≤ (k + 1) * (maxSkip + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_succ k)
      have hidx2 : idx ≤ (k + 1) * (maxSkip + 1) := by omega
      have hlast2 : v.lastIndex ≤ (k + 1) * (maxSkip + 1) := by omega
      refine ⟨hidx2, hlast2, fun kv hkv => ?_⟩
      change kv ∈ v.skippedKeys.filter (·.1 != idx) at hkv
      change kv.1 ≤ v.lastIndex
      exact hv.2 kv (List.mem_of_mem_filter hkv)

/-- Step-indexed receiver-state invariant for `Engine.Hooks`. -/
structure HooksVRInv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (VROkStep : ℕ → rsV → Prop)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV) : Prop where
  mono : ∀ {k k' : ℕ} {v : rsV}, k ≤ k' → VROkStep k v → VROkStep k' v
  startRecv_step : ∀ ctx P t γ σ Tn (h : HS) res,
    res ∈ support ((hk.startRecv ctx P t γ σ Tn).run h) →
    ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROkStep 0 rs
  fsRecv_step : ∀ {k : ℕ} ctx P t (rs : rsV) hdr e rec (h : HS) res,
    VROkStep k rs →
    res ∈ support ((hk.fsRecv ctx P t rs hdr e rec).run h) →
    ∀ v' i' m', res.1 = some (some (v', i', m')) → VROkStep (k + 1) v'
  commit_vR : ∀ ctx P old new (h : HS) res,
    res ∈ support ((hk.commit ctx P old new).run h) →
    ∀ new', res.1 = some new' → new'.vR = new.vR

/-- Virtual-party receiver-table invariant with `q` remaining adversary queries out of `B`. -/
def SMVRInv {γV σV ssV rsV : Type}
    (VROkStep : ℕ → rsV → Prop) (B q : ℕ)
    (s : Ctx γV T σV ssV rsV M E) : Prop :=
  ∀ (P : Party) (t : ℕ) (v : rsV), (s.st P).vR t = some v → VROkStep (B - q) v

theorem SMVRInv.mono {γV σV ssV rsV : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hMono : ∀ {k k' : ℕ} {v : rsV}, k ≤ k' → VROkStep k v → VROkStep k' v)
    {B q q' : ℕ} {s : Ctx γV T σV ssV rsV M E}
    (hq : q' ≤ q) (h : SMVRInv VROkStep B q s) : SMVRInv VROkStep B q' s :=
  fun P t v hv => hMono (by omega) (h P t v hv)

theorem epMgmt_st_eq {St Msg C : Type} {Δ qep : ℕ} {s s₁ : GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.st = s.st := by
  unfold GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, GameState.leak]
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at h
    · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl

theorem vSend_vR_eq [Inhabited E] {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : HS) :
    ∀ res ∈ support ((vSend hk ctx P s m pair r).run h),
      ∀ st' c, res.1 = some (st', c) → st'.vR = s.vR := by
  intro ⟨vsRes, h'⟩ hmem st' c hEq
  subst hEq
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hs₁_vR : ∀ s₁, s₁? = some s₁ → s₁.vR = s.vR := by
    unfold vSendStep1 at hmem1
    split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, _, hmem1⟩ := hmem1
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩; intro s₁ hs₁; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩; intro s₁ hs₁; cases hs₁; rfl
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨rfl, rfl⟩; intro s₁ hs₁; cases hs₁; rfl
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨h, _⟩; cases h
  · have hvR1 := hs₁_vR s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem2
      rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩; exact hvR1
    · simp only [hvS, StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, _, hmem2⟩ := hmem2
      rcases fsRes with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨h, _⟩; cases h
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem2
        rcases hmem2 with ⟨⟨rfl, rfl⟩, rfl⟩; exact hvR1

theorem vRecv_vrInv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {k : ℕ}
    (ctx : Ctx γV T σV ssV rsV M E) (P : Party)
    (s : VP γV T σV ssV rsV) (c : Header T × E)
    (rec : Option (Record M (Header T × E))) (h : HS)
    (hVR : ∀ t v, s.vR t = some v → VROkStep k v) :
    ∀ res ∈ support ((vRecv hk ctx P s c rec).run h),
      ∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        ∀ t v, st'.vR t = some v → VROkStep (k + 1) v := by
  intro ⟨vrRes, h'⟩ hmem st' t' i' m' hEq t v hv
  subst hEq
  rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨h, _⟩; cases h
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hs₁_vR : ∀ s₁, s₁? = some (some s₁) → ∀ t v, s₁.vR t = some v → VROkStep k v := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1
        rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨rfl, rfl⟩; intro _ h; cases h
        · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩; intro _ h; cases h
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩; intro _ h; cases h
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            intro s₁ hs₁ t₀ v₀ hv₀
            cases hs₁
            by_cases ht₀ : t₀ = s.tcur + 1
            · subst ht₀
              simp only [Function.update_self, Option.some.injEq] at hv₀
              subst hv₀
              exact hVRHk.mono (Nat.zero_le k)
                (hVRHk.startRecv_step ctx P (s.tcur + 1) s.γ s.root Tn h
                  (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl)
            · simp only [Function.update_of_ne ht₀] at hv₀
              exact hVR t₀ v₀ hv₀
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩; intro s₁ hs₁; cases hs₁; exact hVR
    rcases s₁? with _ | (_ | s₁)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨h, _⟩; cases h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hmem2
      rcases hmem2 with ⟨h, _⟩; cases h
    · have hVR₁ := hs₁_vR s₁ rfl
      rcases hvRc : s₁.vR c.1.1 with _ | v₀
      · simp only [hvRc, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨h, _⟩; cases h
      · simp only [hvRc, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
        rcases fsRes with _ | _ | ⟨v', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem2
          rcases hmem2 with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem2
          rcases hmem2 with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
          by_cases htc : t = c.1.1
          · subst htc
            simp only [Function.update_self, Option.some.injEq] at hv
            subst hv
            exact hVRHk.fsRecv_step ctx P c.1.1 v₀ c.1 c.2 rec h₁
              (some (some (v', i', m')), h') (hVR₁ c.1.1 v₀ hvRc) hfs v' i' m' rfl
          · simp only [Function.update_of_ne htc] at hv
            exact hVRHk.mono (Nat.le_succ k) (hVR₁ t v hv)

theorem commitE_vrInv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {B q : ℕ}
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (s : Ctx γV T σV ssV rsV M E) (P : Party)
    (old new : VP γV T σV ssV rsV) (pos : Pos)
    (hEs : SMVRInv VROkStep B q es.g) (hS : SMVRInv VROkStep B q s)
    (hNew : ∀ t v, new.vR t = some v → VROkStep (B - q) v) :
    ∀ res ∈ support ((commitE hk s P old new pos).run es),
      SMVRInv VROkStep B q res.2.g ∧
      (∀ s₁, res.1 = some s₁ → SMVRInv VROkStep B q s₁) := by
  intro ⟨cmRes, es'⟩ hmem
  unfold commitE abortE at hmem
  rw [run_liftH_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨ans, h'⟩, hcm, hmem⟩ := hmem
  rcases ans with _ | new'
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hEs, fun _ h => by cases h⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    have hvR := hVRHk.commit_vR (s.accept P new pos) P old new es.h (some new', h') hcm new' rfl
    refine ⟨hEs, fun s₁ hs₁ Q t v hv => ?_⟩
    cases hs₁
    by_cases hQP : Q = P
    · subst hQP
      simp only [Function.update_self, hvR] at hv
      exact hNew t v hv
    · simp only [Function.update_of_ne hQP, GameState.accept] at hv
      exact hS Q t v hv

theorem implE_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((implE hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  have hBq : B - (q + 1) + 1 = B - q := by
    have := hInv.trans_le; omega
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((transmitE hk Δ qep π (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hep] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
            run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          rcases vsRes with _ | ⟨st', ct⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            have hst_eq := epMgmt_st_eq hep
            have hvR_eq := vSend_vR_eq hk s₁ P (s₁.st P) m none r es.h (some (st', ct), h') hvs
              st' ct rfl
            intro Q t₀ v₀ hv₀
            simp only [GameState.record] at hv₀
            by_cases hQP : Q = P
            · subst hQP
              simp only [Function.update_self, hvR_eq, hst_eq] at hv₀
              exact hVRQ Q t₀ v₀ hv₀
            · simp only [Function.update_of_ne hQP, hst_eq] at hv₀
              exact hVRQ Q t₀ v₀ hv₀
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((challE hk Δ qep cfg π (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
              run_liftH_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hVRQ
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              have hst_eq := epMgmt_st_eq hep
              have hvR_eq := vSend_vR_eq hk s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h
                (some (st', ct), h') hvs st' ct rfl
              intro Q t₀ v₀ hv₀
              simp only [GameState.record] at hv₀
              by_cases hQP : Q = P
              · subst hQP
                simp only [Function.update_self, hvR_eq, hst_eq] at hv₀
                exact hVRQ Q t₀ v₀ hv₀
              · simp only [Function.update_of_ne hQP, hst_eq] at hv₀
                exact hVRQ Q t₀ v₀ hv₀
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((deliverE hk maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
          · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have hSt'VR : ∀ t₀ v₀, st'.vR t₀ = some v₀ → VROkStep (B - q) v₀ := by
            rw [← hBq]
            exact vRecv_vrInv hk hVRHk es.g P (es.g.st P) c (some r) es.h (hVR P)
              (some (some (st', t', i', m')), h') hvr st' t' i' m' rfl
          have ⟨hEs'', hAcc⟩ := commitE_vrInv hk hVRHk { es with h := h' } es.g P (es.g.st P)
            st' r.pos hVRQ hVRQ hSt'VR (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hEs''
          · have hs₁ : SMVRInv VROkStep B q s₁ := hAcc s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            split_ifs <;> exact hs₁
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((injectE hk Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte,
        run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
            have hSt'VR : ∀ t₀ v₀, st'.vR t₀ = some v₀ → VROkStep (B - q) v₀ := by
              rw [← hBq]
              exact vRecv_vrInv hk hVRHk es.g P (es.g.st P) c none es.h (hVR P)
                (some (some (st', t', i', m')), h') hvr st' t' i' m' rfl
            have ⟨hEs'', hAcc⟩ := commitE_vrInv hk hVRHk { es with h := h' } es.g P (es.g.st P)
              st' ⟨P.other, t', i'⟩ hVRQ hVRQ hSt'VR (cmRes, es'') hcm
            rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hEs''
            · have hs₁ : SMVRInv VROkStep B q s₁ := hAcc s₁ rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hs₁
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hf : cfg.injectFull t'
            · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hVRQ
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((corrE hk π P).run es) at hmem
    unfold corrE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
        rcases revRes with _ | st
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ

end HandlerEval

end CryptoGames.SM.Engine

