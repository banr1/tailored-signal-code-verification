/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperTMinusFS
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperCKA
public import Computational.Proofs.ReductionDsl.SM.DeliverForgeShifted
import ProofLib.BV.WidthNorm
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed Shifted Paper `DeliverForge` Reductions

Defines the shifted paper-semantics `DeliverForge` engine and reductions (`redCKAAuthDFShiftedPaper`,
`redPRNGAuthDFShiftedPaper`, `redFSAuthDFShiftedPaper`, and their `Dir2` specializations) together
with their `CostedReduction` counterparts and evaluation bridges.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Construction.DeliverForge

def implEDFShiftedPaperGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy) :
    QueryImpl (unifSpec + SM.specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  let i₀ : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS) := coinsE
  let i₁ : QueryImpl (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (transmitE hk Δ qep π) (challE hk Δ qep cfg π))
      (deliverE hk maxSkip cfg)) (injectEGen b1 hk Δ qep tStar cfg)) (corrEShiftedPaper l hk π)
  let i₂ : QueryImpl ((Party × (Header T × E) × (Header T × E)) →ₒ Option (RecvResult M))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
    deliverForgeEGen b1 hk Δ qep tStar cfg
  HAdd.hAdd i₀ (HAdd.hAdd i₁ i₂)

def engRunDFShiftedPaperGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip tStar : ℕ) (cfg : SM.Config M) (π : Policy)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec (Option (Bool × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)) := do
  let (vpOpt, h₁) ← init.run h₀
  match vpOpt with
  | none => return none
  | some (vpA, vpB) =>
    let g₀ : SM.GameState (VP Γv T Sv SSv RSv) M (Header T × E) :=
      { st := fun | .A => vpA | .B => vpB, b := b }
    let es₀ : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS :=
      { g := g₀, h := h₁, abort := false }
    let res ← (simulateQ (implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π) A).run es₀
    return some res

/-- Shifted paper authenticity simulator at `Δ = 2 + Δcka` parameterized by `b1 : Bool`. -/
def authSimDFShiftedPaperGen {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {K Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (l : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    TComp tspec Bool := do
  let π : Policy := ⟨true, tL, tStar⟩
  let r ← engRunDFShiftedPaperGen b1 l hk (2 + Δcka) qep fs.maxSkip tStar (SM.Config.auth tStar) π
    init h₀ false A
  match r with
  | none => return false
  | some (_, es) => return authOut (2 + Δcka) π es

@[simp] theorem authSimDFShiftedPaperGen_false {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {K Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    authSimDFShiftedPaperGen false l fs Δcka qep hk init h₀ tL tStar A =
      authSimDFShiftedPaper l fs Δcka qep hk init h₀ tL tStar A := by
  dsimp only [authSimDFShiftedPaperGen, authSimDFShiftedPaper]
  congr 1; funext r; rcases r with _ | ⟨_, es⟩ <;> rfl

@[simp] theorem authSimDFShiftedPaperGen_true {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {K Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) (qep : ℕ)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (tL : Option ℕ) (tStar : ℕ) (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    authSimDFShiftedPaperGen true l fs 0 qep hk init h₀ tL tStar A =
      authSimDFShiftedDir2Paper l fs qep hk init h₀ tL tStar A := by
  dsimp only [authSimDFShiftedPaperGen, authSimDFShiftedDir2Paper]
  congr 1; funext r; rcases r with _ | ⟨_, es⟩ <;> rfl

/-- Shifted paper PRF-PRNG reduction parameterized by `authH : Bool`. -/
def redPRNGAuthDFShiftedPaperGen
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ) (authH : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from
  authSimDFShiftedPaperGen (!authH) l fs Δcka qep
    (hooksPRNG cka prng fs ⟨authH, some (l - 1), tStar⟩)
    (initPRNG cka prng fs lam ⟨authH, some (l - 1), tStar⟩) {} (some (l - 1)) tStar A

@[simp] theorem redPRNGAuthDFShiftedPaperGen_true
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    redPRNGAuthDFShiftedPaperGen cka prng fs lam Δcka qep l tStar true A =
      redPRNGAuthDFShiftedPaper cka prng fs lam Δcka qep l tStar A := by
  unfold redPRNGAuthDFShiftedPaperGen redPRNGAuthDFShiftedPaper
  exact authSimDFShiftedPaperGen_false l fs Δcka qep _ _ _ _ tStar A

@[simp] theorem redPRNGAuthDFShiftedPaperGen_false
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    redPRNGAuthDFShiftedPaperGen cka prng fs lam 0 qep l tStar false A =
      redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep l tStar A := by
  unfold redPRNGAuthDFShiftedPaperGen redPRNGAuthDFShiftedDir2Paper
  exact authSimDFShiftedPaperGen_true l fs qep _ _ _ _ tStar A

/-- Shifted paper FS-AEAD reduction parameterized by `authH : Bool`. -/
def redFSAuthDFShiftedPaperGen
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l tStar : ℕ) (authH : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← engRunDFShiftedPaperGen (!authH) l
    (hooksFS cka prng fs Δcka ⟨authH, some (l - 1), tStar⟩ j)
    (2 + Δcka) qep fs.maxSkip tStar (SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩
    (initFS cka prng fs lam ⟨authH, some (l - 1), tStar⟩ j) {} false A
  sampleT Bool

@[simp] theorem redFSAuthDFShiftedPaperGen_true
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    redFSAuthDFShiftedPaperGen cka prng fs lam Δcka qep j l tStar true A =
      redFSAuthDFShiftedPaper cka prng fs lam Δcka qep j l tStar A := rfl

@[simp] theorem redFSAuthDFShiftedPaperGen_false
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep j l tStar : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    redFSAuthDFShiftedPaperGen cka prng fs lam 0 qep j l tStar false A =
      redFSAuthDFShiftedDir2Paper cka prng fs lam qep j l tStar A := rfl

end CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Engine

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

section ShiftedPaperHandlers

variable
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

def corrECShiftedPaper
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l : ℕ) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    Comp OO I' Γ'
      (.prod (.opt psTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0) ← return (es, p)
    let s0 := esG es0
    let refuse := orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE L s0 p0)))
    if refuse then
      return (none, es0)
    else
      let s1 := cAfterCorrShiftedE L l s0 p0
      if orE (leakDoomE L π s0 s1) (corrDoomE π s0 p0) then
        return (none, esSetAbort es0 true)
      else
        (optSt, h') ← hk.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match optSt with
        | none => return (none, esMk s0 h' true)
        | some st => return (some st, esMk s1 h' (esAbort es0))

def implECShiftedPaperGen
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (b1 : Bool) (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip tStar : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .transmit arg =>
      (r, es') ← transmitEC hk L Δ qep π es0 arg
      return (.inl (.inl (.inl (.inl r))), es')
    | .challenge arg =>
      (r, es') ← challEC hk L Δ qep cfg π es0 arg
      return (.inl (.inl (.inl (.inr r))), es')
    | .deliver arg =>
      (r, es') ← deliverEC hk L maxSkip cfg es0 arg
      return (.inl (.inl (.inr r)), es')
    | .inject arg =>
      (r, es') ← injectECGen b1 hk L Δ qep tStar cfg es0 arg
      return (.inl (.inr r), es')
    | .corrupt arg =>
      (r, es') ← corrECShiftedPaper hk L l π es0 arg
      return (.inr r, es')

def implECDFShiftedPaperGen
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (b1 : Bool) (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip tStar : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .inl qBase =>
      (r, es') ← implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar cfg π es0 qBase
      return (.inl r, es')
    | .inr qDf =>
      (r, es') ← deliverForgeECGen b1 hk L Δ qep tStar cfg es0 qDf
      return (.inr r, es')

theorem corrECShiftedPaper_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L l : ℕ) (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (pE : Expr OO Γ' .bool)
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hp : pE.eval ρ = partyEnc P) :
    (corrECShiftedPaper hkC L l π esE pE).eval ρ =
      Prod.map (Option.map ckaPsEnc) (esEnc vpTblEnc hsEncFn) <$>
        (corrEShiftedPaper l hk π P).run es := by
  unfold corrECShiftedPaper corrEShiftedPaper abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE pE).eval ρ = (esEnc vpTblEnc hsEncFn es, partyEnc P) := by
    simp [Expr.eval, hes, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) .bool)
    (esEnc vpTblEnc hsEncFn es, partyEnc P) ρ
  rw [eval_ite]
  have hCorrOk : (cCorrAllowedPaperE L (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
      es.g.corrAllowedPaper P :=
    cCorrAllowedPaperE_eval vpTblEnc (O' := OO) L (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
      hBound.chall_le rfl rfl
  have hRefuse : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (orE (cGsWin (esG (.fst .v0)))
        (.not (cCorrAllowedPaperE L (esG (.fst .v0)) (.snd .v0))))).eval ρ₁ =
      (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) := by
    simp only [orE_eval, not_eval, hCorrOk]
    simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    have hAfter : (cAfterCorrShiftedE L l (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        cGsEnc vpTblEnc (afterCorrShifted l es.g P) :=
      cAfterCorrShiftedE_eval vpTblEnc (O' := OO) L l (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
        hBound.trans_le hBound.comp_u rfl rfl
    have hAfterLeaks : (afterCorrShifted l es.g P).leaks.length ≤ L :=
      afterCorrShifted_leaks_le l hBound P
    have hLeakDoom : (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrShiftedE L l (esG (.fst .v0)) (.snd .v0))).eval ρ₁ =
        π.leakDoom es.g (afterCorrShifted l es.g P) :=
      leakDoomE_eval vpTblEnc (O' := OO) L π (esG (.fst .v0))
        (cAfterCorrShiftedE L l (esG (.fst .v0)) (.snd .v0)) ρ₁ es.g (afterCorrShifted l es.g P)
        hAfterLeaks rfl hAfter
    have hCorrDoom : (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        π.corrDoom es.g P :=
      corrDoomE_eval vpTblEnc (O' := OO) π (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P rfl rfl
    have hDoom : (orE (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrShiftedE L l (esG (.fst .v0)) (.snd .v0)))
        (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0))).eval ρ₁ =
        (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P) := by
      rw [orE_eval, hLeakDoom, hCorrDoom]
    rw [hDoom]
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
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
        have hAfter2 :
            (cAfterCorrShiftedE L l (esG (.fst (Expr.v2 (O := OO))))
              (.snd (Expr.v2 (O := OO)))).eval ρ₂ =
            cGsEnc vpTblEnc (afterCorrShifted l es.g P) :=
          cAfterCorrShiftedE_eval vpTblEnc (O' := OO) L l
            (esG (.fst (Expr.v2 (O := OO)))) (.snd (Expr.v2 (O := OO))) ρ₂ es.g P
            hBound.trans_le hBound.comp_u rfl rfl
        simp only [eval_ret, esMk, pair_eval, some_eval, hAfter2]
        rfl

theorem rdecDF_implECDFShiftedPaper_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L l Δ qep maxSkip tStar : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (implECDFShiftedPaperGen b1 hkC L l Δ qep maxSkip tStar cfgC π esE qE).eval ρ) =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π
          (.inr q)).run es := by
  unfold implECDFShiftedPaperGen
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE qE).eval ρ =
      (esEnc vpTblEnc hsEncFn es,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hes, hq]
  rw [h0]; clear h0
  rcases q with q | ⟨P, c, c'⟩
  · simp only [ckaSMCodecDF, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    unfold implECShiftedPaperGen DeliverForge.implEDFShiftedPaperGen
    rw [eval_bind_ret]
    rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · simp only [Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero, Env.get_cons_succ]
      rw [transmitEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep π
            _ _ _ es P m r hHB hBound rfl rfl]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨res, es'⟩ => rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero, Env.get_cons_succ]
      rw [challEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg π
            _ _ _ es P m₀ m₁ r hHB hBound rfl rfl]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨res, es'⟩ => rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero, Env.get_cons_succ]
      rw [deliverEC_eval hsEncFn HBounded hkC hk hHk L maxSkip cfgC cfg hCfg heqT heqM heqE
            _ _ _ es P c hHB hBound (hVR P) rfl rfl]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨res, es'⟩ => ?_; rcases res with _ | (_ | m') <;> rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero, Env.get_cons_succ]
      rw [injectECGen_eval b1 hsEncFn HBounded hkC hk hHk L Δ qep tStar cfgC cfg hCfg heqT heqE
            _ _ _ es P c hHB hBound (hVR P) rfl rfl]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨res, es'⟩ => ?_; rcases res with _ | (_ | m') <;> rfl
    · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      rw [corrECShiftedPaper_eval hsEncFn HBounded hkC hk hHk L l π
            _ _ _ es P hHB hBound rfl rfl]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨res, es'⟩ => ?_; rcases res with _ | st
      · rfl
      · simp [Prod.map]
  · simp only [ckaSMCodecDF, DeliverForge.implEDFShiftedPaperGen, Comp.eval, Expr.eval,
      Expr.v0, Expr.v1, Env.get_cons_zero]
    rw [deliverForgeECGen_eval b1 hsEncFn HBounded hkC hk hHk L Δ qep tStar cfgC cfg hCfg heqT heqE
          _ _ _ es P c c' hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl

theorem corrEShiftedPaper_inv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q : ℕ} (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((corrEShiftedPaper l hk π P).run es), SMEngineInv L B q res.2.g := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold corrEShiftedPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
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
        exact hInv.afterCorrShifted l P

theorem implEDFShiftedPaper_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip tStar : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support
      ((DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with ((t3 | arg) | P) | arg
  · exact implEDFShifted_inv hk l cfg π es (.inl (.inl (.inl t3))) hInv
  · exact injectEGen_inv b1 hk cfg es arg hInv
  · exact corrEShiftedPaper_inv hk l π es P hInv
  · exact deliverForgeEGen_inv b1 hk cfg es arg hInv

theorem corrEShiftedPaper_vrInv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {B q : ℕ} (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((corrEShiftedPaper l hk π P).run es), SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  intro ⟨out, es'⟩ hmem
  unfold corrEShiftedPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩; exact hVRQ)

theorem implEDFShiftedPaper_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip tStar : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support
      ((DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases t with ((t3 | arg) | P) | arg
  · exact implEDFShifted_vrInv hk hVRHk l cfg π es (.inl (.inl (.inl t3))) hInv hVR
  · exact injectEGen_vrInv b1 hk hVRHk cfg es arg hInv hVR
  · exact corrEShiftedPaper_vrInv hk hVRHk l π es P hVR
  · exact deliverForgeEGen_vrInv b1 hk hVRHk cfg es arg hInv hVR

theorem corrEShiftedPaper_b_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (l : ℕ) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party) :
    ∀ res ∈ support ((corrEShiftedPaper l hk π P).run es), res.2.g.b = es.g.b := by
  intro ⟨out, es'⟩ hmem
  unfold corrEShiftedPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩; rfl)

theorem implEDFShiftedPaper_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (b1 : Bool) (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip tStar : ℕ} (l : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support
      ((DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with ((t3 | arg) | P) | arg
  · exact implEDFShifted_b_eq hk l cfg π es (.inl (.inl (.inl t3)))
  · exact injectEGen_b_eq b1 hk cfg es arg
  · exact corrEShiftedPaper_b_eq hk l π es P
  · exact deliverForgeEGen_b_eq b1 hk cfg es arg

theorem simulateQ_implECDFShiftedPaper_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (hDefaultE : defaultE = default)
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B l Δ qep maxSkip tStar : ℕ)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost)
      (VROk := VROkStep B) hkC hk)
    (hVRHk : HooksVRInv VROkStep hk)
    (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    (hHbStep : ∀ (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
      (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
      HBounded es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support
        ((DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr t)).run es),
        HBounded res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
        HBounded es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 hkC L l Δ qep maxSkip tStar cfgC π .v0 .v1)) oa).run
          (esEnc vpTblEnc hsEncFn es) =
          (Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (simulateQ
              (DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π) oa).run
              es) ∧
        ∀ res ∈ support
          ((simulateQ
            (DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π) oa).run
            es),
          HBounded res.2.h ∧ SMEngineInv L B 0 res.2.g ∧ res.2.g.b = es.g.b := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hHB, hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 hkC L l Δ qep maxSkip tStar cfgC π .v0 .v1)) (.inl n)).run
            (esEnc vpTblEnc hsEncFn es) =
          (fun u => (u, esEnc vpTblEnc hsEncFn es)) <$>
            query (spec := unifSpec + TSpec) (.inl n) := by
        simp [handlerImpl, hU, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inl n)).run es =
          (fun u => (u, es)) <$> query (spec := unifSpec + TSpec) (.inl n) := by
        simp [DeliverForge.implEDFShiftedPaperGen, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hHB hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B v :=
        fun P t₀ v hv => hVRHk.mono (Nat.sub_le B (m + 1)) (hVR P t₀ v hv)
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 hkC L l Δ qep maxSkip tStar cfgC π .v0 .v1)) (.inr t)).run
            (esEnc vpTblEnc hsEncFn es) =
          Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (DeliverForge.implEDFShiftedPaperGen b1 l hk Δ qep maxSkip tStar cfg π (.inr t)).run
              es := by
        simp only [handlerImpl, StateT.run_mk,
          ← rdecDF_implECDFShiftedPaper_eval b1 hDefaultE hsEncFn HBounded hkC hk hHk L l Δ qep
            maxSkip tStar cfgC cfg hCfg heqT heqM heqE π .v0 .v1
            (.cons (esEnc vpTblEnc hsEncFn es)
              (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
            es t hHB hInv.toBoundedEngine hVRB rfl rfl,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem
        have hInv₁ := implEDFShiftedPaper_inv b1 hk l cfg π es t hInv (u, es₁) hmem
        have hVR₁ := implEDFShiftedPaper_vrInv b1 hk hVRHk l cfg π es t hInv hVR (u, es₁) hmem
        exact (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem₁
        have hInv₁ := implEDFShiftedPaper_inv b1 hk l cfg π es t hInv (u, es₁) hmem₁
        have hVR₁ := implEDFShiftedPaper_vrInv b1 hk hVRHk l cfg π es t hInv hVR (u, es₁) hmem₁
        have hb₁ := implEDFShiftedPaper_b_eq b1 hk l cfg π es t (u, es₁) hmem₁
        obtain ⟨hHB₂, hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).2 res hmem₂
        exact ⟨hHB₂, hInv₂, hb₂.trans hb₁⟩

end ShiftedPaperHandlers

end CryptoGames.SM.Engine
namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

variable
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

section HooksCKACDFShiftedPaper

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

def redCKAAuthDFShiftedPaperGenProg (L B Δcka qep maxSkip l tStarH tStar : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaShiftedEsTy
  init := rdsl [_] do
    es ← initCKAShiftedEStateC l false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFShiftedPaperGen (raw (decide (Δcka = 0))) (raw (hooksCKAShiftedC B l tStarH))
      L l (raw (2 + Δcka)) qep maxSkip tStar
      (raw (modeCfgEC OO ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st

abbrev redCKAAuthDFShiftedPaperProg (L B Δcka qep maxSkip l tStar : ℕ) :=
  redCKAAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip l tStar tStar

abbrev redCKAAuthDFShiftedDir2PaperProg (L B qep maxSkip l tStar : ℕ) :=
  redCKAAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B 0 qep maxSkip l 0 tStar

theorem redCKAAuthDFShiftedPaperProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L B B_q Δcka qep l tStarH tStar : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksCKAShifted cka prng fs l tStarH))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip l tStarH tStar).eval (fun _ => A) () =
      DeliverForge.authSimDFShiftedPaperGen (decide (Δcka = 0)) l fs Δcka qep
        (DeliverForge.hooksCKAShifted cka prng fs l tStarH)
        (DeliverForge.initCKAShifted cka prng fs lam l) {} (some (l - 1)) tStar A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKAShiftedC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B l tStarH hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initCKAShiftedEStateC_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    prng fs hPrngInit hPrngUp hFsInitS hFsInitR hSampKR
    l (Expr.bool (O := OO) false) (Env.cons (t := .unit) () .nil)
  unfold redCKAAuthDFShiftedPaperGenProg CostedReduction.eval CostedReduction.impl DeliverForge.authSimDFShiftedPaperGen
  dsimp only
  have hVp : @ckaVpEnc KC Γ CCoins T I KR RSt K SS RS M E =
      vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs) := rfl
  have hRun : DeliverForge.engRunDFShiftedPaperGen (decide (Δcka = 0)) l
      (DeliverForge.hooksCKAShifted cka prng fs l tStarH)
      (2 + Δcka) qep fs.maxSkip tStar (Config.auth tStar) ⟨true, some (l - 1), tStar⟩
      (DeliverForge.initCKAShifted cka prng fs lam l) {} false A =
    (do
      let es₀ ← initCKAShiftedRaw prng fs lam l false
      let res ← (simulateQ (DeliverForge.implEDFShiftedPaperGen (decide (Δcka = 0)) l
        (DeliverForge.hooksCKAShifted cka prng fs l tStarH) (2 + Δcka) qep fs.maxSkip tStar
        (Config.auth tStar) (⟨true, some (l - 1), tStar⟩ : Mode).policy) A).run es₀
      return some res) := by
    unfold DeliverForge.engRunDFShiftedPaperGen DeliverForge.initCKAShifted initCKAShiftedRaw
    simp only [StateT.run_bind, StateT.run_lift, DeliverForge.liftCShifted, bind_assoc, pure_bind]
    refine bind_congr fun kr => ?_
    by_cases hl : 1 ≤ l
    · simp only [hl, ↓reduceIte, StateT.run_bind, StateT.run_lift, DeliverForge.setγPreShifted,
        StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
      refine bind_congr fun γA? => bind_congr fun γB? => ?_
      have hEqH :
          ({ base := {},
             γPre := Function.update (Function.update (fun _ => none) .A γA?) .B γB? } :
            DeliverForge.CKAStateShifted Γ T I) =
          { base := {}, γPre := fun | .A => γA? | .B => γB? } := by
        congr 1; funext p; cases p <;> rfl
      rw [hEqH]; rfl
    · simp only [hl, ↓reduceIte, StateT.run_pure, pure_bind]
      have hEqH :
          ({} : DeliverForge.CKAStateShifted Γ T I) =
          { base := {}, γPre := fun | .A => none | .B => none } := by
        congr 1; funext p; cases p <;> rfl
      rw [hEqH]; rfl
  rw [eval_bind, hInit, hVp, hRun]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKAShiftedRaw prng fs lam l false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKAShiftedRaw_inv prng fs lam l false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKAShiftedRaw_vrInv (B := B_q) (qAdv := qAdv) prng fs lam l false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implECDFShiftedPaper_vr_eq (decide (Δcka = 0)) hDefaultE
    (fun _ => rfl) ckaShiftedHsEnc (fun _ => True)
    (hooksCKAShiftedC B l tStarH) (DeliverForge.hooksCKAShifted cka prng fs l tStarH)
    L B_q l (2 + Δcka) qep fs.maxSkip tStar hHk hVRHk
    (modeCfgEC OO ⟨true, some (l - 1), tStar⟩) (⟨true, some (l - 1), tStar⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨true, some (l - 1), tStar⟩) heqT heqM heqE
    (⟨true, some (l - 1), tStar⟩ : Mode).policy
    (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀ hVR₀
  dsimp only [Expr.v0, Mode.cfg, ↓reduceIte] at hSim hSimInv
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hOut := authOutE_eval vpTblEnc ckaShiftedHsEnc (O' := OO) L (2 + Δcka)
    (⟨true, some (l - 1), tStar⟩ : Mode).policy .v0
    (Env.cons (esEnc vpTblEnc ckaShiftedHsEnc es') (Env.cons (t := .bool) b' .nil))
    es' hBnd'.leaks_le hBnd'.corrs_le rfl
  exact congrArg pure hOut

@[simp] theorem implECDFShiftedPaper_hooksCKAShiftedC_queries (b1 : Bool)
    (L B l Δ qep maxSkip tStarH tStar : ℕ) (mo : Mode) {Γ'} (es : Expr OO Γ' ckaShiftedEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksCKAShiftedC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B l tStarH)
      L l Δ qep maxSkip tStar (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  cases b1 <;> simp [implECDFShiftedPaperGen, implECShiftedPaperGen, corrECShiftedPaper,
    transmitEC, challEC, deliverEC, injectECGen, injectEC, injectECB1, deliverForgeECGen,
    deliverForgeEC, deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
    hooksCKAShiftedC, Comp.queries]

end HooksCKACDFShiftedPaper

section HooksPRNGCDFShiftedPaper

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

/-- Costed shifted paper PRF-PRNG reduction parameterized by `authH : Bool`. -/
def redPRNGAuthDFShiftedPaperGenProg (L B Δcka qep maxSkip l tStar : ℕ) (authH : Bool) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_] do
    es ← initPRNGEStateC (raw ⟨authH, some (l - 1), tStar⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFShiftedPaperGen (raw (!authH)) (raw (hooksPRNGC B ⟨authH, some (l - 1), tStar⟩))
      L l (raw (2 + Δcka)) qep maxSkip tStar
      (raw (modeCfgEC OO ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st

abbrev redPRNGAuthDFShiftedPaperProg (L B Δcka qep maxSkip l tStar : ℕ) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip l tStar true

abbrev redPRNGAuthDFShiftedDir2PaperProg (L B qep maxSkip l tStar : ℕ) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B 0 qep maxSkip l tStar false

private theorem simulateQ_liftM_unif {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl tspec (StateT St ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM mx : TComp tspec α) = StateT.lift mx := by
  ext st; rw [← liftComp_eq_liftM]
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
    (liftComp mx (unifSpec + tspec))).run st = (mx >>= fun a => pure (a, st))
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : TComp tspec _) := rfl
    have hrun : ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) + impl) (.inl t)) :
        StateT St ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]; simp only [bind_assoc, pure_bind, ih]

private theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st = (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT; rw [simulateQ_liftM_unif]; rfl

theorem redPRNGAuthDFShiftedPaperProg_advantage_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L B B_q Δcka qep l tStar : ℕ) (authH : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksPRNG cka prng fs ⟨authH, some (l - 1), tStar⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip l tStar authH).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng
        (DeliverForge.redPRNGAuthDFShiftedPaperGen cka prng fs lam Δcka qep l tStar authH A) := by
  have hEval : (redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep fs.maxSkip l tStar authH).eval (fun _ => A) () =
    (do
      let es₀ ← initPRNGRaw cka prng fs lam ⟨authH, some (l - 1), tStar⟩ false
      let (_, es') ← (simulateQ (DeliverForge.implEDFShiftedPaperGen (!authH) l
        (hooksPRNG cka prng fs ⟨authH, some (l - 1), tStar⟩)
        (2 + Δcka) qep fs.maxSkip tStar (⟨true, some (l - 1), tStar⟩ : Mode).cfg
        (⟨true, some (l - 1), tStar⟩ : Mode).policy) A).run es₀
      return authOut (2 + Δcka) (⟨true, some (l - 1), tStar⟩ : Mode).policy es') := by
    have hA' : A.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
      refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
    have hHk := hooksPRNGC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) cka prng fs B ⟨authH, some (l - 1), tStar⟩
      hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT hSampCCoins
      (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
    have hInit := initPRNGEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) cka prng fs hInitA hInitB
      hPrngUp hFsInitS hFsInitR hSampKC ⟨authH, some (l - 1), tStar⟩ (.bool false)
      (Env.cons (t := (.unit : Ty S)) () .nil)
    unfold CostedReduction.eval redPRNGAuthDFShiftedPaperGenProg CostedReduction.impl; dsimp only; rw [eval_bind, hInit]
    let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
      (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
    let esT := @prngEsTy KC Γ CCoins T I KR RSt K SS RS M E
    have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
        vpE := rfl
    rw [hVp]
    simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
      bind_assoc, pure_bind]
    refine OracleComp.bind_congr_of_forall_mem_support
      (initPRNGRaw cka prng fs lam ⟨authH, some (l - 1), tStar⟩ false) fun es₀ hes₀ => ?_
    have ⟨hInv₀, _⟩ := initPRNGRaw_inv cka prng fs lam ⟨authH, some (l - 1), tStar⟩ false
      hqB hB1 hBB es₀ hes₀
    have hVR₀ := initPRNGRaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam
      ⟨authH, some (l - 1), tStar⟩ false (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
    have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implECDFShiftedPaper_vr_eq (!authH) hDefaultE
      (fun _ => rfl) prngHsEnc (fun _ => True) (hooksPRNGC B ⟨authH, some (l - 1), tStar⟩)
      (hooksPRNG cka prng fs ⟨authH, some (l - 1), tStar⟩) L B_q l (2 + Δcka) qep fs.maxSkip tStar
      hHk hVRHk (modeCfgEC OO ⟨true, some (l - 1), tStar⟩) (⟨true, some (l - 1), tStar⟩ : Mode).cfg
      (modeCfgEC_agrees ⟨true, some (l - 1), tStar⟩) heqT heqM heqE
      (⟨true, some (l - 1), tStar⟩ : Mode).policy (fun _ _ _ _ _ _ => trivial) hA' es₀
      trivial hInv₀ hVR₀
    dsimp only [Expr.v0] at hSim; rw [hSim, bind_map_left]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
    obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
    have hBnd' := hInv'.toBoundedEngine
    have hOut := authOutE_eval vpE prngHsEnc (O' := OO) L (2 + Δcka)
      (⟨true, some (l - 1), tStar⟩ : Mode).policy .v0
      (Env.cons (t := esT) (esEnc vpE prngHsEnc es')
        (Env.cons (t := (.bool : Ty S)) b' .nil))
      es' hBnd'.leaks_le hBnd'.corrs_le rfl
    dsimp only [Prod.map, id, Expr.v0, vpE, Mode.policy] at hOut ⊢; rw [hOut]
  have hGame :
      PRFPRNG.game prng
        ((redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip l tStar authH).eval (fun _ => A) ()) =
      PRFPRNG.game prng
        (DeliverForge.redPRNGAuthDFShiftedPaperGen cka prng fs lam Δcka qep l tStar authH A) := by
    unfold PRFPRNG.game
    refine bind_congr fun b_prng => ?_
    have hBr : PRFPRNG.branch prng b_prng
        ((redPRNGAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK)
            L B Δcka qep fs.maxSkip l tStar authH).eval (fun _ => A) ()) =
        PRFPRNG.branch prng b_prng
          (DeliverForge.redPRNGAuthDFShiftedPaperGen cka prng fs lam Δcka qep l tStar authH A) := by
      rw [hEval]
      unfold PRFPRNG.branch DeliverForge.redPRNGAuthDFShiftedPaperGen
        DeliverForge.authSimDFShiftedPaperGen DeliverForge.engRunDFShiftedPaperGen initPRNG
        initPRNGRaw
      refine bind_congr fun kr => ?_
      rw [StateT.run'_eq, StateT.run'_eq]
      refine congrArg (Prod.fst <$> ·) ?_
      simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run,
        bind_assoc, pure_bind]
      refine bind_congr fun kc => ?_
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
      obtain ⟨σv, k, rfl, rfl⟩ := rootPRNG_zero_support_some (T := T) prng
        ⟨authH, some (l - 1), tStar⟩ lam kr b_prng step h₀ sp hmem
      simp [StateT.run_pure, simulateQ_pure, Mode.policy]; rfl
    unfold PRFPRNG.branch at hBr
    simp only [← bind_assoc]
    exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr
  unfold PRFPRNG.advantage
  rw [hGame]

@[simp] theorem implECDFShiftedPaper_hooksPRNGC_queries (b1 : Bool)
    (L l B Δcka qep maxSkip tStar : ℕ) (mo mo' : Mode) {Γ'} (es : Expr OO Γ' prngEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B mo)
      L l (2 + Δcka) qep maxSkip tStar (modeCfgEC OO mo') mo'.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  cases b1 <;> simp [implECDFShiftedPaperGen, implECShiftedPaperGen, transmitEC, challEC, deliverEC,
    injectECGen, injectEC, injectECB1, corrECShiftedPaper, deliverForgeECGen, deliverForgeEC,
    deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksPRNGC, Comp.queries]

end HooksPRNGCDFShiftedPaper
section HooksFSCDFShiftedPaper

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hsTy" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsEnc" => fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "hsDec" => fsHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpEnc" =>
  fsVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

theorem corrEShiftedPaper_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L l : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E) (FSState T RSt K I SS RS E))
    (P : Party) (hvR : ∀ t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.corrEShiftedPaper l (hooksFSL cka prng fs L Δcka mo j) π P).run es =
      (DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) π P).run es := by
  unfold DeliverForge.corrEShiftedPaper; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !es.g.corrAllowedPaper P)
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp [hdoom]
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        hooksFSL_reveal_eq cka prng fs L Δcka mo j es.g P (es.g.st P) hvR]

theorem implEDFShiftedPaper_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L l Δ qep maxSkip tStar : ℕ) (cfg : Config M)
    (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E) (FSState T RSt K I SS RS E))
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hVR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFSL cka prng fs L Δcka mo j) Δ qep maxSkip
        tStar cfg π (.inr q)).run es =
      (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip tStar cfg π (.inr q)).run es := by
  rcases q with ((t3 | arg) | P) | arg
  · exact implEDFShifted_hooksFSL_eq cka prng fs L l Δ qep maxSkip cfg π Δcka mo j es
      (.inl (.inl (.inl t3))) hVR
  · change (injectEGen b1 (hooksFSL cka prng fs L Δcka mo j) Δ qep tStar cfg arg).run es =
      (injectEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg arg).run es
    rw [injectEGen_hooksFSL_eq]
  · exact corrEShiftedPaper_hooksFSL_eq cka prng fs L l π Δcka mo j es P (hVR P)
  · change (deliverForgeEGen b1 (hooksFSL cka prng fs L Δcka mo j) Δ qep tStar cfg arg).run es =
      (deliverForgeEGen b1 (hooksFS cka prng fs Δcka mo j) Δ qep tStar cfg arg).run es
    rw [deliverForgeEGen_hooksFSL_eq]

theorem corrEShiftedPaper_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {L B q : ℕ} (l : ℕ) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E) (FSState T RSt K I SS RS E))
    (P : Party) (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) π P).run es),
      FSEngineInv L B q res.2 := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := corrEShiftedPaper_inv (hooksFS cka prng fs Δcka mo j) l π es P hInv.sm (out, es') hmem
  unfold DeliverForge.corrEShiftedPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom :
        (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hPres := fsReveal_preserve cka prng fs Δcka mo j es.h es.g P (es.g.st P)
        (revRes, h') hrev
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩;
         exact ⟨hSm, by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
           by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
           by dsimp only; rw [hPres.2.2]; exact hInvQ.fsTrans_le,
           hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩)

theorem implEDFShiftedPaper_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {L B q Δ qep maxSkip tStar : ℕ} (l : ℕ)
    (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E) (FSState T RSt K I SS RS E))
    (q_df : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j)
        Δ qep maxSkip tStar cfg π (.inr q_df)).run es), FSEngineInv L B q res.2 := by
  rcases q_df with ((t3 | arg) | P) | arg
  · exact implEDFShifted_fs_inv (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cka prng fs l cfg π Δcka
      mo j es (.inl (.inl (.inl t3))) hInv
  · exact injectEGen_fs_inv b1 cka prng fs cfg Δcka mo j es arg hInv
  · exact corrEShiftedPaper_fs_inv cka prng fs l π Δcka mo j es P hInv
  · exact deliverForgeEGen_fs_inv b1 cka prng fs cfg Δcka mo j es arg hInv

theorem simulateQ_implECDFShiftedPaper_fs_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L B B_q l Δ Δcka qep tStar : ℕ) (mo mo' : Mode)
    (j : ℕ)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) = fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
          (FSState T RSt K I SS RS E)),
        FSEngineInv L B_q qAdv es →
        (simulateQ
          (handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) oa).run
          (esEnc vpEnc hsEnc es) =
          (Prod.map id (esEnc vpEnc hsEnc) <$>
            (simulateQ (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j)
              Δ qep fs.maxSkip tStar mo'.cfg mo'.policy) oa).run es) ∧
        ∀ res ∈ support ((simulateQ
            (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j)
              Δ qep fs.maxSkip tStar mo'.cfg mo'.policy) oa).run es),
          FSEngineInv L B_q 0 res.2 ∧ res.2.g.b = es.g.b := by
  have hHk := hooksFSC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) cka prng fs L B Δcka mo j hSend hRecv hPrngUp
    hFsInitS hFsInitR hFsSend heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR)
    (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (γvT := .base .γ)
    (svT := .base .sig) (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
  have hVp : vpEnc = vpE := rfl
  intro α oa; induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv; refine ⟨by simp [simulateQ_pure, Prod.map], fun res hmem => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) (.inl n)).run
            (esEnc vpEnc hsEnc es) =
          (fun u => (u, esEnc vpEnc hsEnc es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j) Δ qep fs.maxSkip
            tStar mo'.cfg mo'.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [DeliverForge.implEDFShiftedPaperGen, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hInv).1, fun res hmem => ?_⟩
      rw [mem_support_bind_iff] at hmem; obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m :=
        fun u => by simpa [isGameQuery] using hq.2 u
      have hStepL := rdecDF_implECDFShiftedPaper_eval b1 hDefaultE hsEnc (FSHBounded L)
        (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        (hooksFSL cka prng fs L Δcka mo j) hHk
        L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.cfg (modeCfgEC_agrees mo')
        heqT heqM heqE mo'.policy .v0 .v1
        (.cons (esEnc vpE hsEnc es)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es t hInv.toFSHBounded hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implEDFShiftedPaper_hooksFSL_eq b1 cka prng fs L l Δ qep fs.maxSkip tStar mo'.cfg
        mo'.policy Δcka mo j es t hInv.vR_none_of_le_L] at hStepL
      have hStep :
          ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) (.inr t)).run
            (esEnc vpEnc hsEnc es) =
          Prod.map id (esEnc vpEnc hsEnc) <$>
            (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j) Δ qep
              fs.maxSkip tStar mo'.cfg mo'.policy (.inr t)).run es := by
        rw [hVp]; dsimp only [vpE] at hStepL ⊢
        simp only [handlerImpl, StateT.run_mk, prngSMCodecDF, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · exact (ih u (hqm u) es₁
          (implEDFShiftedPaper_fs_inv b1 cka prng fs l mo'.cfg mo'.policy Δcka mo j es t hInv
            (u, es₁) hmem)).1
      · intro res hmem; rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hInv₁ := implEDFShiftedPaper_fs_inv b1 cka prng fs l mo'.cfg mo'.policy Δcka mo j es t
          hInv (u, es₁) hmem₁
        have hb₁ := implEDFShiftedPaper_b_eq b1 (hooksFS cka prng fs Δcka mo j) l mo'.cfg
          mo'.policy es t (u, es₁) hmem₁
        obtain ⟨hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hInv₁).2 res hmem₂
        exact ⟨hInv₂, hb₂.trans hb₁⟩

end HooksFSCDFShiftedPaper
end CryptoGames.SM.Construction
