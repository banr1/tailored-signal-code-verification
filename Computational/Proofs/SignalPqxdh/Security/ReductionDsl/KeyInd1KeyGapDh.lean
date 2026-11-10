/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeyGapDh

/-!
# Costed One-Key `KeyInd` `GapDhWithSign` Reduction

**Checked by Lean.** Expresses the four-leg one-key `GapDhWithSign` simulator
`fgKeyInd1KeyGapDhAdv4` as first-order `CostedReduction` syntax trees (`fgKeyInd1KeyGapDhProg` and
the tuple-keyed `fgKeyInd1KeyGapDh2Prog`).
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-! ## Context Renaming and Interface Lifting -/

abbrev Ren (Γ Δ : List PT) := {τ : PT} → Var Γ τ → Var Δ τ

def liftRen {Γ Δ : List PT} {σ : PT} (ρ : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

def twoVarRen {Δ : List PT} {τ₁ τ₂ : PT} (v₁ : Var Δ τ₁) (v₂ : Var Δ τ₂) : Ren [τ₁, τ₂] Δ
  | _, .zero => v₁
  | _, .succ .zero => v₂

def renameExpr : {Γ Δ : List PT} → {t : PT} → Ren Γ Δ → Expr pqxdhOps Γ t → Expr pqxdhOps Δ t
  | _, _, _, ρ, .var x => .var (ρ x)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .bool b => .bool b
  | _, _, _, _, .nat n => .nat n
  | _, _, _, ρ, .add a b => .add (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .sub a b => .sub (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .mulK k a => .mulK k (renameExpr ρ a)
  | _, _, _, ρ, .divK k a => .divK k (renameExpr ρ a)
  | _, _, _, ρ, .modK k a => .modK k (renameExpr ρ a)
  | _, _, _, ρ, .lt a b => .lt (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .eqN a b => .eqN (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .not a => .not (renameExpr ρ a)
  | _, _, _, ρ, .and a b => .and (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .ite c a b => .ite (renameExpr ρ c) (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .pair a b => .pair (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .fst a => .fst (renameExpr ρ a)
  | _, _, _, ρ, .snd a => .snd (renameExpr ρ a)
  | _, _, _, ρ, .inl a => .inl (renameExpr ρ a)
  | _, _, _, ρ, .inr a => .inr (renameExpr ρ a)
  | _, _, _, _, .none => .none
  | _, _, _, ρ, .some a => .some (renameExpr ρ a)
  | _, _, _, ρ, .caseOpt e n s =>
    .caseOpt (renameExpr ρ e) (renameExpr ρ n) (renameExpr (liftRen ρ) s)
  | _, _, _, ρ, .caseSum e l r =>
    .caseSum (renameExpr ρ e) (renameExpr (liftRen ρ) l) (renameExpr (liftRen ρ) r)
  | _, _, _, ρ, .letE e b => .letE (renameExpr ρ e) (renameExpr (liftRen ρ) b)
  | _, _, _, ρ, .op o a => .op o (renameExpr ρ a)
  | _, _, _, _, .nil => .nil
  | _, _, _, ρ, .cons x l => .cons (renameExpr ρ x) (renameExpr ρ l)
  | _, _, _, ρ, .len l => .len (renameExpr ρ l)
  | _, _, _, ρ, .take n l => .take (renameExpr ρ n) (renameExpr ρ l)
  | _, _, _, ρ, .appendL K a b => .appendL K (renameExpr ρ a) (renameExpr ρ b)
  | _, _, _, ρ, .findB K l p => .findB K (renameExpr ρ l) (renameExpr (liftRen ρ) p)
  | _, _, _, ρ, .anyB K l p => .anyB K (renameExpr ρ l) (renameExpr (liftRen ρ) p)
  | _, _, _, ρ, .mapB K l f => .mapB K (renameExpr ρ l) (renameExpr (liftRen ρ) f)
  | _, _, _, ρ, .foldrB K l z f =>
    .foldrB K (renameExpr ρ l) (renameExpr ρ z) (renameExpr (liftRen (liftRen ρ)) f)
  | _, _, _, ρ, .tconst a => .tconst (renameExpr ρ a)
  | _, _, _, ρ, .tget m i => .tget (renameExpr ρ m) (renameExpr ρ i)
  | _, _, _, ρ, .tset m i a => .tset (renameExpr ρ m) (renameExpr ρ i) (renameExpr ρ a)

def renameComp {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} :
    {Γ Δ : List PT} → {t : PT} → Ren Γ Δ → Comp pqxdhOps I Γ t → Comp pqxdhOps I Δ t
  | _, _, _, ρ, .ret e => .ret (renameExpr ρ e)
  | _, _, _, ρ, .bind c k => .bind (renameComp ρ c) (renameComp (liftRen ρ) k)
  | _, _, _, ρ, .ite b c d => .ite (renameExpr ρ b) (renameComp ρ c) (renameComp ρ d)
  | _, _, _, ρ, .caseOpt e n s =>
    .caseOpt (renameExpr ρ e) (renameComp ρ n) (renameComp (liftRen ρ) s)
  | _, _, _, ρ, .caseSum e l r =>
    .caseSum (renameExpr ρ e) (renameComp (liftRen ρ) l) (renameComp (liftRen ρ) r)
  | _, _, _, ρ, .sample s e => .sample s (renameExpr ρ e)
  | _, _, _, ρ, .query g e => .query g (renameExpr ρ e)
  | _, _, _, ρ, .iter n e body => .iter n (renameExpr ρ e) (renameComp (liftRen ρ) body)
  | _, _, _, ρ, .findM K l p => .findM K (renameExpr ρ l) (renameComp (liftRen ρ) p)
  | _, _, _, ρ, .anyM K l p => .anyM K (renameExpr ρ l) (renameComp (liftRen ρ) p)
  | _, _, _, ρ, .mapM K l f => .mapM K (renameExpr ρ l) (renameComp (liftRen ρ) f)
  | _, _, _, ρ, .consumeFirstM K l p mk =>
    .consumeFirstM K (renameExpr ρ l) (renameComp (liftRen ρ) p) (renameExpr (liftRen ρ) mk)
  | _, _, _, ρ, .foldM K l z f =>
    .foldM K (renameExpr ρ l) (renameExpr ρ z) (renameComp (liftRen (liftRen ρ)) f)

/-- Lifts a `pqGapDhIface` computation into `pqSigAndDdhIface` with zero signing queries. -/
def liftGdhComp : {Γ : List PT} → {t : PT} →
    Comp pqxdhOps pqGapDhIface Γ t → Comp pqxdhOps pqSigAndDdhIface Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind c k => .bind (liftGdhComp c) (liftGdhComp k)
  | _, _, .ite b c d => .ite b (liftGdhComp c) (liftGdhComp d)
  | _, _, .caseOpt e n s => .caseOpt e (liftGdhComp n) (liftGdhComp s)
  | _, _, .caseSum e l r => .caseSum e (liftGdhComp l) (liftGdhComp r)
  | _, _, .sample s e => Comp.sample (I := pqSigAndDdhIface) s e
  | _, _, .query g e =>
    match g with
    | Sum.inl t => Comp.query (I := pqSigAndDdhIface) (Sum.inl t) e
    | Sum.inr () => Comp.query (I := pqSigAndDdhIface) (Sum.inr (Sum.inr ())) e
  | _, _, .iter n e body => .iter n e (liftGdhComp body)
  | _, _, .findM K l p => .findM K l (liftGdhComp p)
  | _, _, .anyM K l p => .anyM K l (liftGdhComp p)
  | _, _, .mapM K l f => .mapM K l (liftGdhComp f)
  | _, _, .consumeFirstM K l p mk => .consumeFirstM K l (liftGdhComp p) mk
  | _, _, .foldM K l z f => .foldM K l z (liftGdhComp f)

def sigChalQ_dsl (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    Comp pqxdhOps pqSigAndDdhIface Γ (B 64) :=
  Comp.query (I := pqSigAndDdhIface) (Sum.inr (Sum.inl m)) msg

/-! ## One-Key Simulator State and Handler -/

abbrev gdh1KeyStateTy : PT := .prod gdhStateTy .nat

def sim1KeyStateToVal {S : Setup} (pa : paramsTy.denote) (st : FgKeyInd1KeySimState S) :
    gdh1KeyStateTy.denote :=
  ((pa, simStateToVal st.sim), st.sigBudget)

def callGdhHandle (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyStateTy) :=
  letV (.fst (v st1)) fun gst =>
  bindV (renameComp (twoVarRen gst (.succ q)) (liftGdhComp (gdhHandle S K))) fun res =>
  .ret (.pair (.fst (v res)) (.pair (.snd (v res)) (.snd (v st1))))

def initPrin1KeyB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyStateTy) :=
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  .ite (eAny K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (v u))
    (.ret (.pair rNone (v st1)))
    (letV (.and (paPrinFlag (v pa)) (natEq (v u) (paPrinIdx (v pa)))) fun isT =>
     bindV (liftGdhComp (gPrim sBytes32)) fun sk0 =>
     bindV (liftGdhComp (gPrim (qX25519Base (v sk0)))) fun pk0 =>
     letV (.ite (v isT) (litB 32 []) (v sk0)) fun sec0 =>
     letV (.ite (v isT) (paUp (v pa)) (v pk0)) fun ikPk =>
     let e := peMk (v sec0) (v ikPk) (v sec0) (v ikPk) (.bool false)
     let bSt' := stUpd (v bSt) (prin := .cons (.pair (v u) e) (stPrin (v bSt)))
     let sm' := smUpd (v sm) (base := bSt')
     .ret (.pair (rInitPrin (v ikPk) (v ikPk)) (.pair (.pair (v pa) sm') (.snd (v st1)))))

/-- One-key `.genSPK u j` handler signing target-principal bundles via two `sigChalQ_dsl` queries
while `sigBudget > 0`. -/
def genSpk1KeyB (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy)
    (x : Var Δ (.prod .nat .nat)) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyStateTy) :=
  let pa := Expr.fst (.fst (v st1))
  .ite (.and (paPrinFlag pa) (natEq (.fst (v x)) (paPrinIdx pa)))
    (letV pa fun paV =>
     letV (.snd (.fst (v st1))) fun sm =>
     letV (smBase (v sm)) fun bSt =>
     letV (.snd (v st1)) fun sigB =>
     .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
       (.ret (.pair rNone (v st1)))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (v st1)))
         fun ue =>
           .ite (natEq (v sigB) (.nat 0))
             (.ret (.pair rNone (v st1)))
             (letV (natEq (spkFlatIdxE S (.fst (v x)) (.snd (v x))) (paSpkIdx (v paV))) fun isT =>
              bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
              bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
              letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
              letV (.ite (v isT) (KeyInd.paV (v paV)) (v spkPkRaw)) fun spkPk =>
              bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
              bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
              bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
              bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
              let jId := u32OfNat (.snd (v x))
              let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
                (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
              let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
                .none jId (.fst (v kp)) (v pqSig)
              let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
              let sm' := smUpd (v sm) (base := bSt')
              .ret (.pair (rBundle buOut) (.pair (.pair (v paV) sm') (.sub (v sigB) (.nat 1)))))))
    (callGdhHandle S K st1 q)

def gdh1KeyHandle (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyStateTy, keyIndQueryTy]
      (.prod keyIndRespTy gdh1KeyStateTy) :=
  let st1 : Var [gdh1KeyStateTy, keyIndQueryTy] gdh1KeyStateTy := .zero
  let q : Var [gdh1KeyStateTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  caseSumV (v q) (fun u => initPrin1KeyB K st1 u) fun r1 =>
  caseSumV (v r1) (fun _ => callGdhHandle S K (.succ (.succ st1)) (.succ (.succ q))) fun r2 =>
  caseSumV (v r2) (fun x => genSpk1KeyB S K (.succ (.succ (.succ st1))) (.succ (.succ (.succ q))) x)
    fun _ => callGdhHandle S K (.succ (.succ (.succ st1))) (.succ (.succ (.succ q)))

def gdh1KeyFinish (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyStateTy, .bool] (B 32) :=
  let st1 : Var [gdh1KeyStateTy, .bool] gdh1KeyStateTy := .zero
  letV (.fst (v st1)) fun gst =>
  renameComp (twoVarRen gst (.succ (.succ .zero))) (liftGdhComp (gdhFinish S K))

/-! ## Flat-Indexed Reduction -/

def initParams1KeyIk (S : Setup) {Γ : List PT}
    (tIdx pIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ paramsTy :=
  paMk V U U (.bool true) pIdx (.bool false) tIdx (.nat S.N_spk_tot)
    (.bool false) (.nat S.N_opk_tot) (.nat 2)

def initParams1KeyFlat (S : Setup) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ paramsTy :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  .ite (.lt idx (.nat nA))
    (initParamsDh S (.bool true)
      (.divK S.N_spk_tot idx) (.modK S.N_spk_tot idx) U V)
    (.ite (.lt idx (.nat (nA + nC)))
      (let r := Expr.sub idx (.nat nA)
       initParamsDh S (.bool false)
         (.divK S.N_spk_tot r) (.modK S.N_spk_tot r) U V)
      (.ite (.lt idx (.nat (nA + nC + nB)))
        (let r := Expr.sub idx (.nat (nA + nC))
         initParams1KeyIk S (.divK S.N_id r) (.modK S.N_id r) U V)
        (let r := Expr.sub idx (.nat (nA + nC + nB))
         initParamsOpk S (.divK S.N_opk_tot r) (.modK S.N_opk_tot r) U V)))

def initAdv4_1KeyBase (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqGapDhIface Γ gdhStateTy :=
  letV (.pair U V) fun uv =>
  bindV (gPrim (sIndex (fgTotalIndexCount S))) fun idx =>
  bindV (gPrim sBool) fun secb =>
  .ret (.pair (initParams1KeyFlat S (.fst (v uv)) (.snd (v uv)) (v idx)) (emptySimE (v secb)))

def initAdv4_1Key (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqSigAndDdhIface Γ gdh1KeyStateTy :=
  bindV (liftGdhComp (initAdv4_1KeyBase S U V)) fun s =>
  .ret (.pair (v s) (.nat (min S.N_spk_tot S.N_recv)))

/-- Flat-indexed `CostedReduction` syntax tree for `fgKeyInd1KeyGapDhAdv4 S b`. -/
def fgKeyInd1KeyGapDhProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := gdh1KeyStateTy
  init   :=
    bindV (initAdv4_1Key S (.fst (.var .zero)) (.snd (.var .zero))) fun s =>
      .ret (.pair .unit (v s))
  handle := gdh1KeyHandle S K
  finish := gdh1KeyFinish S K

/-! ## Tuple-Keyed Reduction -/

abbrev gdh1KeyState2Ty : PT := .prod gdhState2Ty .nat

def sim1KeyState2ToVal {S : Setup} (pa2 : params2Ty.denote) (st : FgKeyInd1KeySimState S)
    (sigB : Nat) : gdh1KeyState2Ty.denote :=
  ((pa2, simStateToVal st.sim), sigB)

def callGdhHandle2 (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyState2Ty) :=
  letV (.fst (v st1)) fun gst =>
  bindV (renameComp (twoVarRen gst (.succ q)) (liftGdhComp (gdhHandle2 S K))) fun res =>
  .ret (.pair (.fst (v res)) (.pair (.snd (v res)) (.snd (v st1))))

def initPrin1Key2B (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyState2Ty) (u : Var Γ₂ .nat) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyState2Ty) :=
  letV (.fst (.fst (v st1))) fun pa =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  .ite (eAny K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (v u))
    (.ret (.pair rNone (v st1)))
    (letV (eCaseOpt (pa2PrinTarget (v pa)) (.bool false) fun uT => natEq (v u) (v uT)) fun isT =>
     bindV (liftGdhComp (gPrim sBytes32)) fun sk0 =>
     bindV (liftGdhComp (gPrim (qX25519Base (v sk0)))) fun pk0 =>
     letV (.ite (v isT) (litB 32 []) (v sk0)) fun sec0 =>
     letV (.ite (v isT) (pa2Up (v pa)) (v pk0)) fun ikPk =>
     let e := peMk (v sec0) (v ikPk) (v sec0) (v ikPk) (.bool false)
     let bSt' := stUpd (v bSt) (prin := .cons (.pair (v u) e) (stPrin (v bSt)))
     let sm' := smUpd (v sm) (base := bSt')
     .ret (.pair (rInitPrin (v ikPk) (v ikPk)) (.pair (.pair (v pa) sm') (.snd (v st1)))))

def genSpk1Key2B (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy)
    (x : Var Δ (.prod .nat .nat)) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyState2Ty) :=
  let pa := Expr.fst (.fst (v st1))
  .ite (eCaseOpt (pa2PrinTarget pa) (.bool false) fun uT => natEq (.fst (v x)) (v uT))
    (letV pa fun paV =>
     letV (.snd (.fst (v st1))) fun sm =>
     letV (smBase (v sm)) fun bSt =>
     letV (.snd (v st1)) fun sigB =>
     .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
       (.ret (.pair rNone (v st1)))
       (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
         (.ret (.pair rNone (v st1)))
         fun ue =>
           .ite (natEq (v sigB) (.nat 0))
             (.ret (.pair rNone (v st1)))
             (letV (eCaseOpt (pa2SpkTarget (v paV)) (.bool false) fun sp => nat2Eq (v x) (v sp)) fun isT =>
              bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
              bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
              letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
              letV (.ite (v isT) (KeyInd.pa2V (v paV)) (v spkPkRaw)) fun spkPk =>
              bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
              bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
              bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
              bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
              let jId := u32OfNat (.snd (v x))
              let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
                (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
              let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
                .none jId (.fst (v kp)) (v pqSig)
              let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
              let sm' := smUpd (v sm) (base := bSt')
              .ret (.pair (rBundle buOut) (.pair (.pair (v paV) sm') (.sub (v sigB) (.nat 1)))))))
    (callGdhHandle2 S K st1 q)

def gdh1KeyHandle2 (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyState2Ty, keyIndQueryTy]
      (.prod keyIndRespTy gdh1KeyState2Ty) :=
  let st1 : Var [gdh1KeyState2Ty, keyIndQueryTy] gdh1KeyState2Ty := .zero
  let q : Var [gdh1KeyState2Ty, keyIndQueryTy] keyIndQueryTy := .succ .zero
  caseSumV (v q) (fun u => initPrin1Key2B K st1 u) fun r1 =>
  caseSumV (v r1) (fun _ => callGdhHandle2 S K (.succ (.succ st1)) (.succ (.succ q))) fun r2 =>
  caseSumV (v r2) (fun x => genSpk1Key2B S K (.succ (.succ (.succ st1))) (.succ (.succ (.succ q))) x)
    fun _ => callGdhHandle2 S K (.succ (.succ (.succ st1))) (.succ (.succ (.succ q)))

def gdh1KeyFinish2 (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [gdh1KeyState2Ty, .bool] (B 32) :=
  let st1 : Var [gdh1KeyState2Ty, .bool] gdh1KeyState2Ty := .zero
  letV (.fst (v st1)) fun gst =>
  renameComp (twoVarRen gst (.succ (.succ .zero))) (liftGdhComp (gdhFinish2 S K))

/-- Tuple-keyed 4-mode parameter sampler matching `params1KeyFlatVal` under `params2ToFlat S`
without `bits S.N_*` AST size terms. -/
def initParams1Key2C (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) : Comp pqxdhOps pqGapDhIface Δ params2Ty :=
  if fgTotalIndexCount S = 0 then
    let U := .fst (v uv)
    let V := .snd (v uv)
    .ret (pa2Mk U V U .none (.bool false)
      (.some (.pair (.bool true) (.pair (.nat 0) (.nat 0))))
      .none (.bool true)
      (.some (.pair (.nat 0) (.pair (.nat 0) (.nat 0))))
      (.nat 3))
  else
    let nA := S.N_id * S.N_spk_tot
    let nC := S.N_send_tot * S.N_spk_tot
    let nB := S.N_send_tot * S.N_id
    let nD := S.N_send_opk_tot * S.N_opk_tot
    chooseArm2C (Γ₁ := Γ₁) (nA + nC) (nB + nD)
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nA nC
          (fun {_} [_] =>
            bindV (samplePrin2C S) fun pt =>
            bindV (sampleSpkPair2C S) fun st =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
          (fun {_} [_] =>
            bindV (sampleSendTarget2C S) fun et =>
            bindV (sampleSpkPair2C S) fun st =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1))))
      (fun {_} [_] =>
        chooseArm2C (Γ₁ := Γ₁) nB nD
          (fun {_} [_] =>
            bindV (sampleSendTarget2C S) fun et =>
            bindV (samplePrin2C S) fun pt =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk V U U (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)))
          (fun {_} [_] =>
            bindV (sampleSendOpkTarget2C S) fun et =>
            bindV (sampleOpkTriple2C S) fun ot =>
            let U := .fst (v uv)
            let V := .snd (v uv)
            .ret (pa2Mk U V U .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3))))

def initAdv4_1Key2Base (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqGapDhIface Γ gdhState2Ty :=
  letV (.pair U V) fun uv =>
  bindV (initParams1Key2C S uv) fun pa =>
  bindV (gPrim sBool) fun secb =>
  .ret (.pair (v pa) (emptySimE (v secb)))

def initAdv4_1Key2 (S : Setup) (K : Nat) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    Comp pqxdhOps pqSigAndDdhIface Γ gdh1KeyState2Ty :=
  bindV (liftGdhComp (initAdv4_1Key2Base S U V)) fun s =>
  .ret (.pair (v s) (.nat (min K (min S.N_spk_tot S.N_recv))))

/-- Tuple-keyed `CostedReduction` syntax tree for `fgKeyInd1KeyGapDhAdv4 S b` without `bits S.N_*`
AST size terms. -/
def fgKeyInd1KeyGapDh2Prog (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := gdh1KeyState2Ty
  init   :=
    bindV (initAdv4_1Key2 S K (.fst (.var .zero)) (.snd (.var .zero))) fun s =>
      .ret (.pair .unit (v s))
  handle := gdh1KeyHandle2 S K
  finish := gdh1KeyFinish2 S K

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

namespace SignalPqxdh.Security.ReductionDsl.KeyInd
export SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (fgKeyInd1KeyGapDhProg fgKeyInd1KeyGapDh2Prog)
end SignalPqxdh.Security.ReductionDsl.KeyInd

namespace SignalPqxdh.Security
export SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (fgKeyInd1KeyGapDhProg fgKeyInd1KeyGapDh2Prog)
end SignalPqxdh.Security
