/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Costed `ReductionDsl` Program for the One-Key `GapSigEufCma` Reduction

**Checked by Lean.** Defines `sigKeyInd1KeyProg` (and budget instantiation `sigKeyInd1KeyDslProg`)
over `pqxdhOps` and `pqSigAndDdhIface` corresponding to `sigReductionKeyInd1Key`, embedding
`gdhHandle2` via context renaming and interface lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleSpec

def Var.liftRename {S : Sig} {Γ Δ : List (Ty S)} {u t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) : Var (u :: Γ) t → Var (u :: Δ) t
  | .zero => .zero
  | .succ v => .succ (ρ v)

def Expr.rename {S : Sig} {O : Ops S} : {Γ Δ : List (Ty S)} → {t : Ty S} →
    (∀ {τ}, Var Γ τ → Var Δ τ) → Expr O Γ t → Expr O Δ t
  | _, _, _, ρ, .var v => .var (ρ v)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .bool b => .bool b
  | _, _, _, _, .nat n => .nat n
  | _, _, _, ρ, .add a b => .add (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .sub a b => .sub (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .mulK k a => .mulK k (a.rename ρ)
  | _, _, _, ρ, .divK k a => .divK k (a.rename ρ)
  | _, _, _, ρ, .modK k a => .modK k (a.rename ρ)
  | _, _, _, ρ, .lt a b => .lt (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .eqN a b => .eqN (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .not a => .not (a.rename ρ)
  | _, _, _, ρ, .and a b => .and (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .ite c a b => .ite (c.rename ρ) (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .fst a => .fst (a.rename ρ)
  | _, _, _, ρ, .snd a => .snd (a.rename ρ)
  | _, _, _, ρ, .inl a => .inl (a.rename ρ)
  | _, _, _, ρ, .inr a => .inr (a.rename ρ)
  | _, _, _, _, .none => .none
  | _, _, _, ρ, .some a => .some (a.rename ρ)
  | _, _, _, ρ, .caseOpt e n s => .caseOpt (e.rename ρ) (n.rename ρ) (s.rename (Var.liftRename ρ))
  | _, _, _, ρ, .caseSum e l r =>
    .caseSum (e.rename ρ) (l.rename (Var.liftRename ρ)) (r.rename (Var.liftRename ρ))
  | _, _, _, ρ, .letE e b => .letE (e.rename ρ) (b.rename (Var.liftRename ρ))
  | _, _, _, ρ, .op o a => .op o (a.rename ρ)
  | _, _, _, _, .nil => .nil
  | _, _, _, ρ, .cons x l => .cons (x.rename ρ) (l.rename ρ)
  | _, _, _, ρ, .len l => .len (l.rename ρ)
  | _, _, _, ρ, .take n l => .take (n.rename ρ) (l.rename ρ)
  | _, _, _, ρ, .appendL K a b => .appendL K (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .findB K l p => .findB K (l.rename ρ) (p.rename (Var.liftRename ρ))
  | _, _, _, ρ, .anyB K l p => .anyB K (l.rename ρ) (p.rename (Var.liftRename ρ))
  | _, _, _, ρ, .mapB K l f => .mapB K (l.rename ρ) (f.rename (Var.liftRename ρ))
  | _, _, _, ρ, .foldrB K l z f =>
    .foldrB K (l.rename ρ) (z.rename ρ) (f.rename (Var.liftRename (Var.liftRename ρ)))
  | _, _, _, ρ, .tconst a => .tconst (a.rename ρ)
  | _, _, _, ρ, .tget m i => .tget (m.rename ρ) (i.rename ρ)
  | _, _, _, ρ, .tset m i a => .tset (m.rename ρ) (i.rename ρ) (a.rename ρ)

def Comp.rename {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ Δ : List (Ty S)} → {t : Ty S} →
    (∀ {τ}, Var Γ τ → Var Δ τ) → Comp O I Γ t → Comp O I Δ t
  | _, _, _, ρ, .ret e => .ret (e.rename ρ)
  | _, _, _, ρ, .bind c k => .bind (c.rename ρ) (k.rename (Var.liftRename ρ))
  | _, _, _, ρ, .ite b c d => .ite (b.rename ρ) (c.rename ρ) (d.rename ρ)
  | _, _, _, ρ, .caseOpt e n s => .caseOpt (e.rename ρ) (n.rename ρ) (s.rename (Var.liftRename ρ))
  | _, _, _, ρ, .caseSum e l r =>
    .caseSum (e.rename ρ) (l.rename (Var.liftRename ρ)) (r.rename (Var.liftRename ρ))
  | _, _, _, ρ, .sample s e => .sample s (e.rename ρ)
  | _, _, _, ρ, .query g e => .query g (e.rename ρ)
  | _, _, _, ρ, .iter n e body => .iter n (e.rename ρ) (body.rename (Var.liftRename ρ))
  | _, _, _, ρ, .findM K l p => .findM K (l.rename ρ) (p.rename (Var.liftRename ρ))
  | _, _, _, ρ, .anyM K l p => .anyM K (l.rename ρ) (p.rename (Var.liftRename ρ))
  | _, _, _, ρ, .mapM K l f => .mapM K (l.rename ρ) (f.rename (Var.liftRename ρ))
  | _, _, _, ρ, .consumeFirstM K l p mk =>
    .consumeFirstM K (l.rename ρ) (p.rename (Var.liftRename ρ)) (mk.rename (Var.liftRename ρ))
  | _, _, _, ρ, .foldM K l z f =>
    .foldM K (l.rename ρ) (z.rename ρ) (f.rename (Var.liftRename (Var.liftRename ρ)))

def Env.ofRename {S : Sig} : {Γ Δ : List (Ty S)} → (∀ {τ}, Var Γ τ → Var Δ τ) → Env Δ → Env Γ
  | [], _, _, _ => .nil
  | _ :: _, _, ρ, env => .cons (env.get (ρ .zero)) (Env.ofRename (fun v => ρ (.succ v)) env)

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-! ## Interface lifters and `pqSigAndDdhIface` queries -/

abbrev s1Prim {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    Comp pqxdhOps pqSigAndDdhIface Γ τ :=
  liftBase (C := sigAndDdhOracle) c

def qSigDdhSign (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    Comp pqxdhOps pqSigAndDdhIface Γ (B 64) :=
  Comp.query (I := pqSigAndDdhIface) (.inr (.inl m)) msg

/-- Lift a `pqGapDhIface` computation into `pqSigAndDdhIface`, making zero signing queries. -/
def liftGdhToSigDdh : {Γ : List PT} → {t : PT} →
    Comp pqxdhOps pqGapDhIface Γ t → Comp pqxdhOps pqSigAndDdhIface Γ t
  | _, _, .ret e => .ret e
  | _, _, .bind c k => .bind (liftGdhToSigDdh c) (liftGdhToSigDdh k)
  | _, _, .ite b c d => .ite b (liftGdhToSigDdh c) (liftGdhToSigDdh d)
  | _, _, .caseOpt e n s => .caseOpt e (liftGdhToSigDdh n) (liftGdhToSigDdh s)
  | _, _, .caseSum e l r => .caseSum e (liftGdhToSigDdh l) (liftGdhToSigDdh r)
  | _, _, .sample s e => Comp.sample (I := pqSigAndDdhIface) s e
  | _, _, .query (Sum.inl g) e => Comp.query (I := pqSigAndDdhIface) (Sum.inl g) e
  | _, _, .query (Sum.inr ()) e => Comp.query (I := pqSigAndDdhIface) (Sum.inr (Sum.inr ())) e
  | _, _, .iter n e body => .iter n e (liftGdhToSigDdh body)
  | _, _, .findM K l p => .findM K l (liftGdhToSigDdh p)
  | _, _, .anyM K l p => .anyM K l (liftGdhToSigDdh p)
  | _, _, .mapM K l f => .mapM K l (liftGdhToSigDdh f)
  | _, _, .consumeFirstM K l p mk => .consumeFirstM K l (liftGdhToSigDdh p) mk
  | _, _, .foldM K l z f => .foldM K l z (liftGdhToSigDdh f)

def renamePair {Δ : List PT} {τ₁ τ₂ : PT} (v1 : Var Δ τ₁) (v2 : Var Δ τ₂) :
    ∀ {τ}, Var [τ₁, τ₂] τ → Var Δ τ
  | _, .zero => v1
  | _, .succ .zero => v2

/-! ## State encoding for `Sig1KeySimState` -/

/-- DSL state encoding `(fg, (targetParty, (targetPk, (signBudget, forgery))))`. -/
abbrev sig1KeyStTy : PT :=
  .prod simTy (.prod .nat (.prod (B 32) (.prod .nat (.opt (.prod (B 1569) (B 64))))))

@[reducible] def s1Fg {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) : Expr pqxdhOps Γ simTy :=
  .fst e
@[reducible] def s1Target {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd e)
@[reducible] def s1Pk {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd e))
@[reducible] def s1Budget {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) : Expr pqxdhOps Γ .nat :=
  .fst (.snd (.snd (.snd e)))
@[reducible] def s1Forgery {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) :
    Expr pqxdhOps Γ (.opt (.prod (B 1569) (B 64))) :=
  .snd (.snd (.snd (.snd e)))
@[reducible] def s1Base {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy) :
    Expr pqxdhOps Γ keyIndStateTy :=
  smBase (s1Fg e)

@[reducible] def s1Mk {Γ : List PT} (fg : Expr pqxdhOps Γ simTy)
    (target : Expr pqxdhOps Γ .nat) (pk : Expr pqxdhOps Γ (B 32))
    (budget : Expr pqxdhOps Γ .nat)
    (forgery : Expr pqxdhOps Γ (.opt (.prod (B 1569) (B 64)))) : Expr pqxdhOps Γ sig1KeyStTy :=
  .pair fg (.pair target (.pair pk (.pair budget forgery)))

@[reducible] def s1Upd {Γ : List PT} (e : Expr pqxdhOps Γ sig1KeyStTy)
    (fg : Expr pqxdhOps Γ simTy := s1Fg e)
    (budget : Expr pqxdhOps Γ .nat := s1Budget e)
    (forgery : Expr pqxdhOps Γ (.opt (.prod (B 1569) (B 64))) := s1Forgery e) :
    Expr pqxdhOps Γ sig1KeyStTy :=
  s1Mk fg (s1Target e) (s1Pk e) budget forgery

abbrev S1RS : PT := .prod keyIndRespTy sig1KeyStTy

def sig1KeyStToVal {S : Setup} (st : Sig1KeySimState S) : sig1KeyStTy.denote :=
  (simStateToVal st.fg, (st.targetParty, (st.targetPk, (st.signBudget, st.forgery))))

def encSig1KeyRS {S : Setup} (p : KeyIndResponse × Sig1KeySimState S) : S1RS.denote :=
  (keyIndRespToVal p.1, sig1KeyStToVal p.2)

/-! ## Handler branches and pre-dispatch -/

/-- Forgery extraction on an initiator bundle (`extractBundleForgeryPrim`). -/
def extract1KeyC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (bu : Var Γ₂ preKeyBundleTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.opt (.prod (B 1569) (B 64))) :=
  bindV (s1Prim (letV (s1Base (v s)) fun g => honestPeerC S K g (buIkB (v bu)))) fun peer =>
  bindV (s1Prim (qSigVerify 33
      (.pair (s1Pk (v s)) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))) fun v1 =>
  bindV (s1Prim (qSigVerify 1569
      (.pair (s1Pk (v s)) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))) fun v2 =>
  .ret (eCaseOpt (s1Forgery (v s))
    (eCaseOpt (v peer) .none fun k =>
      .ite (natEq (v k) (s1Target (v s)))
        (.ite (.and (v v1) (.not (eAny K (stSpks (s1Base (v s))) fun e =>
            .and (natEq (.fst (.fst (v e))) (v k)) (eqB (sbSpkPk (.snd (v e))) (buSpkB (v bu))))))
          (.some (.pair (widenEC (encEC (buSpkB (v bu)))) (buSpkSig (v bu))))
          (.ite (.and (v v2) (.not (eAny K (stSpks (s1Base (v s))) fun e =>
              .and (natEq (.fst (.fst (v e))) (v k))
                (eqB (sbPqspkPk (.snd (v e))) (buPqspkB (v bu))))))
            (.some (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu))))
            .none))
        .none)
    fun fg => .some (v fg))

/-- `.initPrin u` branch of `sig1KeyStep`, planting `(targetPk, targetPk)` when `u == targetParty`. -/
def sig1KeyInitPrinB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (u : Var Γ₂ .nat) :
    Comp pqxdhOps pqSigAndDdhIface Δ S1RS :=
  .ite (eAny K (stPrin (s1Base (v s))) fun e => natEq (.fst (v e)) (v u))
    (.ret (.pair rNone (v s))) <|
  bindV (s1Prim sBytes32) fun s0 =>
  bindV (s1Prim (qX25519Base (v s0))) fun ik =>
  let isTgt := natEq (v u) (s1Target (v s))
  let sec := Expr.ite isTgt (litB 32 []) (v s0)
  let pk := Expr.ite isTgt (s1Pk (v s)) (v ik)
  .ret (.pair (rInitPrin pk pk)
    (s1Upd (v s) (fg := smUpd (s1Fg (v s))
      (base := stUpd (s1Base (v s))
        (prin := .cons (.pair (v u) (peMk sec pk sec pk (.bool false)))
          (stPrin (s1Base (v s))))))))

/-- Target `.genSPK u j` branch of `sig1KeyStep`, signing SPK and PQSPK via `qSigDdhSign`. -/
def sig1KeyTargetGenSpkB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ (.prod .nat .nat)) :
    Comp pqxdhOps pqSigAndDdhIface Δ S1RS :=
  .ite (eAny K (stSpks (s1Base (v s))) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair rNone (v s))) <|
  caseOptV (eFind K (stPrin (s1Base (v s))) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair rNone (v s))) fun uE =>
  .ite (natEq (s1Budget (v s)) (.nat 0)) (.ret (.pair rNone (v s))) <|
  bindV (s1Prim sBytes32) fun spkSk =>
  bindV (s1Prim (qX25519Base (v spkSk))) fun spkPk =>
  bindV (qSigDdhSign 33 (encEC (v spkPk))) fun sig1 =>
  bindV (s1Prim sRandom64) fun seed =>
  bindV (s1Prim (qKemKeyGen (v seed))) fun kp =>
  bindV (qSigDdhSign 1569 (encKEM (.fst (v kp)))) fun sig2 =>
  .ret (.pair (rBundle (buMk (peIkAPk (.snd (v uE))) (u32OfNat (.snd (v x))) (v spkPk) (v sig1)
      .none (u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (s1Upd (v s)
      (fg := smUpd (s1Fg (v s))
        (base := stUpd (s1Base (v s)) (spks := .cons (.pair (v x) (sbMk (v spkSk) (v spkPk)
          (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.bool false))) (stSpks (s1Base (v s))))))
      (budget := .sub (s1Budget (v s)) (.nat 1))))

/-- `.initiateOPK` / `.initiateNoOPK` forgery check before delegating to `delegateFgC`. -/
def sig1KeyInitiateCheckC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ initQTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1RS .unit) :=
  letV (.snd (.snd (v x))) fun bu =>
  bindV (extract1KeyC S K s bu) fun fg =>
  .ite (isSomeE (v fg))
    (.ret (.inl (.pair rNone (s1Upd (v s) (forgery := v fg)))))
    (.ret (.inr .unit))

/-- Pre-dispatch for `sig1KeyHandleC`, handling frozen states, `.initPrin`, target `.genSPK`, and
    extracted `.initiate*` forgeries directly. -/
def sig1KeyPreDispatchC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.sum S1RS .unit) :=
  .ite (isSomeE (s1Forgery (v s))) (.ret (.inl (.pair rNone (v s)))) <|
  caseSumV (v q) (fun u => bindV (sig1KeyInitPrinB K s u) fun r => .ret (.inl (v r))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .ite (natEq (.fst (v x)) (s1Target (v s)))
      (bindV (sig1KeyTargetGenSpkB K s x) fun r => .ret (.inl (v r)))
      (.ret (.inr .unit))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q) (fun x => sig1KeyInitiateCheckC S K s x) fun q =>
  caseSumV (v q) (fun x => sig1KeyInitiateCheckC S K s x) fun _ =>
  .ret (.inr .unit)

def pa2Zero {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ params2Ty :=
  pa2Mk (litB 32 []) pk (litB 32 []) .none (.bool false) .none .none (.bool false) .none (.nat 1)

def pa2ZeroVal (pk : Bytes) : params2Ty.denote :=
  ([], (pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))

/-- Delegate `q` to `gdhHandle2 S K` lifted into `pqSigAndDdhIface`. -/
def delegateFgC (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ S1RS :=
  letV (.pair (pa2Zero (s1Pk (v s))) (s1Fg (v s))) fun gdhSt =>
  bindV (liftGdhToSigDdh ((gdhHandle2 S K).rename (renamePair gdhSt (.succ (Ext.wk q))))) fun r =>
  .ret (.pair (.fst (v r)) (s1Upd (v s) (fg := .snd (.snd (v r)))))

def sig1KeyHandleC (S : Setup) (K : Nat) :
    Comp pqxdhOps pqSigAndDdhIface [sig1KeyStTy, keyIndQueryTy] S1RS :=
  let s : Var [sig1KeyStTy, keyIndQueryTy] sig1KeyStTy := .zero
  let q : Var [sig1KeyStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  bindV (sig1KeyPreDispatchC S K s q) fun pre =>
  caseSumV (v pre) (fun res => .ret (v res)) fun _ =>
  delegateFgC S K s q

/-! ## `CostedReduction` program -/

/-- `CostedReduction` program for `sigReductionKeyInd1Key S b` with loop bound `K`. -/
def sigKeyInd1KeyProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (keyIndSpec S) (keyIndCodec S)
      (B 32) .unit .bool (.prod (B 1569) (B 64)) where
  σ := sig1KeyStTy
  init :=
    bindV (s1Prim (sIndex S.N_id)) fun k =>
    bindV (s1Prim sBool) fun secb =>
    .ret (.pair .unit
      (s1Mk (emptySimE (v secb)) (v k) (.var (.succ (.succ .zero)))
        (.nat (min K (min S.N_spk_tot S.N_recv))) .none))
  handle := sig1KeyHandleC S K
  finish :=
    .ret (eCaseOpt (s1Forgery (.var .zero)) (.pair (litB 1569 []) (litB 64 [])) fun fg => v fg)

abbrev sigKeyInd1KeyDslProg (S : Setup) (b : QueryBudget) :=
  sigKeyInd1KeyProg S b.q_total

/-! ## Clamped `signBudget` agreement -/

private theorem sig1KeyStep_signBudget_min_eq {S : Setup} (K n : Nat) (q : KeyIndQuery S)
    (st₁ st₂ : Sig1Key.Sig1KeySimState S)
    (hfg : st₁.fg = st₂.fg) (htp : st₁.targetParty = st₂.targetParty)
    (hpk : st₁.targetPk = st₂.targetPk) (hfo : st₁.forgery = st₂.forgery)
    (hb : min (n + 1) st₁.signBudget = min (n + 1) st₂.signBudget) :
    (Prod.map id (fun s => { s with signBudget := min n s.signBudget })) <$>
        Sig1Key.sig1KeyStep S K q st₁ =
      (Prod.map id (fun s => { s with signBudget := min n s.signBudget })) <$>
        Sig1Key.sig1KeyStep S K q st₂ := by
  rcases st₁ with ⟨fg, tp, pk, b₁, fo⟩
  rcases st₂ with ⟨fg₂, tp₂, pk₂, b₂, fo₂⟩
  dsimp only at hfg htp hpk hfo hb
  subst hfg; subst htp; subst hpk; subst hfo
  rcases b₁ with _ | b₁'
  · have hb₂ : b₂ = 0 := by omega
    subst hb₂
    rfl
  · rcases b₂ with _ | b₂'
    · omega
    · have hEq0 : min n (b₁' + 1) = min n (b₂' + 1) := by omega
      have hEq1 : min n b₁' = min n b₂' := by omega
      unfold Sig1Key.sig1KeyStep
      by_cases hFo : fo.isSome = true
      · simp [hFo, Prod.map, hEq0]
      · simp only [hFo, Bool.false_eq_true, ↓reduceIte]
        cases q with
        | initPrin u =>
          by_cases hAny : (fg.base.principals.any fun x => x.1 == u.val) = true
          · simp [hAny, Prod.map, hEq0]
          · simp only [hAny, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc,
              Function.comp_def, pure_bind, Prod.map, id]
            simp only [hEq0]
        | genSPK u j =>
          by_cases hT : (u.val == tp) = true
          · simp only [hT, ↓reduceIte]
            by_cases hAny : (fg.base.spkBundles.any fun x => x.1 == (u.val, j.val)) = true
            · simp [hAny, Prod.map, hEq0]
            · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
              cases hFind : fg.base.principals.find? fun x => x.1 == u.val with
              | none => simp [Prod.map, hEq0]
              | some p =>
                rcases p with ⟨idx, uEntry⟩
                simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
                  Prod.map, id, hEq1]
          · simp only [hT, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc,
              Function.comp_def, pure_bind, Prod.map, id, hEq0]
        | initiateOPK u i bu =>
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
          refine bind_congr fun fgOpt => ?_
          by_cases hS : fgOpt.isSome = true
          · simp [hS, Prod.map, hEq0]
          · simp [hS, Prod.map, hEq0]
        | initiateNoOPK u i bu =>
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
          refine bind_congr fun fgOpt => ?_
          by_cases hS : fgOpt.isSome = true
          · simp [hS, Prod.map, hEq0]
          · simp [hS, Prod.map, hEq0]
        | corruptIK _ | genOPK _ _ _ | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _
        | testSession _ | roQuery _ | revealDhSecrets | revealSessionKey _
        | registerKey _ | revealSpkSk _ _ =>
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
            Prod.map, id, hEq0]

theorem runWithSigDdhStep_sig1KeyStep_zeroBudget_eq {S : Setup} {α : Type} (K : Nat)
    (mx : OracleComp (unifSpec + keyIndSpec S) α) :
    ∀ (m : Nat) (st₁ st₂ : Sig1Key.Sig1KeySimState S),
      mx.IsQueryBoundP (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) m →
      st₁.fg = st₂.fg → st₁.targetParty = st₂.targetParty →
      st₁.targetPk = st₂.targetPk → st₁.forgery = st₂.forgery →
      min m st₁.signBudget = min m st₂.signBudget →
      (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) mx st₁ =
        (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) mx st₂ := by
  induction mx using OracleComp.inductionOn with
  | pure x =>
    intro m st₁ st₂ _ hfg htp hpk hfo _
    rcases st₁ with ⟨fg, tp, pk, b₁, fo⟩
    rcases st₂ with ⟨fg₂, tp₂, pk₂, b₂, fo₂⟩
    dsimp only at hfg htp hpk hfo
    subst hfg; subst htp; subst hpk; subst hfo
    rfl
  | query_bind q r ih =>
    intro m st₁ st₂ hB hfg htp hpk hfo hb
    rw [isQueryBoundP_query_bind_iff] at hB
    rcases q with n | gq
    · change (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          (liftM (OracleSpec.query (spec := Sig1Key.SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
            fun u => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r u) st₁) =
        (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          (liftM (OracleSpec.query (spec := Sig1Key.SigDdhSimSpec) (Sum.inl (Sum.inl n))) >>=
            fun u => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r u) st₂)
      simp only [map_bind]
      refine bind_congr fun u => ih u m st₁ st₂ (by simpa using hB.2 u) hfg htp hpk hfo hb
    · have hPos : 0 < m := hB.1.resolve_left (by simp)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      change (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          (Sig1Key.sig1KeyStep S K gq st₁ >>=
            fun p => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2) =
        (Prod.map id (fun s => { s with signBudget := 0 })) <$>
          (Sig1Key.sig1KeyStep S K gq st₂ >>=
            fun p => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2)
      let clamp (s : Sig1Key.Sig1KeySimState S) : Sig1Key.Sig1KeySimState S :=
        { s with signBudget := min m' s.signBudget }
      have hClamp (p : (keyIndSpec S).Range gq × Sig1Key.Sig1KeySimState S) :
          (Prod.map id (fun s => { s with signBudget := 0 })) <$>
              Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2 =
            (Prod.map id (fun s => { s with signBudget := 0 })) <$>
              Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) (clamp p.2) :=
        ih p.1 m' p.2 (clamp p.2) (by simpa using hB.2 p.1) rfl rfl rfl rfl (by simp [clamp])
      have hStep := sig1KeyStep_signBudget_min_eq K m' gq st₁ st₂ hfg htp hpk hfo hb
      calc
        (Prod.map id (fun s => { s with signBudget := 0 })) <$>
            (Sig1Key.sig1KeyStep S K gq st₁ >>=
              fun p => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2)
          = Sig1Key.sig1KeyStep S K gq st₁ >>= fun p =>
              (Prod.map id (fun s => { s with signBudget := 0 })) <$>
                Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) (clamp p.2) := by
              simp only [map_bind]
              exact bind_congr hClamp
        _ = ((Prod.map id clamp) <$> Sig1Key.sig1KeyStep S K gq st₁) >>= fun p =>
              (Prod.map id (fun s => { s with signBudget := 0 })) <$>
                Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2 := by
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
                Prod.map, id]
        _ = ((Prod.map id clamp) <$> Sig1Key.sig1KeyStep S K gq st₂) >>= fun p =>
              (Prod.map id (fun s => { s with signBudget := 0 })) <$>
                Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2 := by
              rw [hStep]
        _ = Sig1Key.sig1KeyStep S K gq st₂ >>= fun p =>
              (Prod.map id (fun s => { s with signBudget := 0 })) <$>
                Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) (clamp p.2) := by
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
                Prod.map, id]
        _ = (Prod.map id (fun s => { s with signBudget := 0 })) <$>
            (Sig1Key.sig1KeyStep S K gq st₂ >>=
              fun p => Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) (r p.1) p.2) := by
              simp only [map_bind]
              exact bind_congr fun p => (hClamp p).symm

theorem runWithSigDdhStep_sig1KeyStep_forgery_eq {S : Setup} {α : Type} (K : Nat)
    (mx : OracleComp (unifSpec + keyIndSpec S) α) (st : Sig1Key.Sig1KeySimState S)
    (hB : mx.IsQueryBoundP (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K) :
    (do let (_, finalSt) ←
          Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) mx
            { st with signBudget := min K st.signBudget }
        return finalSt.forgery.getD ([], [])) =
      (do let (_, finalSt) ← Sig1Key.runWithSigDdhStep (Sig1Key.sig1KeyStep S K) mx st
          return finalSt.forgery.getD ([], [])) := by
  have h := congrArg (Functor.map (fun p : α × Sig1Key.Sig1KeySimState S => p.2.forgery.getD ([], [])))
    (runWithSigDdhStep_sig1KeyStep_zeroBudget_eq K mx K
      { st with signBudget := min K st.signBudget } st hB rfl rfl rfl rfl (by simp))
  simpa only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, Prod.map] using h

end SignalPqxdh.Security.ReductionDsl.KeyInd
