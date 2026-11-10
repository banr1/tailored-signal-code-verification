/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSig -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec -- proof-setup: allow-public-import

/-!
# Shadow-Indexed `Auth` Simulator State, Dispatcher, and Clamped Arms

Defines clamped per-kind loop fuels (`AuthKindFuels`), AVL-backed random-oracle shadow states and
simulation relations (`AuthBaseShadowRel`, `AuthFixedShadowRel`), and the 12-way outer query
dispatcher (`dispatchAuthQ`) for the kind-split one-key `Auth` reductions. Also provides clamped
base wrappers, `O(log cap)` shadow RO arms, and post-step AVL head synchronization (`syncRoBothC`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK

open OracleSpec OracleComp
open _root_.SignalPqxdh (Setup QueryBudget Bytes AuthQuery)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  AtomicPureOp B PB drKeyT bits
)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift AtomicIface embedTy embedVal mapExpr mapComp mapSamp exprRename compRename
  tlAuthPrim tlAuthSigDdh tlPrfMk tlPrfHmac
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlTy avlEmptyE dfltB192E dfltPair32E dfltDrKeyE dfltPbytesPair32E
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec (
  AvlB192Valid AvlPair32Valid avlEmptyE_b192_valid avlEmptyE_pair32_valid
)

/-- Clamped per-kind loop fuels and AVL table capacity for the kind-split one-key `Auth` reductions. -/
structure AuthKindFuels where
  M_on   : ℕ
  M_off  : ℕ
  M_dh   : ℕ
  M_sess : ℕ
  K_on   : ℕ
  K_on1  : ℕ
  K_ro   : ℕ
  K_cap  : ℕ
  deriving DecidableEq, Repr

/-- Canonical clamped fuel bundle computed from `(S, b)`. -/
@[expose] def AuthKindFuels.ofBudget (S : Setup) (b : QueryBudget) : AuthKindFuels :=
  let mOn  := min b.q_on b.q_total
  let mOff := min (b.q_ro + b.q_roRoot) b.q_total
  { M_on   := mOn
    M_off  := mOff
    M_dh   := min mOn S.N_dh
    M_sess := min mOn S.N_sess_tot
    K_on   := min b.q_total mOn
    K_on1  := min b.q_total (mOn + 1)
    K_ro   := min b.q_total (mOff + mOn)
    K_cap  := mOff + 2 * mOn + 1 }

theorem AuthKindFuels.K_on_le_q_total (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_on ≤ b.q_total :=
  Nat.min_le_left _ _

@[simp] theorem AuthKindFuels.K_on_eq_M_on (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_on = (AuthKindFuels.ofBudget S b).M_on := by
  simp only [AuthKindFuels.ofBudget]
  omega

theorem AuthKindFuels.K_on1_le_q_total (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_on1 ≤ b.q_total :=
  Nat.min_le_left _ _

theorem AuthKindFuels.K_ro_le_q_total (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_ro ≤ b.q_total :=
  Nat.min_le_left _ _

theorem AuthKindFuels.K_ro_le_sum (S : Setup) (b : QueryBudget) :
    (AuthKindFuels.ofBudget S b).K_ro ≤
      (AuthKindFuels.ofBudget S b).M_off + (AuthKindFuels.ofBudget S b).M_on :=
  Nat.min_le_right _ _

@[simp] theorem AuthKindFuels.min_K_on_N_dh (S : Setup) (b : QueryBudget) :
    min (AuthKindFuels.ofBudget S b).K_on S.N_dh = (AuthKindFuels.ofBudget S b).M_dh := by
  simp only [AuthKindFuels.ofBudget]
  omega

@[simp] theorem AuthKindFuels.min_K_on_N_sess_tot (S : Setup) (b : QueryBudget) :
    min (AuthKindFuels.ofBudget S b).K_on S.N_sess_tot = (AuthKindFuels.ofBudget S b).M_sess := by
  simp only [AuthKindFuels.ofBudget]
  omega

@[reducible, expose] def roAvlTy : Ty pqAtomicSig :=
  avlTy (B 192) (drKeyT (ℓ := 0) (Pt := Empty))

@[reducible, expose] def roRootAvlTy : Ty pqAtomicSig :=
  avlTy (.prod (B 32) (B 32)) (.prod (PB 32) (PB 32))

@[reducible, expose] def roBothAvlTy : Ty pqAtomicSig :=
  .prod roAvlTy roRootAvlTy

@[reducible, expose] def roListAtomicTy : Ty pqAtomicSig :=
  .list (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))

@[reducible, expose] def roRootListAtomicTy : Ty pqAtomicSig :=
  .list (.prod (.prod (PB 32) (PB 32)) (.prod (PB 32) (PB 32)))

@[expose] def emptyRoAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ roAvlTy :=
  avlEmptyE dfltB192E dfltDrKeyE

@[expose] def emptyRoRootAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ roRootAvlTy :=
  avlEmptyE dfltPair32E dfltPbytesPair32E

@[expose] def emptyRoBothAvlE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ roBothAvlTy :=
  .pair emptyRoAvlE emptyRoRootAvlE

@[expose] def wk1 {x y : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)} :
    Var [x] y → Var (x :: Γ) y
  | .zero => .zero

@[expose] def wk2 {x z y : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)} :
    Var [x, z] y → Var (x :: z :: Γ) y
  | .zero => .zero
  | .succ .zero => .succ .zero

@[expose] def liftExpr1 {a b : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a] b)
    (argE : Expr pqAtomicOps Γ (embedTy a)) :
    Expr pqAtomicOps Γ (embedTy b) :=
  .letE argE (exprRename wk1 (mapExpr e : Expr pqAtomicOps [embedTy a] (embedTy b)))

@[expose] def liftExpr2 {a b c : Ty _root_.SignalPqxdh.LegacyCosted.pqSig}
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr _root_.SignalPqxdh.LegacyCosted.pqxdhOps [a, b] c)
    (arg0 : Expr pqAtomicOps Γ (embedTy a))
    (arg1 : Expr pqAtomicOps Γ (embedTy b)) :
    Expr pqAtomicOps Γ (embedTy c) :=
  .letE arg1 (.letE (exprRename Var.succ arg0)
    (exprRename wk2 (mapExpr e : Expr pqAtomicOps [embedTy a, embedTy b] (embedTy c))))

@[reducible, expose] def authBaseAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.authStateTy

@[reducible, expose] def authFixedAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy

@[reducible, expose] def authBaseShadowStTy : Ty pqAtomicSig :=
  .prod authBaseAtomicTy roBothAvlTy

@[reducible, expose] def authFixedShadowStTy : Ty pqAtomicSig :=
  .prod authFixedAtomicTy roBothAvlTy

@[expose] def forgetAuthBaseShadow (s : authBaseShadowStTy.denote) : authBaseAtomicTy.denote :=
  s.1

@[expose] def forgetAuthBaseShadowE {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ authBaseShadowStTy) : Expr pqAtomicOps Γ authBaseAtomicTy :=
  .fst e

@[expose] def forgetAuthFixedShadow (s : authFixedShadowStTy.denote) : authFixedAtomicTy.denote :=
  s.1

@[expose] def forgetAuthFixedShadowE {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ authFixedShadowStTy) : Expr pqAtomicOps Γ authFixedAtomicTy :=
  .fst e

@[expose] def baseRoCacheE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) : Expr pqAtomicOps Γ roListAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stRo
      (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.authStateTy]) (.var .vz))
    stE

@[expose] def baseRootRoCacheE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy) : Expr pqAtomicOps Γ roRootListAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stRoot
      (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.authStateTy]) (.var .vz))
    stE

@[expose] def fixedRoCacheE {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) : Expr pqAtomicOps Γ roListAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRoCache
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid
          (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy])
          (.var .vz))))
    fhstE

@[expose] def fixedRootRoCacheE {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) : Expr pqAtomicOps Γ roRootListAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asRootRoCache
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid
          (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy])
          (.var .vz))))
    fhstE

/-- Representation invariant linking `roBoth` to the chronological `asRoCache` and `asRootRoCache`
    association lists. -/
structure AuthRoBothValid (cap : ℕ)
    (roBoth : roBothAvlTy.denote)
    (roList : roListAtomicTy.denote)
    (rootList : roRootListAtomicTy.denote) : Prop where
  ro_valid : AvlB192Valid cap roBoth.1 roList
  root_valid : AvlPair32Valid cap roBoth.2 rootList

/-- Forgetful shadow simulation relation on `authBaseShadowStTy` mirroring `(stRo, stRoot)`. -/
structure AuthBaseShadowRel (cap : ℕ)
    (sShadow : authBaseShadowStTy.denote)
    (sLegacy : authBaseAtomicTy.denote) : Prop where
  forget_eq : forgetAuthBaseShadow sShadow = sLegacy
  ro_both_valid : AuthRoBothValid cap sShadow.2
    ((baseRoCacheE (Γ := [authBaseAtomicTy]) .v0).eval (.cons sLegacy .nil))
    ((baseRootRoCacheE (Γ := [authBaseAtomicTy]) .v0).eval (.cons sLegacy .nil))

/-- Forgetful shadow simulation relation on `authFixedShadowStTy` mirroring `(asRoCache, asRootRoCache)`. -/
structure AuthFixedShadowRel (cap : ℕ)
    (sShadow : authFixedShadowStTy.denote)
    (sLegacy : authFixedAtomicTy.denote) : Prop where
  forget_eq : forgetAuthFixedShadow sShadow = sLegacy
  ro_both_valid : AuthRoBothValid cap sShadow.2
    ((fixedRoCacheE (Γ := [authFixedAtomicTy]) .v0).eval (.cons sLegacy .nil))
    ((fixedRootRoCacheE (Γ := [authFixedAtomicTy]) .v0).eval (.cons sLegacy .nil))

theorem emptyRoBothAvlE_valid {Γ : List (Ty pqAtomicSig)} (cap : ℕ) (ρ : Env Γ) :
    AuthRoBothValid cap (emptyRoBothAvlE.eval ρ) [] [] :=
  ⟨avlEmptyE_b192_valid cap dfltDrKeyE ρ, avlEmptyE_pair32_valid cap dfltPbytesPair32E ρ⟩

@[reducible, expose] def authQueryAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.authQueryTy

@[reducible, expose] def authSendQAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.sendQTy

@[reducible, expose] def authRecvQAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.recvQTy

@[reducible, expose] def authRespAtomicTy : Ty pqAtomicSig :=
  embedTy _root_.SignalPqxdh.Security.ReductionDsl.authRespTy

/-- Outermost 12-way constructor dispatcher routing each `AuthQuery S` tag directly to its handler
    arm before any effectful bind. -/
@[expose] def dispatchAuthQ {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig}
    (qE : Expr pqAtomicOps Γ authQueryAtomicTy)
    (armInitPrin   : Comp pqAtomicOps I (.nat :: Γ) out)
    (armCorrupt    : Comp pqAtomicOps I (.nat :: Γ) out)
    (armGenSpk     : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
    (armGenOpk     : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
    (armSendOpk    : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
    (armSendNoOpk  : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
    (armRecvOpk    : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
    (armRecvNoOpk  : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
    (armRo         : Comp pqAtomicOps I (PB 192 :: Γ) out)
    (armRoRoot     : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
    (armRevealDh   : Comp pqAtomicOps I (.unit :: Γ) out)
    (armRegister   : Comp pqAtomicOps I (PB 32 :: Γ) out) :
    Comp pqAtomicOps I Γ out :=
  let wk {a t : Ty pqAtomicSig} {Δ : List (Ty pqAtomicSig)}
      (h : ∀ {x}, Var Γ x → Var Δ x) : Var (a :: Γ) t → Var (a :: Δ) t
    | .zero => .zero
    | .succ v => .succ (h v)
  let s1 {a x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: Γ) x := .succ v
  let s2 {a b x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: Γ) x := .succ (s1 v)
  let s3 {a b c x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: Γ) x := .succ (s2 v)
  let s4 {a b c d x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: Γ) x := .succ (s3 v)
  let s5 {a b c d e x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: Γ) x := .succ (s4 v)
  let s6 {a b c d e f x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: f :: Γ) x := .succ (s5 v)
  let s7 {a b c d e f g x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: f :: g :: Γ) x := .succ (s6 v)
  let s8 {a b c d e f g h x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: f :: g :: h :: Γ) x := .succ (s7 v)
  let s9 {a b c d e f g h i x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: f :: g :: h :: i :: Γ) x := .succ (s8 v)
  let s10 {a b c d e f g h i j x : Ty pqAtomicSig} (v : Var Γ x) : Var (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: Γ) x := .succ (s9 v)
  .caseSum qE
    armInitPrin
    (.caseSum .v0
      (compRename (wk s1) armCorrupt)
      (.caseSum .v0
        (compRename (wk s2) armGenSpk)
        (.caseSum .v0
          (compRename (wk s3) armGenOpk)
          (.caseSum .v0
            (compRename (wk s4) armSendOpk)
            (.caseSum .v0
              (compRename (wk s5) armSendNoOpk)
              (.caseSum .v0
                (compRename (wk s6) armRecvOpk)
                (.caseSum .v0
                  (compRename (wk s7) armRecvNoOpk)
                  (.caseSum .v0
                    (compRename (wk s8) armRo)
                    (.caseSum .v0
                      (compRename (wk s9) armRoRoot)
                      (.caseSum .v0
                        (compRename (wk s10) armRevealDh)
                        (compRename (wk s10) armRegister)))))))))))

section ClampedHsWrappers

open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy preKeyBundleTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext v bindV eAny natEq RS stPrin rs aNone aInitPrin stUpd peMk
)

/-- One-key `initPrin` simulator arm parameterized by explicit loop fuel `K`. -/
@[expose] def initPrin1KeyFuelB (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun s0 => bindV (.queryPrim .x25519Base (v s0)) fun ik =>
  .ret (rs (aInitPrin (v ik) (v ik)) (stUpd (v st) (prin := .listCons
    (.pair (v u) (peMk (v s0) (v ik) (v s0) (v ik) (.litBool false))) (stPrin (v st)))))

@[expose] def initPrin1KeyKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  initPrin1KeyFuelB F.K_on st u

@[expose] def corruptKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.corruptB F.K_on st u

@[expose] def genOpkKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genOpkB F.K_on st x

@[expose] def genSpkKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.genSpkB F.K_on st x

@[expose] def registerKB {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy)
    (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.registerB st sk

@[expose] def extractKC (S : Setup) (F : AuthKindFuels) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (tp : Var Γ₁ .nat)
    (tpk : Var Γ₂ (B 32))
    (st : Var Γ₃ authStateTy)
    (bu : Var Γ₄ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod (B 1569) (B 64))) :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.extractC S F.K_on tp tpk st bu

end ClampedHsWrappers

section ClampedFixedWrappers

open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (
  Ext authHybridStateTy authHybridStateFixedTy RSF
)

@[expose] def initPrin1KeyFixedKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.initPrin1KeyFixedB F.K_on fhst u

@[expose] def corruptFixedKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.corruptFixedB F.K_on fhst u

@[expose] def genSpkFixedKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genSpkFixedB F.K_on fhst x

@[expose] def genOpkFixedKB (F : AuthKindFuels) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.genOpkFixedB F.K_on fhst x

@[expose] def registerFixedKB {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.registerFixedB fhst sk

@[expose] def finalizeAuthFixedKDsl (S : Setup) (F : AuthKindFuels) {Γ : List (Ty pqSig)} :
    Comp pqxdhOps pqPrimIface (authHybridStateTy :: .bool :: .bool :: Γ) .bool :=
  _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.finalizeAuthFixedDsl S F.K_on

end ClampedFixedWrappers

section ShadowRoAndSync

@[expose] def aNoneAtomicE {Γ : List (Ty pqAtomicSig)} : Expr pqAtomicOps Γ authRespAtomicTy :=
  .inl .unit

@[expose] def aDrKeyAtomicE {Γ : List (Ty pqAtomicSig)}
    (dkE : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) :
    Expr pqAtomicOps Γ authRespAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aDrKey
      (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.drKeyTy]) (.var .vz))
    dkE

@[expose] def aRootKdfAtomicE {Γ : List (Ty pqAtomicSig)}
    (rkCkE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Expr pqAtomicOps Γ authRespAtomicTy :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.aRootKdf
      (Γ := [.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 32)])
      (.fst (.var .vz)) (.snd (.var .vz)))
    rkCkE

@[expose] def baseSetRoCacheE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy)
    (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    Expr pqAtomicOps Γ authBaseAtomicTy :=
  let RoTy := Ty.list (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
    _root_.SignalPqxdh.Security.ReductionDsl.drKeyTy)
  liftExpr2
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd
      (Γ := [RoTy, _root_.SignalPqxdh.Security.ReductionDsl.authStateTy])
      (.var (.vs .vz)) (ro := .var .vz))
    roE stE

@[expose] def baseSetRootRoCacheE {Γ : List (Ty pqAtomicSig)}
    (stE : Expr pqAtomicOps Γ authBaseAtomicTy)
    (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    Expr pqAtomicOps Γ authBaseAtomicTy :=
  let B32 := _root_.SignalPqxdh.LegacyCosted.B 32
  let RootTy := Ty.list (.prod (.prod B32 B32) (.prod B32 B32))
  liftExpr2
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.stUpd
      (Γ := [RootTy, _root_.SignalPqxdh.Security.ReductionDsl.authStateTy])
      (.var (.vs .vz)) (root := .var .vz))
    rootE stE

@[expose] def fixedHasWonE {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy) : Expr pqAtomicOps Γ .bool :=
  liftExpr1
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.asHasWonAuth
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid
          (Γ := [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy])
          (.var .vz))))
    fhstE

@[expose] def fixedSetRoCacheE {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy)
    (roE : Expr pqAtomicOps Γ roListAtomicTy) :
    Expr pqAtomicOps Γ authFixedAtomicTy :=
  let RoTy := Ty.list (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.drKeyTy)
  liftExpr2
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.fhstSetBase
      (Γ := [RoTy, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy])
      (.var (.vs .vz))
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid (.var (.vs .vz))))
        (ro := .var .vz)))
    roE fhstE

@[expose] def fixedSetRootRoCacheE {Γ : List (Ty pqAtomicSig)}
    (fhstE : Expr pqAtomicOps Γ authFixedAtomicTy)
    (rootE : Expr pqAtomicOps Γ roRootListAtomicTy) :
    Expr pqAtomicOps Γ authFixedAtomicTy :=
  let B32 := _root_.SignalPqxdh.LegacyCosted.B 32
  let RootTy := Ty.list (.prod (.prod B32 B32) (.prod B32 B32))
  liftExpr2
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.fhstSetBase
      (Γ := [RootTy, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authHybridStateFixedTy])
      (.var (.vs .vz))
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.stUpd
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsBase
          (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.ahsfHybrid (.var (.vs .vz))))
        (root := .var .vz)))
    rootE fhstE

/-- `O(log cap)` shadow RO lookup-or-sample step on `(roList, roAvl)` for `PB 192 → drKeyT`. -/
@[expose] def roShadowStepC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps A.toIface Γ
      (.prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod roListAtomicTy roAvlTy)) :=
  .bind (.ret (.pair roListE (.pair tblE (.pair secE (aop (.pbytesToBytes 192) secE)))))
    (.bind (avlSearchB192C cap (.fst (.snd .v0)) (.snd (.snd (.snd .v0))))
      (.caseOpt (.fst .v0)
        (.bind (mapSamp A .drKey96)
          (.bind (avlInsertAtPathC cap
              (.fst (.snd .v2))
              (.snd .v1)
              (.snd (.snd (.snd .v2)))
              .v0)
            (.ret (.pair .v1
              (.pair (.cons (.pair (.fst (.snd (.snd .v3))) .v1) (.fst .v3)) .v0)))))
        (.ret (.pair .v0 (.pair (.fst .v2) (.fst (.snd .v2)))))))

/-- `O(log cap)` shadow root-RO lookup-or-sample step on `(rootList, roRootAvl)`. -/
@[expose] def roRootShadowStepC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Comp pqAtomicOps A.toIface Γ
      (.prod (.prod (PB 32) (PB 32)) (.prod roRootListAtomicTy roRootAvlTy)) :=
  let keyPairE : Expr pqAtomicOps Γ (.prod (B 32) (B 32)) :=
    .letE inpE (.pair (aop (.pbytesToBytes 32) (.fst .v0)) (aop (.pbytesToBytes 32) (.snd .v0)))
  .bind (.ret (.pair rootListE (.pair tblE (.pair inpE keyPairE))))
    (.bind (avlSearchPair32C cap (.fst (.snd .v0)) (.snd (.snd (.snd .v0))))
      (.caseOpt (.fst .v0)
        (.bind (.bind (mapSamp A .bytes32) (.bind (mapSamp A .bytes32) (.ret (.pair .v1 .v0))))
          (.bind (avlInsertAtPathC cap
              (.fst (.snd .v2))
              (.snd .v1)
              (.snd (.snd (.snd .v2)))
              .v0)
            (.ret (.pair .v1
              (.pair (.cons (.pair (.fst (.snd (.snd .v3))) .v1) (.fst .v3)) .v0)))))
        (.ret (.pair .v0 (.pair (.fst .v2) (.fst (.snd .v2)))))))

@[expose] def roBaseShadowArmC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps A.toIface Γ (.prod authRespAtomicTy authBaseShadowStTy) :=
  .bind (.ret (.pair sE secE))
    (.bind (roShadowStepC A cap (baseRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0))
      (.ret (.pair (aDrKeyAtomicE (.fst .v0))
        (.pair (baseSetRoCacheE (.fst (.fst .v1)) (.fst (.snd .v0)))
          (.pair (.snd (.snd .v0)) (.snd (.snd (.fst .v1))))))))

@[expose] def roRootBaseShadowArmC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Comp pqAtomicOps A.toIface Γ (.prod authRespAtomicTy authBaseShadowStTy) :=
  .bind (.ret (.pair sE inpE))
    (.bind (roRootShadowStepC A cap
        (baseRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0))
      (.ret (.pair (aRootKdfAtomicE (.fst .v0))
        (.pair (baseSetRootRoCacheE (.fst (.fst .v1)) (.fst (.snd .v0)))
          (.pair (.fst (.snd (.fst .v1))) (.snd (.snd .v0)))))))

/-- `O(log cap)` `.roQuery` arm on `authFixedShadowStTy` with `asHasWonAuth` short-circuit. -/
@[expose] def roFixedShadowArmC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    Comp pqAtomicOps A.toIface Γ (.prod authRespAtomicTy authFixedShadowStTy) :=
  .bind (.ret (.pair fsE secE))
    (.ite (fixedHasWonE (.fst (.fst .v0)))
      (.ret (.pair aNoneAtomicE (.fst .v0)))
      (.bind (roShadowStepC A cap
          (fixedRoCacheE (.fst (.fst .v0))) (.fst (.snd (.fst .v0))) (.snd .v0))
        (.ret (.pair (aDrKeyAtomicE (.fst .v0))
          (.pair (fixedSetRoCacheE (.fst (.fst .v1)) (.fst (.snd .v0)))
            (.pair (.snd (.snd .v0)) (.snd (.snd (.fst .v1)))))))))

/-- `O(log cap)` `.roRootQuery` arm on `authFixedShadowStTy` with `asHasWonAuth` short-circuit. -/
@[expose] def roRootFixedShadowArmC {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    Comp pqAtomicOps A.toIface Γ (.prod authRespAtomicTy authFixedShadowStTy) :=
  .bind (.ret (.pair fsE inpE))
    (.ite (fixedHasWonE (.fst (.fst .v0)))
      (.ret (.pair aNoneAtomicE (.fst .v0)))
      (.bind (roRootShadowStepC A cap
          (fixedRootRoCacheE (.fst (.fst .v0))) (.snd (.snd (.fst .v0))) (.snd .v0))
        (.ret (.pair (aRootKdfAtomicE (.fst .v0))
          (.pair (fixedSetRootRoCacheE (.fst (.fst .v1)) (.fst (.snd .v0)))
            (.pair (.fst (.snd (.fst .v1))) (.snd (.snd .v0))))))))

@[expose] def listHeadOptE {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (l : Expr pqAtomicOps Γ (.list t)) : Expr pqAtomicOps Γ (.opt t) :=
  .findB 1 l (.bool true)

@[simp] theorem listHeadOptE_eval {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (l : Expr pqAtomicOps Γ (.list t)) (ρ : Env Γ) :
    (listHeadOptE l).eval ρ = (l.eval ρ).head? := by
  cases h : l.eval ρ <;> simp [listHeadOptE, Expr.eval, h]

@[expose] def syncRoHeadB192C {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy) :
    Comp pqAtomicOps I Γ roAvlTy :=
  .bind (.ret (.pair roListE tblE))
    (.caseOpt (listHeadOptE (.fst .v0))
      (.ret (.snd .v0))
      (.bind (.ret (.pair (.snd .v1) (.pair (aop (.pbytesToBytes 192) (.fst .v0)) (.snd .v0))))
        (.bind (avlSearchB192C cap (.fst .v0) (.fst (.snd .v0)))
          (.caseOpt (.fst .v0)
            (avlInsertAtPathC cap (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1)))
            (.ret (.fst .v2))))))

@[expose] def syncRoHeadPair32C {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    Comp pqAtomicOps I Γ roRootAvlTy :=
  .bind (.ret (.pair rootListE tblE))
    (.caseOpt (listHeadOptE (.fst .v0))
      (.ret (.snd .v0))
      (.bind (.ret (.pair (.snd .v1)
          (.pair (.pair (aop (.pbytesToBytes 32) (.fst (.fst .v0)))
                        (aop (.pbytesToBytes 32) (.snd (.fst .v0))))
            (.snd .v0))))
        (.bind (avlSearchPair32C cap (.fst .v0) (.fst (.snd .v0)))
          (.caseOpt (.fst .v0)
            (avlInsertAtPathC cap (.fst .v1) (.snd .v0) (.fst (.snd .v1)) (.snd (.snd .v1)))
            (.ret (.fst .v2))))))

/-- Pure `O(log cap)` post-step sync of `roBothAvlTy` with the heads of `(roList', rootList')`. -/
@[expose] def syncRoBothC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    Comp pqAtomicOps I Γ roBothAvlTy :=
  .bind (.ret (.pair roListE (.pair rootListE roBothE)))
    (.bind (syncRoHeadB192C cap (.fst .v0) (.fst (.snd (.snd .v0))))
      (.bind (syncRoHeadPair32C cap (.fst (.snd .v1)) (.snd (.snd (.snd .v1))))
        (.ret (.pair .v1 .v0))))

@[expose] def syncBaseShadowRespC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    Comp pqAtomicOps I Γ (.prod authRespAtomicTy authBaseShadowStTy) :=
  .bind (.ret (.pair rsE roBothE))
    (.bind (syncRoBothC cap
        (baseRoCacheE (.snd (.fst .v0)))
        (baseRootRoCacheE (.snd (.fst .v0)))
        (.snd .v0))
      (.ret (.pair (.fst (.fst .v1)) (.pair (.snd (.fst .v1)) .v0))))

@[expose] def syncFixedShadowRespC {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    Comp pqAtomicOps I Γ (.prod authRespAtomicTy authFixedShadowStTy) :=
  .bind (.ret (.pair rsfE roBothE))
    (.bind (syncRoBothC cap
        (fixedRoCacheE (.snd (.fst .v0)))
        (fixedRootRoCacheE (.snd (.fst .v0)))
        (.snd .v0))
      (.ret (.pair (.fst (.fst .v1)) (.pair (.snd (.fst .v1)) .v0))))

end ShadowRoAndSync

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
