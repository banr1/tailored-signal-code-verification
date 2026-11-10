/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
public import Computational.Proofs.E2E.Dsl.SpqrSim
public import Computational.Proofs.E2E.Dsl.DrSessionSim

/-!
# Bridge from `e2eSig` / `e2eOps` to `atomicSig` / `atomicSessionOps`

Translates oracle-free and coin-sampling `ReductionDsl` programs from `Costed.e2eOps` into
`atomicSessionOps` with exact evaluation preservation and linear step-cost preservation, and lifts
the SPQR and Double Ratchet session simulators.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drReceiveC drReceiveC_cost drReceiveC_eval_params drRecvOutT)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_cost drSendC_eval_params)
open Computational.Proofs.E2E.Dsl.SpqrSimRecv (spqrRecvComp spqrRecvComp_cost spqrRecvComp_eval)
open Computational.Proofs.E2E.Dsl.SpqrSimSend (spqrSendComp spqrSendComp_cost spqrSendComp_eval)
open CryptoGames.CKA (DHFun)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoGames.Ratchet (padOrTruncatePlain)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr)
open ReductionDsl (AtomicCurveCheckOp AtomicGroupOp AtomicPtDecOp AtomicPtEncOp AtomicPureOp AtomicSort AtomicSpqrKemOp AtomicSymOp B BV256 BV512 Comp Env Expr GhostStT Iface Ops PK PlainT PtT Sig Ty UniformSamplerTag Var anyML atomicCurveCheckOps atomicPtDecOps atomicPtEncOps atomicSamplers atomicSessionOps atomicSig consumeFirstML findML foldML iterM mapML)

namespace Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge

open OracleSpec OracleComp
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks spqrSendComp spqrSendComp_cost
  spqrSendComp_queries spqrSendComp_eval spqrRecvComp spqrRecvComp_cost spqrRecvComp_queries
  spqrRecvComp_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSim (E2ECoinSamplers mkE2ECoinSamplers
  drSendC drSendC_cost drSendC_queries drSendC_eval_params drRecvOutT drReceiveC drReceiveC_cost
  drReceiveC_queries drReceiveC_eval_params drTrArmC drTrArmC_cost drTrArmC_queries_zero
  drTrArmC_eval drChArmC drChArmC_cost drChArmC_queries_zero drChArmC_eval drDlArmC drDlArmC_cost
  drDlArmC_queries_zero drDlArmC_eval drIjArmC drIjArmC_cost drIjArmC_queries_zero drIjArmC_eval
  drCrArmC drCrArmC_cost drCrArmC_queries drCrArmC_eval)

/-! ## Operation constructors over `atomicSessionOps` -/

section SessionOpConstructors

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[reducible] def sessPureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) a

@[reducible] def sessPtEncOp {Γ : List (Ty ASig)} (o : AtomicPtEncOp)
    (a : Expr AOps Γ ((atomicPtEncOps ℓ encT).dom o)) :
    Expr AOps Γ ((atomicPtEncOps ℓ encT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl o))))) a

@[reducible] def sessSymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr o))))) a

@[reducible] def sessGroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inr o))) a

@[reducible] def sessPtDecOp {Γ : List (Ty ASig)} (o : AtomicPtDecOp)
    (a : Expr AOps Γ ((atomicPtDecOps ℓ decT).dom o)) :
    Expr AOps Γ ((atomicPtDecOps ℓ decT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inr (Sum.inl o))) a

@[reducible] def sessCurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).cod o) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inr (Sum.inr o))) a

@[reducible] def sessSpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inr o) a

@[simp] theorem eval_sessPureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_sessPureOp {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sessPtEncOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sessPtEncOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).eval ρ = encT (a.eval ρ) := rfl

@[simp] theorem cost_sessPtEncOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) :
    (sessPtEncOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).cost = a.cost + 4 := rfl

@[simp] theorem eval_sessSymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_sessSymOp {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessSymOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem eval_sessGroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_sessGroupOp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem eval_sessPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sessPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).eval ρ = decT (a.eval ρ) := rfl

@[simp] theorem cost_sessPtDecOp {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sessPtDecOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).cost = a.cost + 8 := rfl

@[simp] theorem eval_sessCurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (sessCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

@[simp] theorem cost_sessCurveOp {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sessCurveOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + (atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem eval_sessSpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C K (a.eval ρ) := rfl

@[simp] theorem cost_sessSpqrKemOp {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

end SessionOpConstructors

/-! ## Coin-sampler helpers -/

section CoinSamplers

variable {ℓ : ℕ} {Pt : Type} [SampleableType Pt]

def atomicDraw256 {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt := by rfl)
    {Γ : List (Ty (atomicSig ℓ Pt))} : Comp O I Γ BV256 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  exact ReductionDsl.Comp.sample
    (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩)
    (ReductionDsl.UniformSamplerTag.base ReductionDsl.AtomicUnifBase.bv256) .unit

def atomicDraw512 {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt := by rfl)
    {Γ : List (Ty (atomicSig ℓ Pt))} : Comp O I Γ BV512 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  exact ReductionDsl.Comp.sample
    (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩)
    (ReductionDsl.UniformSamplerTag.base ReductionDsl.AtomicUnifBase.bv512) .unit

def atomicDrawPt {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt := by rfl)
    {Γ : List (Ty (atomicSig ℓ Pt))} : Comp O I Γ PtT := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  exact ReductionDsl.Comp.sample
    (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩)
    (ReductionDsl.UniformSamplerTag.base ReductionDsl.AtomicUnifBase.pt) .unit

@[simp] theorem atomicDraw256_eval {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (atomicDraw256 (O := O) (I := I) h).eval ρ = I.liftP ($ᵗ (BitVec 256)) := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  dsimp only [atomicDraw256, ReductionDsl.Comp.eval]
  congr 1

@[simp] theorem atomicDraw512_eval {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (atomicDraw512 (O := O) (I := I) h).eval ρ = I.liftP ($ᵗ (BitVec 512)) := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  dsimp only [atomicDraw512, ReductionDsl.Comp.eval]
  congr 1

@[simp] theorem atomicDrawPt_eval {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ) :
    (atomicDrawPt (O := O) (I := I) h).eval ρ = I.liftP ($ᵗ Pt) := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  dsimp only [atomicDrawPt, ReductionDsl.Comp.eval]
  congr 1

@[simp] theorem atomicDraw256_cost {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw256 (O := O) (I := I) h (Γ := Γ)).cost = 2 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem atomicDraw512_cost {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDraw512 (O := O) (I := I) h (Γ := Γ)).cost = 3 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem atomicDrawPt_cost {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (atomicDrawPt (O := O) (I := I) h (Γ := Γ)).cost = 2 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem atomicDraw256_queries_zero {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (w : I.Tag → ℕ) :
    (atomicDraw256 (O := O) (I := I) h (Γ := Γ)).queries w (fun _ => 0) = 0 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem atomicDraw512_queries_zero {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (w : I.Tag → ℕ) :
    (atomicDraw512 (O := O) (I := I) h (Γ := Γ)).queries w (fun _ => 0) = 0 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

@[simp] theorem atomicDrawPt_queries_zero {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (h : I.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty (atomicSig ℓ Pt))} (w : I.Tag → ℕ) :
    (atomicDrawPt (O := O) (I := I) h (Γ := Γ)).queries w (fun _ => 0) = 0 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at h
  subst h
  rfl

end CoinSamplers

/-! ## Sort, type, and value lifting -/

/-- Dummy `SignalPqxdh.Primitives` record used to instantiate `P`-independent session programs before translating them into `atomicSessionOps`. -/
def zeroPqxdhPrims : SignalPqxdh.Primitives where
  x25519 := fun _ _ => []
  x25519Base := fun _ => []
  isCanonical := fun _ => false
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  sigVerify := fun _ _ _ => false
  sha512 := fun _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  scalarFromBytesModOrder := fun _ => []
  scalarFromWide := fun _ => []
  montToEd := fun _ _ => none
  isTorsionFree := fun _ => false
  edNeg := fun _ => []
  doubleScalarMulBasepoint := fun _ _ _ => []
  compress := fun _ => []
  kemKeyGen := fun _ => ([], [])
  kemEncaps := fun _ _ => none
  kemDecaps := fun _ _ => none
  hkdfDerive96 := fun _ => ⟨[], [], []⟩
  rootCreateChain := fun _ _ => ([], [])
  chainKdfSeed := fun _ => []
  chainKdfNext := fun _ => []
  spqrInitSend := fun _ _ => none
  spqrInitRecv := fun _ _ => none
  deriveMsgKeys := fun _ _ => ⟨[], [], []⟩
  aeadEnc := fun _ _ _ => []
  aeadDec := fun _ _ _ => none
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false
  sha256Compress := fun _ _ => []
  sha512Compress := fun _ _ => []
  aesEncBlock := fun _ _ => []
  aesDecBlock := fun _ _ => []

@[reducible] def liftSort : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESort → AtomicSort
  | .pbytes w => .pbytes w
  | .pu32 => .pu32
  | .bytes w => .bytes w
  | .u8 => .u8
  | .u32 => .u32
  | .u64 => .u64
  | .bv128 => .bv128
  | .bv256 => .bv256
  | .bv512 => .bv512
  | .fin n => .fin n
  | .pk => .pk
  | .idKey => .idKey
  | .plain => .plain
  | .ghostSt => .ghostSt
  | .binSt => .binSt

@[reducible] def liftTy {ℓ : ℕ} {Pt : Type} :
    Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ) → Ty (atomicSig ℓ Pt)
  | .base b => .base (liftSort b)
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .opt t => .opt (liftTy t)
  | .prod t u => .prod (liftTy t) (liftTy u)
  | .sum t u => .sum (liftTy t) (liftTy u)
  | .list t => .list (liftTy t)
  | .tbl t => .tbl (liftTy t)

@[reducible] def liftCtx {ℓ : ℕ} {Pt : Type} :
    List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)) → List (Ty (atomicSig ℓ Pt))
  | [] => []
  | t :: Γ => liftTy t :: liftCtx Γ

def liftBaseVal {ℓ : ℕ} {Pt : Type} :
    (b : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESort) → b.den ℓ → (liftSort b).den ℓ Pt
  | .pbytes _, x => x
  | .pu32, x => x
  | .bytes _, x => x
  | .u8, x => x
  | .u32, x => x
  | .u64, x => x
  | .bv128, x => x
  | .bv256, x => x
  | .bv512, x => x
  | .fin _, x => x
  | .pk, x => x
  | .idKey, x => x
  | .plain, x => x
  | .ghostSt, x => x
  | .binSt, x => x

def liftVal {ℓ : ℕ} {Pt : Type} :
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)} → t.denote → (liftTy (Pt := Pt) t).denote
  | .base b, x => liftBaseVal b x
  | .unit, () => ()
  | .bool, x => x
  | .nat, x => x
  | .opt _, x => x.map liftVal
  | .prod _ _, (x, y) => (liftVal x, liftVal y)
  | .sum _ _, .inl x => .inl (liftVal x)
  | .sum _ _, .inr y => .inr (liftVal y)
  | .list _, xs => xs.map liftVal
  | .tbl _, m => fun i => liftVal (m i)

theorem liftBase_den_eq (ℓ : ℕ) (Pt : Type) (b : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESort) :
    (liftSort b).den ℓ Pt = b.den ℓ := by
  cases b <;> rfl

theorem liftBaseVal_heq {ℓ : ℕ} {Pt : Type} (b : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ESort) (x : b.den ℓ) :
    HEq (liftBaseVal (Pt := Pt) b x) x := by
  cases b <;> rfl

theorem liftTy_denote_eq {ℓ : ℕ} {Pt : Type} :
    (t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)) → (liftTy (Pt := Pt) t).denote = t.denote
  | .base b => liftBase_den_eq ℓ Pt b
  | .unit => rfl
  | .bool => rfl
  | .nat => rfl
  | .opt t => by simp only [ReductionDsl.Ty.denote, liftTy_denote_eq t]
  | .prod t u => by simp only [ReductionDsl.Ty.denote, liftTy_denote_eq t, liftTy_denote_eq u]
  | .sum t u => by simp only [ReductionDsl.Ty.denote, liftTy_denote_eq t, liftTy_denote_eq u]
  | .list t => by simp only [ReductionDsl.Ty.denote, liftTy_denote_eq t]
  | .tbl t => by simp only [ReductionDsl.Ty.denote, liftTy_denote_eq t]

private theorem opt_map_heq {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, HEq (f a) a) (x : Option α) : HEq (x.map f) x := by
  subst h
  cases x with
  | none => rfl
  | some a => simp [eq_of_heq (hf a)]

private theorem prod_mk_heq {α₁ β₁ α₂ β₂ : Type} (h1 : β₁ = α₁) (h2 : β₂ = α₂)
    {a : α₁} {b : β₁} {c : α₂} {d : β₂} (hb : HEq b a) (hd : HEq d c) :
    HEq (b, d) (a, c) := by
  subst h1; subst h2; cases hb; cases hd; rfl

private theorem sum_inl_heq {α₁ β₁ α₂ β₂ : Type} (h1 : β₁ = α₁) (h2 : β₂ = α₂)
    {a : α₁} {b : β₁} (hb : HEq b a) :
    HEq (Sum.inl b : β₁ ⊕ β₂) (Sum.inl a : α₁ ⊕ α₂) := by
  subst h1; subst h2; cases hb; rfl

private theorem sum_inr_heq {α₁ β₁ α₂ β₂ : Type} (h1 : β₁ = α₁) (h2 : β₂ = α₂)
    {c : α₂} {d : β₂} (hd : HEq d c) :
    HEq (Sum.inr d : β₁ ⊕ β₂) (Sum.inr c : α₁ ⊕ α₂) := by
  subst h1; subst h2; cases hd; rfl

private theorem list_map_heq {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, HEq (f a) a) (xs : List α) : HEq (xs.map f) xs := by
  subst h
  induction xs with
  | nil => rfl
  | cons a as ih => simp [eq_of_heq (hf a), eq_of_heq ih]

private theorem tbl_map_heq {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, HEq (f a) a) (m : ℕ → α) : HEq (fun i => f (m i)) m := by
  subst h
  apply heq_of_eq
  funext i
  exact eq_of_heq (hf (m i))

theorem liftVal_heq {ℓ : ℕ} {Pt : Type} :
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)} → (x : t.denote) → HEq (liftVal (Pt := Pt) (t := t) x) x
  | .base b, x => liftBaseVal_heq b x
  | .unit, () => HEq.rfl
  | .bool, _ => HEq.rfl
  | .nat, _ => HEq.rfl
  | .opt t, x => opt_map_heq (liftTy_denote_eq t) liftVal liftVal_heq x
  | .prod t u, (x, y) =>
    prod_mk_heq (liftTy_denote_eq t) (liftTy_denote_eq u) (liftVal_heq x) (liftVal_heq y)
  | .sum t u, .inl x => sum_inl_heq (liftTy_denote_eq t) (liftTy_denote_eq u) (liftVal_heq x)
  | .sum t u, .inr y => sum_inr_heq (liftTy_denote_eq t) (liftTy_denote_eq u) (liftVal_heq y)
  | .list t, xs => list_map_heq (liftTy_denote_eq t) liftVal liftVal_heq xs
  | .tbl t, m => tbl_map_heq (liftTy_denote_eq t) liftVal liftVal_heq m

def liftVar {ℓ : ℕ} {Pt : Type} :
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))} → {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)} →
    Var Γ t → Var (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (liftVar v)

def liftEnv {ℓ : ℕ} {Pt : Type} :
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))} → Env Γ → Env (liftCtx (Pt := Pt) Γ)
  | [], .nil => .nil
  | _ :: _, .cons x ρ => .cons (liftVal x) (liftEnv ρ)

theorem liftEnv_get {ℓ : ℕ} {Pt : Type} :
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))} → {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)} →
    (ρ : Env Γ) → (v : Var Γ t) →
    (liftEnv (Pt := Pt) ρ).get (liftVar v) = liftVal (ρ.get v)
  | _ :: _, _, .cons _ _, .zero => rfl
  | _ :: _, _, .cons _ ρ, .succ v => liftEnv_get ρ v

/-! ## Equivalence of recursive wire and SPQR helpers -/

private theorem readProstVarint_eq_aux :
    ∀ bs, ReductionDsl.e2eReadProstVarint bs = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eReadProstVarint bs
  | [] => rfl
  | b :: rest => by
    simp only [ReductionDsl.e2eReadProstVarint, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eReadProstVarint,
      readProstVarint_eq_aux rest]

theorem readProstVarint_eq :
    @ReductionDsl.e2eReadProstVarint = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eReadProstVarint :=
  funext readProstVarint_eq_aux

private theorem splitSpqrPrev_eq_aux :
    ∀ fuel bs, ReductionDsl.splitSpqrPrev fuel bs = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.splitSpqrPrev fuel bs
  | 0, _ => rfl
  | fuel + 1, bs => by
    simp only [ReductionDsl.splitSpqrPrev, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.splitSpqrPrev,
      ReductionDsl.e2eReadU32BE, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eReadU32BE,
      splitSpqrPrev_eq_aux fuel (bs.drop 36)]
    rfl

theorem splitSpqrPrev_eq :
    @ReductionDsl.splitSpqrPrev = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.splitSpqrPrev :=
  funext fun fuel => funext (splitSpqrPrev_eq_aux fuel)

private theorem partyToBool_eq : @ReductionDsl.partyToBool = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.partyToBool := by
  funext p; cases p <;> rfl

private theorem boolToParty_eq : @ReductionDsl.boolToParty = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.boolToParty := by
  funext b; cases b <;> rfl

/-! ## `Expr` and `Comp` compiler into `atomicSessionOps` -/

section Compiler

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT
local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def liftPureOpExpr {Γ : List (Ty ASig)} :
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp) →
    Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ)) →
    Expr AOps Γ (liftTy (Pt := Pt) (o.cod ℓ))
  | .pbytesLit w v, a => sessPureOp (.pbytesLit w v) a
  | .pbytesCat m n, a => sessPureOp (.pbytesCat m n) a
  | .pbytesCons b w, a => sessPureOp (.pbytesCons b w) a
  | .pbytesWiden w d, a => sessPureOp (.pbytesWiden w d) a
  | .pbytesTakeK w k, a => sessPureOp (.pbytesTakeK w k) a
  | .pbytesTake w, a => sessPureOp (.pbytesTake w) a
  | .pbytesDrop w, a => sessPureOp (.pbytesDrop w) a
  | .pbytesLen w, a => sessPureOp (.pbytesLen w) a
  | .pbytesEq m n, a => sessPureOp (.pbytesEq m n) a
  | .bytesLit w v, a => sessPureOp (.bytesLit w v) a
  | .bytesCat m n, a => sessPureOp (.bytesCat m n) a
  | .bytesCons b w, a => sessPureOp (.bytesCons b w) a
  | .bytesWiden w d, a => sessPureOp (.bytesWiden w d) a
  | .bytesTakeK w k, a => sessPureOp (.bytesTakeK w k) a
  | .bytesTake w, a => sessPureOp (.bytesTake w) a
  | .bytesDrop w, a => sessPureOp (.bytesDrop w) a
  | .bytesLen w, a => sessPureOp (.bytesLen w) a
  | .bytesEq m n, a => sessPureOp (.bytesEq m n) a
  | .bytesLtOp m n, a => sessPureOp (.bytesLtOp m n) a
  | .pbytesToBytes w, a => sessPureOp (.pbytesToBytes w) a
  | .bytesToPbytes w, a => sessPureOp (.bytesToPbytes w) a
  | .pu32Lit k, a => sessPureOp (.pu32Lit k) a
  | .pu32OfNat, a => sessPureOp .pu32OfNat a
  | .pu32ToNat, a => sessPureOp .pu32ToNat a
  | .pu32Eq, a => sessPureOp .pu32Eq a
  | .pu32ToU32, a => sessPureOp .pu32ToU32 a
  | .u32ToPu32, a => sessPureOp .u32ToPu32 a
  | .u8Lit v, a => sessPureOp (.u8Lit v) a
  | .u8OfNat, a => sessPureOp .u8OfNat a
  | .u8ToNat, a => sessPureOp .u8ToNat a
  | .u8Eq, a => sessPureOp .u8Eq a
  | .u8Lt, a => sessPureOp .u8Lt a
  | .u32Lit v, a => sessPureOp (.u32Lit v) a
  | .u32OfNat, a => sessPureOp .u32OfNat a
  | .u32ToNat, a => sessPureOp .u32ToNat a
  | .u32Eq, a => sessPureOp .u32Eq a
  | .u32Lt, a => sessPureOp .u32Lt a
  | .u32Add, a => sessPureOp .u32Add a
  | .u32Sub, a => sessPureOp .u32Sub a
  | .u32BeBytes, a => sessPureOp .u32BeBytes a
  | .u64Lit v, a => sessPureOp (.u64Lit v) a
  | .u64OfNat, a => sessPureOp .u64OfNat a
  | .u64ToNat, a => sessPureOp .u64ToNat a
  | .u64Eq, a => sessPureOp .u64Eq a
  | .u64Lt, a => sessPureOp .u64Lt a
  | .u64Add, a => sessPureOp .u64Add a
  | .u64Sub, a => sessPureOp .u64Sub a
  | .u64Trunc8, a => sessPureOp .u64Trunc8 a
  | .finVal n, a => sessPureOp (.finVal n) a
  | .finEq n, a => sessPureOp (.finEq n) a
  | .bv128Eq, a => sessPureOp .bv128Eq a
  | .bv256Lit v, a => sessPureOp (.bv256Lit v) a
  | .bv256Eq, a => sessPureOp .bv256Eq a
  | .bv256ToPbytes32, a => sessPureOp .bv256ToPbytes32 a
  | .pbytesToBv256, a => sessPureOp .pbytesToBv256 a
  | .bv256ToBytes32, a => sessPureOp .bv256ToBytes32 a
  | .bytesToBv256, a => sessPureOp .bytesToBv256 a
  | .bv512Lit v, a => sessPureOp (.bv512Lit v) a
  | .bv512ToBytes64, a => sessPureOp .bv512ToBytes64 a
  | .idKeyOfPbytes, a => sessPureOp .idKeyOfPbytes a
  | .idKeySerialize, a => sessPureOp .idKeySerialize a
  | .idKeyEq, a => sessPureOp .idKeyEq a
  | .pkOfPbytes, a => sessPureOp .pkOfPbytes a
  | .pkDeserialize, a => sessPureOp .pkDeserialize a
  | .pkSerialize, a => sessPureOp .pkSerialize a
  | .pkEq, a => sessPureOp .pkEq a
  | .plainDefault, a => sessPureOp .plainDefault a
  | .plainToBytes, a => sessPureOp .plainToBytes a
  | .bytesToPlain, a => sessPureOp .bytesToPlain a
  | .plainEq, a => sessPureOp .plainEq a
  | .checkShortCiphertext, a => sessPureOp .checkShortCiphertext a
  | .parsePreKeyWire, a => sessPureOp .parsePreKeyWire a
  | .partneredInnerBytes, a => sessPureOp .partneredInnerBytes a
  | .wireInnerBytes, a => sessPureOp .wireInnerBytes a
  | .splitWhisperWire, a => sessPureOp .splitWhisperWire a
  | .isValidSignalWire, a => sessPureOp .isValidSignalWire a
  | .signalMsgParse, a => sessPureOp .signalMsgParse a
  | .wrapWhisperWire, a => sessPureOp .wrapWhisperWire a
  | .wrapPreKeyWire, a => sessPureOp .wrapPreKeyWire a
  | .spqrParsePreamble, a => sessPureOp .spqrParsePreamble a
  | .spqrAssembleMsg, a => sessPureOp .spqrAssembleMsg a
  | .spqrStateSplit, a => sessPureOp .spqrStateSplit a
  | .spqrStateJoin, a => sessPureOp .spqrStateJoin a
  | .ghostStateSplit, a => sessPureOp .ghostStateSplit a
  | .ghostStateJoin, a => sessPureOp .ghostStateJoin a
  | .encodeSessionRecord, a => sessPureOp .encodeSessionRecord a

def liftCurveOpExpr {Γ : List (Ty ASig)} :
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp) →
    Expr AOps Γ (liftTy (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc)) →
    Expr AOps Γ (liftTy (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).cod cc))
  | .decEncCheck, a => sessCurveOp .decEncCheck a
  | .checkRatchetKeyOnCurve, a => sessCurveOp .checkRatchetKeyOnCurve a

def liftCryptoOpExpr {Γ : List (Ty ASig)} :
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp) →
    Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ)) →
    Expr AOps Γ (liftTy (Pt := Pt) (c.cod ℓ))
  | .x25519, a => .letE a (sessPureOp (.pbytesLit 32 []) .unit)
  | .x25519Base, a => .letE a (sessPureOp (.pbytesLit 32 []) .unit)
  | .pow8, a => .letE a (sessPureOp (.pbytesLit 32 []) .unit)
  | .isCanonical, a => .letE a (.bool false)
  | .sigSign, a => .letE a (sessPureOp (.pbytesLit 64 []) .unit)
  | .sigVerify, a => .letE a (.bool false)
  | .kemKeyGen, a =>
    .letE a (.pair (sessPureOp (.pbytesLit 1568 []) .unit)
                   (sessPureOp (.pbytesLit 3168 []) .unit))
  | .kemEncaps, a => .letE a .none
  | .kemDecaps, a => .letE a .none
  | .hkdfDerive96, a =>
    .letE a (let z := sessPureOp (.pbytesLit 32 []) .unit; .pair z (.pair z z))
  | .sessionKeyPairGen, a => sessSymOp .sessionKeyPairGen a
  | .sessionRootCreateChain, a => sessSymOp .sessionRootCreateChain a
  | .chainStep, a => sessSymOp .chainStep a
  | .deriveMsgKeys, a => sessSymOp .deriveMsgKeys a
  | .aes256CbcEnc, a => sessSymOp .aes256CbcEnc a
  | .aes256CbcDec, a => sessSymOp .aes256CbcDec a
  | .signalMsgEncode, a => sessSymOp .signalMsgEncode a
  | .signalMsgVerifyMac, a => sessSymOp .signalMsgVerifyMac a
  | .spqrV1InitOp, a => sessSpqrKemOp .spqrV1InitOp a
  | .spqrNegotiateInit, a => sessSpqrKemOp .spqrNegotiateInit a
  | .spqrBraidSend, a => sessSpqrKemOp .spqrBraidSend a
  | .spqrBraidRecv, a => sessSpqrKemOp .spqrBraidRecv a
  | .spqrChainFromVn, a => sessSpqrKemOp .spqrChainFromVn a
  | .spqrChainAddEpoch, a => sessSpqrKemOp .spqrChainAddEpoch a
  | .spqrChainNextKey, a => sessSpqrKemOp .spqrChainNextKey a

def liftOpExpr {Γ : List (Ty ASig)} :
    (o : (EOps).Op) →
    Expr AOps Γ (liftTy (Pt := Pt) ((EOps).dom o)) →
    Expr AOps Γ (liftTy (Pt := Pt) ((EOps).cod o))
  | .inl o, a => liftPureOpExpr o a
  | .inr (.inl cc), a => liftCurveOpExpr cc a
  | .inr (.inr c), a => liftCryptoOpExpr c a

/-- Total expression compiler from `Costed.e2eOps` at `zeroPqxdhPrims` into `atomicSessionOps`. -/
def liftExpr :
    {Γ : List (Ty ESig)} → {t : Ty ESig} →
    Expr EOps Γ t →
    Expr AOps (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .var v => .var (liftVar v)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (liftExpr a) (liftExpr b)
  | _, _, .sub a b => .sub (liftExpr a) (liftExpr b)
  | _, _, .mulK k a => .mulK k (liftExpr a)
  | _, _, .divK k a => .divK k (liftExpr a)
  | _, _, .modK k a => .modK k (liftExpr a)
  | _, _, .lt a b => .lt (liftExpr a) (liftExpr b)
  | _, _, .eqN a b => .eqN (liftExpr a) (liftExpr b)
  | _, _, .not a => .not (liftExpr a)
  | _, _, .and a b => .and (liftExpr a) (liftExpr b)
  | _, _, .ite c a b => .ite (liftExpr c) (liftExpr a) (liftExpr b)
  | _, _, .pair a b => .pair (liftExpr a) (liftExpr b)
  | _, _, .fst a => .fst (liftExpr a)
  | _, _, .snd a => .snd (liftExpr a)
  | _, _, .inl a => .inl (liftExpr a)
  | _, _, .inr a => .inr (liftExpr a)
  | _, _, .none => .none
  | _, _, .some a => .some (liftExpr a)
  | _, _, .caseOpt e n s => .caseOpt (liftExpr e) (liftExpr n) (liftExpr s)
  | _, _, .caseSum e l r => .caseSum (liftExpr e) (liftExpr l) (liftExpr r)
  | _, _, .letE e b => .letE (liftExpr e) (liftExpr b)
  | _, _, .op o a => liftOpExpr o (liftExpr a)
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (liftExpr x) (liftExpr l)
  | _, _, .len l => .len (liftExpr l)
  | _, _, .take n l => .take (liftExpr n) (liftExpr l)
  | _, _, .appendL K a b => .appendL K (liftExpr a) (liftExpr b)
  | _, _, .findB K l p => .findB K (liftExpr l) (liftExpr p)
  | _, _, .anyB K l p => .anyB K (liftExpr l) (liftExpr p)
  | _, _, .mapB K l f => .mapB K (liftExpr l) (liftExpr f)
  | _, _, .foldrB K l z f => .foldrB K (liftExpr l) (liftExpr z) (liftExpr f)
  | _, _, .tconst a => .tconst (liftExpr a)
  | _, _, .tget m i => .tget (liftExpr m) (liftExpr i)
  | _, _, .tset m i a => .tset (liftExpr m) (liftExpr i) (liftExpr a)

private theorem liftPureOpExpr_cost {Γ : List (Ty ASig)} (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost ≤ a.cost + 32 * o.cost ℓ := by
  cases o <;>
  · dsimp only [liftPureOpExpr]
    rw [cost_sessPureOp]
    dsimp only [ReductionDsl.AtomicPureOp.cost, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.cost]
    omega

private theorem liftCurveOpExpr_cost {Γ : List (Ty ASig)} (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc))) :
    (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).cost ≤
      a.cost + 32 * (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).cost cc := by
  cases cc <;>
  · dsimp only [liftCurveOpExpr]
    rw [cost_sessCurveOp]
    dsimp only [atomicCurveCheckOps, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps]
    omega

private theorem liftCryptoOpExpr_cost {Γ : List (Ty ASig)} (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).cost ≤ a.cost + 32 * c.cost ℓ := by
  match c with
  | .x25519 =>
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .x25519 a).cost = a.cost + 34 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.x25519.cost ℓ = 8 := rfl
    rw [hc, hr]; omega
  | .x25519Base =>
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .x25519Base a).cost = a.cost + 34 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.x25519Base.cost ℓ = 8 := rfl
    rw [hc, hr]; omega
  | .pow8 =>
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .pow8 a).cost = a.cost + 34 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.pow8.cost ℓ = 8 := rfl
    rw [hc, hr]; omega
  | .hkdfDerive96 =>
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .hkdfDerive96 a).cost = a.cost + 102 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.hkdfDerive96.cost ℓ = 16 := rfl
    rw [hc, hr]; omega
  | .sigSign =>
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .sigSign a).cost = a.cost + 66 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.sigSign.cost ℓ = 60 := rfl
    rw [hc, hr]; omega
  | .kemKeyGen =>
    let b1 : Expr AOps (liftTy (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.kemKeyGen.dom ℓ) :: Γ) _ :=
      sessPureOp (.pbytesLit 1568 []) .unit
    let b2 : Expr AOps (liftTy (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.kemKeyGen.dom ℓ) :: Γ) _ :=
      sessPureOp (.pbytesLit 3168 []) .unit
    have h1 : b1.cost = 1 + (1568 + 0) := by dsimp only [b1]; rw [cost_sessPureOp]; rfl
    have h2 : b2.cost = 1 + (3168 + 0) := by dsimp only [b2]; rw [cost_sessPureOp]; rfl
    have hc : (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .kemKeyGen a).cost =
        a.cost + (b1.cost + b2.cost + 1) + 1 := rfl
    have hr : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.kemKeyGen.cost ℓ = 160 := rfl
    rw [hc, h1, h2, hr]; omega
  | .isCanonical | .sigVerify | .kemEncaps | .kemDecaps =>
    dsimp only [liftCryptoOpExpr, ReductionDsl.Expr.cost, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSymOp]
    dsimp only [ReductionDsl.AtomicSymOp.cost, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv
  | .spqrChainFromVn | .spqrChainAddEpoch | .spqrChainNextKey =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSpqrKemOp]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.cost, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega

private theorem liftOpExpr_cost {Γ : List (Ty ASig)} (o : (EOps).Op)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((EOps).dom o))) :
    (liftOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost ≤ a.cost + 32 * (EOps).cost o := by
  rcases o with o | (cc | c)
  · exact liftPureOpExpr_cost o a
  · exact liftCurveOpExpr_cost cc a
  · exact liftCryptoOpExpr_cost c a

private theorem mul_cost_step (Kb x y : ℕ) (h : x ≤ 32 * y) :
    Kb * (x + 1) ≤ 32 * (Kb * (y + 1)) := by
  calc Kb * (x + 1) ≤ Kb * (32 * (y + 1)) := Nat.mul_le_mul_left Kb (by omega)
    _ = 32 * (Kb * (y + 1)) := by ring

private theorem mul_cost_step2 (Kb x1 x2 y1 y2 : ℕ) (h1 : x1 ≤ 32 * y1) (h2 : x2 ≤ 32 * y2) :
    Kb * (x1 + x2 + 1) ≤ 32 * (Kb * (y1 + y2 + 1)) := by
  calc Kb * (x1 + x2 + 1) ≤ Kb * (32 * (y1 + y2 + 1)) := Nat.mul_le_mul_left Kb (by omega)
    _ = 32 * (Kb * (y1 + y2 + 1)) := by ring

theorem liftExpr_cost {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr EOps Γ t) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).cost ≤ 32 * e.cost := by
  induction e with
  | var _ | unit | bool _ | none | nil => simp [liftExpr, ReductionDsl.Expr.cost]
  | nat _ => simp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb
  | letE _ _ ha hb | tget _ _ ha hb =>
    simp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | ite _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb | caseSum _ _ _ hc ha hb
  | tset _ _ _ hc ha hb =>
    simp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | op o a ha =>
    have ho := liftOpExpr_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o (liftExpr a)
    simp only [liftExpr, ReductionDsl.Expr.cost] at ho ⊢
    omega
  | findB Kb _ _ hl hp | anyB Kb _ _ hl hp | mapB Kb _ _ hl hp =>
    have hm := mul_cost_step Kb _ _ hp
    simp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | foldrB Kb _ _ _ hl hz hf =>
    have hm := mul_cost_step Kb _ _ hf
    simp only [liftExpr, ReductionDsl.Expr.cost]; omega

private theorem list_find_map {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, (xs.map g).find? q = (xs.find? p).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hpq x]
    cases p x
    · exact list_find_map g q p hpq xs
    · rfl

private theorem list_any_map_eq {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, (xs.map g).any q = xs.any p
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.any_cons, hpq x, list_any_map_eq g q p hpq xs]

private theorem list_map_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ) (f : α → γ) (hfg : ∀ x, f' (g x) = h (f x)) :
    ∀ xs : List α, (xs.map g).map f' = (xs.map f).map h
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, hfg x, list_map_map_eq g h f' f hfg xs]

private theorem list_foldr_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ → δ) (f : α → γ → γ) (hf : ∀ x acc, f' (g x) (h acc) = h (f x acc)) (z : γ) :
    ∀ xs : List α, (xs.map g).foldr f' (h z) = h (xs.foldr f z)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.foldr_cons, list_foldr_map_eq g h f' f hf z xs, hf x]

private theorem e2eParseOptPreKeyId_eq :
    ReductionDsl.e2eParseOptPreKeyId = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseOptPreKeyId := by
  funext xs
  cases xs with
  | nil => rfl
  | cons b rest =>
    dsimp only [ReductionDsl.e2eParseOptPreKeyId, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseOptPreKeyId]
    rw [readProstVarint_eq]

private theorem e2eParseUint32Field_eq :
    ReductionDsl.e2eParseUint32Field = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseUint32Field := by
  funext kb xs
  cases xs with
  | nil => rfl
  | cons k rest =>
    dsimp only [ReductionDsl.e2eParseUint32Field, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseUint32Field]
    rw [readProstVarint_eq]

private theorem e2eParseDjbKeyField_eq :
    ReductionDsl.e2eParseDjbKeyField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseDjbKeyField := rfl

private theorem e2eParseInnerMsgField_eq :
    ReductionDsl.e2eParseInnerMsgField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField := by
  funext xs
  cases xs with
  | nil => rfl
  | cons b rest =>
    by_cases h : b = 0x22#8
    · subst h
      simp [ReductionDsl.e2eParseInnerMsgField, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField, readProstVarint_eq]
    · simp [ReductionDsl.e2eParseInnerMsgField, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField, h]

private theorem e2eParseKyberCtField_eq :
    ReductionDsl.e2eParseKyberCtField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseKyberCtField := rfl

private theorem e2eDecodePreKeyRaw_eq :
    ReductionDsl.e2eDecodePreKeyRaw = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyRaw := by
  funext c
  cases c with
  | nil => rfl
  | cons t cs =>
    cases cs with
    | nil => rfl
    | cons v proto =>
      dsimp only [ReductionDsl.e2eDecodePreKeyRaw, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyRaw]
      rw [e2eParseOptPreKeyId_eq, e2eParseDjbKeyField_eq, e2eParseInnerMsgField_eq,
          e2eParseUint32Field_eq, e2eParseKyberCtField_eq]

private theorem e2eDecodePreKeyMsg_eq :
    ReductionDsl.e2eDecodePreKeyMsg = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyMsg := by
  funext c
  dsimp only [ReductionDsl.e2eDecodePreKeyMsg, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyMsg]
  rw [e2eDecodePreKeyRaw_eq]; rfl

private theorem e2eHdrOfPreKeyMsg_eq :
    ReductionDsl.e2eHdrOfPreKeyMsg = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eHdrOfPreKeyMsg := rfl

private theorem e2eExpectedPreKeyMsg_eq :
    ReductionDsl.e2eExpectedPreKeyMsg = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eExpectedPreKeyMsg := rfl

private theorem e2eWireInnerBytes_eq :
    ReductionDsl.e2eWireInnerBytes = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eWireInnerBytes := by
  funext c
  dsimp only [ReductionDsl.e2eWireInnerBytes, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eWireInnerBytes]
  rw [e2eDecodePreKeyMsg_eq]; rfl

private theorem e2ePartneredInnerBytes_eq :
    ReductionDsl.e2ePartneredInnerBytes = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2ePartneredInnerBytes := by
  funext bobAcc regIdA sessionHdr c
  dsimp only [ReductionDsl.e2ePartneredInnerBytes, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2ePartneredInnerBytes]
  rw [e2eDecodePreKeyMsg_eq, e2eExpectedPreKeyMsg_eq, e2eHdrOfPreKeyMsg_eq]; rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrParamsToV_eq (p : CryptoVerification.LibsignalSpqrV1.ChainParamsPB) :
    ReductionDsl.spqrParamsToV (ℓ := ℓ) (Pt := Pt) p = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsToV (ℓ := ℓ) p := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrParamsOfV_eq (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrParamsOfV (ℓ := ℓ) (Pt := Pt) v = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsOfV (ℓ := ℓ) v := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrVnToV_eq (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB) :
    ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) vn = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnToV (ℓ := ℓ) vn := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrVnOfV_eq (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) v = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV (ℓ := ℓ) v := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrDirToV_eq (d : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB) :
    ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) d = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV (ℓ := ℓ) d := by
  dsimp only [ReductionDsl.spqrDirToV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV]
  rw [splitSpqrPrev_eq]

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrDirOfV_eq (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrDirOfV (ℓ := ℓ) (Pt := Pt) v = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirOfV (ℓ := ℓ) v := rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrChainToV_eq (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) c = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV (ℓ := ℓ) c := by
  dsimp only [ReductionDsl.spqrChainToV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV]
  have hd : ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV (ℓ := ℓ) :=
    funext spqrDirToV_eq
  have hp : ReductionDsl.spqrParamsToV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsToV (ℓ := ℓ) :=
    funext spqrParamsToV_eq
  rw [hd, hp]

omit [DecidableEq Pt] [Zero Pt] in
private theorem spqrChainOfV_eq (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) v = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV (ℓ := ℓ) v := rfl

private theorem e2eRecordExtras_eq :
    ReductionDsl.e2eRecordExtras = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eRecordExtras := by
  funext regIdA regIdB bobRemoteRegId hdr p
  cases p <;> rfl

set_option maxHeartbeats 400000 in
private theorem liftPureOpExpr_eval {Γ : List (Ty ASig)} (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ))) (ρ : Env Γ)
    (x : (o.dom ℓ).denote) (ha : a.eval ρ = liftVal (Pt := Pt) x) :
    (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = liftVal (Pt := Pt) (o.eval ℓ x) := by
  cases o
  case parsePreKeyWire =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .parsePreKeyWire x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval, ReductionDsl.hdrV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrV]
    rw [e2eDecodePreKeyMsg_eq, e2eHdrOfPreKeyMsg_eq]
  case partneredInnerBytes =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .partneredInnerBytes x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval, ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2ePartneredInnerBytes_eq]
  case wireInnerBytes =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .wireInnerBytes x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    rw [e2eWireInnerBytes_eq]
  case wrapPreKeyWire =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .wrapPreKeyWire x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval, ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2eExpectedPreKeyMsg_eq]
  case spqrStateSplit =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .spqrStateSplit x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.spqrSplitEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrSplitEval]
    have hvn : ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnToV (ℓ := ℓ) :=
      funext spqrVnToV_eq
    have hch : ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV (ℓ := ℓ) :=
      funext spqrChainToV_eq
    rw [hvn, hch]; rfl
  case spqrStateJoin =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .spqrStateJoin x))]
    rcases x with ⟨v1?, vn?, ch?⟩
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.spqrJoinEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrJoinEval]
    have hvn : ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV (ℓ := ℓ) :=
      funext spqrVnOfV_eq
    have hch : ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV (ℓ := ℓ) :=
      funext spqrChainOfV_eq
    rw [hvn, hch]
    cases v1? <;> rfl
  case checkShortCiphertext =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .checkShortCiphertext x))]
    rcases x with ⟨c, inner?⟩
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    cases inner? <;> rfl
  case splitWhisperWire =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .splitWhisperWire x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    cases x <;> rfl
  case ghostStateSplit =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .ghostStateSplit x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.ghostSplitEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostSplitEval]
    rw [partyToBool_eq]
  case ghostStateJoin =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .ghostStateJoin x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.ghostJoinEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostJoinEval]
    rw [boolToParty_eq]
  case encodeSessionRecord =>
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ .encodeSessionRecord x))]
    dsimp only [ReductionDsl.AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.e2eEncodeSessionRecord, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eEncodeSessionRecord,
      ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2eRecordExtras_eq]
  all_goals
    dsimp only [liftPureOpExpr]
    rw [eval_sessPureOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x)]
    refine Eq.trans ?_ (eq_of_heq (liftVal_heq (Pt := Pt) _)).symm
    rfl

private theorem liftCurveOpExpr_eval {Γ : List (Ty ASig)} (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc)))
    (ρ : Env Γ) (x : ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc).denote)
    (ha : a.eval ρ = liftVal (Pt := Pt) x) :
    (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).eval ρ =
      liftVal (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).eval cc x) := by
  cases cc <;>
  · dsimp only [liftCurveOpExpr]
    rw [eval_sessCurveOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x)]
    rfl

private theorem liftCryptoOpExpr_eval {Γ : List (Ty ASig)} (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ))) (ρ : Env Γ)
    (x : (c.dom ℓ).denote) (ha : a.eval ρ = liftVal (Pt := Pt) x) :
    (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).eval ρ =
      liftVal (Pt := Pt) (c.eval ℓ zeroPqxdhPrims C K x) := by
  match c with
  | .x25519 | .x25519Base | .pow8 | .isCanonical | .sigSign | .sigVerify
  | .kemKeyGen | .kemEncaps | .kemDecaps | .hkdfDerive96 =>
    rfl
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [liftCryptoOpExpr]
    rw [eval_sessSymOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval ℓ zeroPqxdhPrims C K _ x))]
    rfl
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv | .spqrChainNextKey =>
    dsimp only [liftCryptoOpExpr]
    rw [eval_sessSpqrKemOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval ℓ zeroPqxdhPrims C K _ x))]
    rfl
  | .spqrChainFromVn =>
    dsimp only [liftCryptoOpExpr]
    rw [eval_sessSpqrKemOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval ℓ zeroPqxdhPrims C K .spqrChainFromVn x))]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval,
      ReductionDsl.spqrChainFromVnEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainFromVnEval]
    rw [spqrVnOfV_eq]
    cases CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV x) with
    | error _ => rfl
    | ok c0 =>
      dsimp only
      exact congrArg some (spqrChainToV_eq c0.intoPb)
  | .spqrChainAddEpoch =>
    dsimp only [liftCryptoOpExpr]
    rw [eval_sessSpqrKemOp, ha, eq_of_heq (liftVal_heq (Pt := Pt) x),
        eq_of_heq (liftVal_heq (Pt := Pt) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval ℓ zeroPqxdhPrims C K .spqrChainAddEpoch x))]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval,
      ReductionDsl.spqrChainAddEpochEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainAddEpochEval]
    rw [spqrChainOfV_eq]
    cases CryptoVerification.LibsignalSpqrV1.Chain.fromPb (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV x.1) with
    | error _ => rfl
    | ok c0 =>
      dsimp only
      cases CryptoVerification.LibsignalSpqrV1.Chain.addEpoch
        (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F) c0
        { epoch := x.2.1, secret := CryptoGames.HMAC.keyToBytes32 x.2.2 } with
      | error _ => rfl
      | ok c1 =>
        dsimp only
        exact congrArg (Prod.mk false) (congrArg some (spqrChainToV_eq c1.intoPb))

theorem liftExpr_eval {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr EOps Γ t) (ρ : Env Γ) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).eval (liftEnv ρ) = liftVal (Pt := Pt) (e.eval ρ) := by
  induction e with
  | var v => exact liftEnv_get ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | sub a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | mulK _ a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | divK _ a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | modK _ a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | lt a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | eqN a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | not a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | and a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | ite c a b ihc iha ihb =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihc ρ]
    cases c.eval ρ
    · exact ihb ρ
    · exact iha ρ
  | pair a b iha ihb => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ]; rfl
  | fst a iha =>
    simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]
    rcases a.eval ρ with ⟨_, _⟩; rfl
  | snd a iha =>
    simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]
    rcases a.eval ρ with ⟨_, _⟩; rfl
  | inl a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | inr a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | some a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | caseOpt e n s ihe ihn ihs =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihe ρ]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihe ρ]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    dsimp only [liftExpr, ReductionDsl.Expr.eval]
    rcases o with o | (cc | c)
    · exact liftPureOpExpr_eval o (liftExpr a) (liftEnv ρ) (a.eval ρ) (iha ρ)
    · exact liftCurveOpExpr_eval cc (liftExpr a) (liftEnv ρ) (a.eval ρ) (iha ρ)
    · exact liftCryptoOpExpr_eval c (liftExpr a) (liftEnv ρ) (a.eval ρ) (iha ρ)
  | cons x l ihx ihl => simp only [liftExpr, ReductionDsl.Expr.eval, ihx ρ, ihl ρ]; rfl
  | len l ihl => simp only [liftExpr, ReductionDsl.Expr.eval, ihl ρ, liftVal, List.length_map]
  | take n l ihn ihl => simp only [liftExpr, ReductionDsl.Expr.eval, ihn ρ, ihl ρ, liftVal, List.map_take]
  | appendL Kb a b iha ihb =>
    simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ, ihb ρ, liftVal, ← List.map_append, List.map_take]
  | findB Kb l p ihl ihp =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_find_map liftVal (fun y => (liftExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | anyB Kb l p ihl ihp =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_any_map_eq liftVal (fun y => (liftExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | mapB Kb l f ihl ihf =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_map_map_eq liftVal liftVal (fun y => (liftExpr f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ)) (fun x => ihf (.cons x ρ)) ((l.eval ρ).take Kb)
  | foldrB Kb l z f ihl ihz ihf =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihl ρ, ihz ρ]
    change (((l.eval ρ).map liftVal).take Kb).foldr _ (liftVal (z.eval ρ)) = _
    rw [← List.map_take]
    exact list_foldr_map_eq liftVal liftVal
      (fun y acc => (liftExpr f).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      (z.eval ρ) ((l.eval ρ).take Kb)
  | tconst a iha => simp only [liftExpr, ReductionDsl.Expr.eval, iha ρ]; rfl
  | tget m i ihm ihi => simp only [liftExpr, ReductionDsl.Expr.eval, ihm ρ, ihi ρ]; rfl
  | tset m i a ihm ihi iha =>
    simp only [liftExpr, ReductionDsl.Expr.eval, ihm ρ, ihi ρ, iha ρ]
    funext j
    by_cases hj : j = i.eval ρ <;> simp [hj, liftVal]

@[reducible] def emptyE2EIface {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) :
    Iface ESig T where
  fwdU := I'.fwdU
  uCost := I'.uCost
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc g := g.elim
  dec g := g.elim
  qCost := Empty.elim
  smp := ReductionDsl.Samplers.empty

/-- Lift an oracle-free and sampler-free `Comp` from `Costed.e2eOps` into `atomicSessionOps`. -/
def liftCompEmpty {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T} :
    {Γ : List (Ty ESig)} → {t : Ty ESig} →
    Comp EOps (emptyE2EIface I') Γ t →
    Comp AOps I' (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .ret e => .ret (liftExpr e)
  | _, _, .bind c k => .bind (liftCompEmpty c) (liftCompEmpty k)
  | _, _, .ite b c d => .ite (liftExpr b) (liftCompEmpty c) (liftCompEmpty d)
  | _, _, .caseOpt e n s => .caseOpt (liftExpr e) (liftCompEmpty n) (liftCompEmpty s)
  | _, _, .caseSum e l r => .caseSum (liftExpr e) (liftCompEmpty l) (liftCompEmpty r)
  | _, _, .sample s _ => s.elim
  | _, _, .query g _ => g.elim
  | _, _, .iter n e body => .iter n (liftExpr e) (liftCompEmpty body)
  | _, _, .findM Kb l p => .findM Kb (liftExpr l) (liftCompEmpty p)
  | _, _, .anyM Kb l p => .anyM Kb (liftExpr l) (liftCompEmpty p)
  | _, _, .mapM Kb l f => .mapM Kb (liftExpr l) (liftCompEmpty f)
  | _, _, .consumeFirstM Kb l p mk => .consumeFirstM Kb (liftExpr l) (liftCompEmpty p) (liftExpr mk)
  | _, _, .foldM Kb l z f => .foldM Kb (liftExpr l) (liftExpr z) (liftCompEmpty f)

@[simp] theorem liftCompEmpty_queries {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).queries w ws = 0 := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [liftCompEmpty, ReductionDsl.Comp.queries, ih1, ih2]
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [liftCompEmpty, ReductionDsl.Comp.queries, ih]

theorem liftCompEmpty_cost {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).cost ≤ 32 * c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | bind _ _ hc hk =>
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | ite b _ _ hc hd =>
    have hb := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | caseOpt e _ _ hn hs =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | caseSum e _ _ hl hr =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e _ hb =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    have hm := mul_cost_step n _ _ hb
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | findM Kb l _ hp | anyM Kb l _ hp | mapM Kb l _ hp =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hm := mul_cost_step Kb _ _ hp
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk hp =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hmk := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk
    have hm := mul_cost_step2 Kb _ _ _ _ hp hmk
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ hf =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hz := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z
    have hm := mul_cost_step Kb _ _ hf
    simp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega

private theorem iterM_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (f' : β → m β) (f : α → m α) (hf : ∀ a, f' (g a) = g <$> f a) :
    ∀ (n : ℕ) (a : α), iterM f' n (g a) = g <$> iterM f n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun a' => ?_
    simpa [map_eq_bind_pure_comp] using iterM_map_eq g f' f hf n a'

private theorem findML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (q : β → m Bool) (p : α → m Bool) (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, findML q (xs.map g) = Option.map g <$> findML p xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hpq x, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine bind_congr fun b => ?_
    cases b
    · simpa [map_eq_bind_pure_comp] using findML_map_eq g q p hpq xs
    · simp

private theorem anyML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (q : β → m Bool) (p : α → m Bool) (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, anyML q (xs.map g) = anyML p xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hpq x]
    refine bind_congr fun b => ?_
    cases b
    · exact anyML_map_eq g q p hpq xs
    · rfl

private theorem mapML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}
    (g : α → β) (h : γ → δ) (f' : β → m δ) (f : α → m γ) (hf : ∀ x, f' (g x) = h <$> f x) :
    ∀ xs : List α, mapML f' (xs.map g) = List.map h <$> mapML f xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    refine bind_congr fun y => ?_
    have ih := mapML_map_eq g h f' f hf xs
    simp only [map_eq_bind_pure_comp, Function.comp_def] at ih
    rw [ih, bind_assoc]
    simp

private theorem consumeFirstML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (g : α → β) (q : β → m Bool) (p : α → m Bool) (mk' : β → β) (mk : α → α)
    (hpq : ∀ x, q (g x) = p x) (hmk : ∀ x, mk' (g x) = g (mk x)) :
    ∀ xs : List α, consumeFirstML q mk' (xs.map g) =
      (fun r => (r.1, r.2.map g)) <$> consumeFirstML p mk xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hpq x, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc]
    refine bind_congr fun b => ?_
    cases b
    · have ih := consumeFirstML_map_eq g q p mk' mk hpq hmk xs
      simp only [map_eq_bind_pure_comp, Function.comp_def] at ih
      rw [ih, bind_assoc]
      simp
    · simp [hmk x]

private theorem foldML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}
    (g : α → β) (h : γ → δ) (f' : β → δ → m δ) (f : α → γ → m γ)
    (hf : ∀ x acc, f' (g x) (h acc) = h <$> f x acc) :
    ∀ (xs : List α) (z : γ), foldML f' (h z) (xs.map g) = h <$> foldML f z xs
  | [], z => by simp [foldML]
  | x :: xs, z => by
    simp only [List.map_cons, foldML, hf x z, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    refine bind_congr fun z' => ?_
    simpa [map_eq_bind_pure_comp] using foldML_map_eq g h f' f hf xs z'

theorem liftCompEmpty_eval {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t) (ρ : Env Γ) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).eval (liftEnv ρ) =
      liftVal (Pt := Pt) <$> c.eval ρ := by
  induction c with
  | ret e => simp [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
  | bind c k ihc ihk =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, ihc ρ, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun x => ?_
    have ihx : (liftCompEmpty k).eval (.cons (liftVal x) (liftEnv ρ)) =
        liftVal <$> k.eval (.cons x ρ) := ihk (.cons x ρ)
    simpa [map_eq_bind_pure_comp] using ihx
  | ite b c d ihc ihd =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval b ρ]
    cases b.eval ρ
    · exact ihd ρ
    · exact ihc ρ
  | caseOpt e n s ihn ihs =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e body ihb =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    exact iterM_map_eq liftVal
      (fun y => (liftCompEmpty body).eval (.cons y (liftEnv ρ)))
      (fun x => body.eval (.cons x ρ))
      (fun x => ihb (.cons x ρ))
      n (e.eval ρ)
  | findM Kb l p ihp =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact findML_map_eq liftVal
      (fun y => (liftCompEmpty p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take Kb)
  | anyM Kb l p ihp =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    simpa [liftVal] using anyML_map_eq liftVal
      (fun y => (liftCompEmpty p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take Kb)
  | mapM Kb l f ihf =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact mapML_map_eq liftVal liftVal
      (fun y => (liftCompEmpty f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ))
      (fun x => ihf (.cons x ρ))
      ((l.eval ρ).take Kb)
  | consumeFirstM Kb l p mk ihp =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact consumeFirstML_map_eq liftVal
      (fun y => (liftCompEmpty p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun y => (liftExpr mk).eval (.cons y (liftEnv ρ)))
      (fun x => mk.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      (fun x => liftExpr_eval mk (.cons x ρ))
      ((l.eval ρ).take Kb)
  | foldM Kb l z f ihf =>
    simp only [liftCompEmpty, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftExpr_eval z ρ]
    change foldML _ (liftVal (z.eval ρ)) (((l.eval ρ).map liftVal).take Kb) = _
    rw [← List.map_take]
    exact foldML_map_eq liftVal liftVal
      (fun y acc => (liftCompEmpty f).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      ((l.eval ρ).take Kb) (z.eval ρ)

@[reducible] def coinE2EIface {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) :
    Iface ESig T where
  fwdU := I'.fwdU
  uCost := I'.uCost
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc g := g.elim
  dec g := g.elim
  qCost := Empty.elim
  smp := Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ

def coinE2ESamplers {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) :
    E2ECoinSamplers ℓ zeroPqxdhPrims C K decT encT (coinE2EIface I') :=
  mkE2ECoinSamplers I'.fwdU I'.uCost Empty Empty.elim Empty.elim (·.elim) (·.elim) Empty.elim

def liftSampComp [SampleableType Pt] {ι : Type} {T : OracleSpec ι} :
    (I' : Iface ASig T) → (hsmp : I'.smp = atomicSamplers ℓ Pt) → {Γ : List (Ty ASig)} →
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase) →
    Expr AOps Γ .unit →
    Comp AOps I' Γ (liftTy (Pt := Pt) ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ).sTy s))
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .bool, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩) .bool a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .index N, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩) (.index N) a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .base .bv256, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩)
      (.base .bv256) a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .base .bv512, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicSamplers ℓ Pt⟩)
      (.base .bv512) a

private theorem liftSampComp_queries_zero [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ASig)}
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase) (a : Expr AOps Γ .unit) (w : I'.Tag → ℕ) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s a).queries w (fun _ => 0) = 0 := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

private theorem liftSampComp_cost [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ASig)}
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase) (a : Expr AOps Γ .unit) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s a).cost = a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ).sCost s := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

private theorem liftSampComp_eval [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ESig)}
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase) (a : Expr EOps Γ .unit) (ρ : Env Γ) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s (liftExpr a)).eval (liftEnv ρ) =
      liftVal (Pt := Pt) <$> (ReductionDsl.Comp.sample (I := coinE2EIface I') s a).eval ρ := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> exact (id_map _).symm

/-- Lift a coin-sampling, oracle-free `Comp` from `Costed.e2eOps` into `atomicSessionOps`. -/
def liftCompCoins [SampleableType Pt] {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (hsmp : I'.smp = atomicSamplers ℓ Pt := by rfl) :
    {Γ : List (Ty ESig)} → {t : Ty ESig} →
    Comp EOps (coinE2EIface I') Γ t →
    Comp AOps I' (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .ret e => .ret (liftExpr e)
  | _, _, .bind c k => .bind (liftCompCoins hsmp c) (liftCompCoins hsmp k)
  | _, _, .ite b c d => .ite (liftExpr b) (liftCompCoins hsmp c) (liftCompCoins hsmp d)
  | _, _, .caseOpt e n s => .caseOpt (liftExpr e) (liftCompCoins hsmp n) (liftCompCoins hsmp s)
  | _, _, .caseSum e l r => .caseSum (liftExpr e) (liftCompCoins hsmp l) (liftCompCoins hsmp r)
  | _, _, .sample s a => liftSampComp I' hsmp s (liftExpr a)
  | _, _, .query g _ => g.elim
  | _, _, .iter n e body => .iter n (liftExpr e) (liftCompCoins hsmp body)
  | _, _, .findM Kb l p => .findM Kb (liftExpr l) (liftCompCoins hsmp p)
  | _, _, .anyM Kb l p => .anyM Kb (liftExpr l) (liftCompCoins hsmp p)
  | _, _, .mapM Kb l f => .mapM Kb (liftExpr l) (liftCompCoins hsmp f)
  | _, _, .consumeFirstM Kb l p mk =>
    .consumeFirstM Kb (liftExpr l) (liftCompCoins hsmp p) (liftExpr mk)
  | _, _, .foldM Kb l z f => .foldM Kb (liftExpr l) (liftExpr z) (liftCompCoins hsmp f)

@[simp] theorem liftCompCoins_queries_zero [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t) (w : I'.Tag → ℕ) :
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).queries w (fun _ => 0) = 0 := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [liftCompCoins, ReductionDsl.Comp.queries, ih1, ih2]
  | sample s a =>
    dsimp only [liftCompCoins]
    exact liftSampComp_queries_zero hsmp s (liftExpr a) w
  | query g _ => exact g.elim
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [liftCompCoins, ReductionDsl.Comp.queries, ih]

theorem liftCompCoins_cost [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t) :
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).cost ≤ 32 * c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | bind _ _ hc hk =>
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | ite b _ _ hc hd =>
    have hb := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | caseOpt e _ _ hn hs =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | caseSum e _ _ hl hr =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | sample s a =>
    have ha := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) a
    have hs := liftSampComp_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) hsmp s (liftExpr a)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost, coinE2EIface] at hs ⊢
    omega
  | query g _ => exact g.elim
  | iter n e _ hb =>
    have he := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    have hm := mul_cost_step n _ _ hb
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | findM Kb l _ hp | anyM Kb l _ hp | mapM Kb l _ hp =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hm := mul_cost_step Kb _ _ hp
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk hp =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hmk := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk
    have hm := mul_cost_step2 Kb _ _ _ _ hp hmk
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ hf =>
    have hl := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hz := liftExpr_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z
    have hm := mul_cost_step Kb _ _ hf
    simp only [liftCompCoins, ReductionDsl.Comp.cost]; omega

theorem liftCompCoins_eval [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t) (ρ : Env Γ) :
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).eval (liftEnv ρ) =
      liftVal (Pt := Pt) <$> c.eval ρ := by
  induction c with
  | ret e => simp [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
  | bind c k ihc ihk =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, ihc ρ, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun x => ?_
    have ihx : (liftCompCoins hsmp k).eval (.cons (liftVal x) (liftEnv ρ)) =
        liftVal <$> k.eval (.cons x ρ) := ihk (.cons x ρ)
    simpa [map_eq_bind_pure_comp] using ihx
  | ite b c d ihc ihd =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval b ρ]
    cases b.eval ρ
    · exact ihd ρ
    · exact ihc ρ
  | caseOpt e n s ihn ihs =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | sample s a =>
    dsimp only [liftCompCoins]
    exact liftSampComp_eval hsmp s a ρ
  | query g _ => exact g.elim
  | iter n e body ihb =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval e ρ]
    exact iterM_map_eq liftVal
      (fun y => (liftCompCoins hsmp body).eval (.cons y (liftEnv ρ)))
      (fun x => body.eval (.cons x ρ))
      (fun x => ihb (.cons x ρ))
      n (e.eval ρ)
  | findM Kb l p ihp =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact findML_map_eq liftVal
      (fun y => (liftCompCoins hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take Kb)
  | anyM Kb l p ihp =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    simpa [liftVal] using anyML_map_eq liftVal
      (fun y => (liftCompCoins hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take Kb)
  | mapM Kb l f ihf =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact mapML_map_eq liftVal liftVal
      (fun y => (liftCompCoins hsmp f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ))
      (fun x => ihf (.cons x ρ))
      ((l.eval ρ).take Kb)
  | consumeFirstM Kb l p mk ihp =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftVal, ← List.map_take]
    exact consumeFirstML_map_eq liftVal
      (fun y => (liftCompCoins hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun y => (liftExpr mk).eval (.cons y (liftEnv ρ)))
      (fun x => mk.eval (.cons x ρ))
      (fun x => (ihp (.cons x ρ)).trans (id_map _))
      (fun x => liftExpr_eval mk (.cons x ρ))
      ((l.eval ρ).take Kb)
  | foldM Kb l z f ihf =>
    simp only [liftCompCoins, ReductionDsl.Comp.eval, liftExpr_eval l ρ, liftExpr_eval z ρ]
    change foldML _ (liftVal (z.eval ρ)) (((l.eval ρ).map liftVal).take Kb) = _
    rw [← List.map_take]
    exact foldML_map_eq liftVal liftVal
      (fun y acc => (liftCompCoins hsmp f).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      ((l.eval ρ).take Kb) (z.eval ρ)

end Compiler

/-! ## Context renaming -/

section Renaming

variable {S0 : Sig} {O0 : Ops S0}

def liftRen {Γ₁ Γ₂ : List (Ty S0)} {u : Ty S0}
    (f : ∀ {t}, Var Γ₁ t → Var Γ₂ t) : ∀ {t}, Var (u :: Γ₁) t → Var (u :: Γ₂) t
  | _, .zero => .zero
  | _, .succ v => .succ (f v)

def pullEnv : {Γ₁ Γ₂ : List (Ty S0)} →
    (∀ {t}, Var Γ₁ t → Var Γ₂ t) → Env Γ₂ → Env Γ₁
  | [], _, _, _ => .nil
  | _ :: _, _, f, ρ => .cons (ρ.get (f .zero)) (pullEnv (fun v => f (.succ v)) ρ)

private theorem pullEnv_get : {Γ₁ Γ₂ : List (Ty S0)} →
    (f : ∀ {t}, Var Γ₁ t → Var Γ₂ t) → (ρ : Env Γ₂) → {t : Ty S0} → (v : Var Γ₁ t) →
    (pullEnv f ρ).get v = ρ.get (f v)
  | _ :: _, _, _, _, _, .zero => rfl
  | _ :: _, _, f, ρ, _, .succ v => pullEnv_get (fun w => f (.succ w)) ρ v

private theorem pullEnv_liftRen {Γ₁ Γ₂ : List (Ty S0)} {u : Ty S0}
    (f : ∀ {t}, Var Γ₁ t → Var Γ₂ t) (x : u.denote) (ρ : Env Γ₂) :
    pullEnv (liftRen f) (.cons x ρ) = .cons x (pullEnv f ρ) := by
  have hsucc : ∀ {Δ : List (Ty S0)} (g : ∀ {t}, Var Δ t → Var Γ₂ t),
      pullEnv (fun v => ReductionDsl.Var.succ (g v)) (.cons x ρ) = pullEnv g ρ := by
    intro Δ
    induction Δ with
    | nil => intro _; rfl
    | cons _ _ ih => intro g; exact congrArg (ReductionDsl.Env.cons _) (ih (fun v => g (.succ v)))
  exact congrArg (ReductionDsl.Env.cons x) (hsucc f)

def renExpr : {Γ₁ Γ₂ : List (Ty S0)} → {t : Ty S0} →
    (∀ {u}, Var Γ₁ u → Var Γ₂ u) → Expr O0 Γ₁ t → Expr O0 Γ₂ t
  | _, _, _, f, .var v => .var (f v)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .bool b => .bool b
  | _, _, _, _, .nat n => .nat n
  | _, _, _, f, .add a b => .add (renExpr f a) (renExpr f b)
  | _, _, _, f, .sub a b => .sub (renExpr f a) (renExpr f b)
  | _, _, _, f, .mulK k a => .mulK k (renExpr f a)
  | _, _, _, f, .divK k a => .divK k (renExpr f a)
  | _, _, _, f, .modK k a => .modK k (renExpr f a)
  | _, _, _, f, .lt a b => .lt (renExpr f a) (renExpr f b)
  | _, _, _, f, .eqN a b => .eqN (renExpr f a) (renExpr f b)
  | _, _, _, f, .not a => .not (renExpr f a)
  | _, _, _, f, .and a b => .and (renExpr f a) (renExpr f b)
  | _, _, _, f, .ite c a b => .ite (renExpr f c) (renExpr f a) (renExpr f b)
  | _, _, _, f, .pair a b => .pair (renExpr f a) (renExpr f b)
  | _, _, _, f, .fst a => .fst (renExpr f a)
  | _, _, _, f, .snd a => .snd (renExpr f a)
  | _, _, _, f, .inl a => .inl (renExpr f a)
  | _, _, _, f, .inr a => .inr (renExpr f a)
  | _, _, _, _, .none => .none
  | _, _, _, f, .some a => .some (renExpr f a)
  | _, _, _, f, .caseOpt e n s => .caseOpt (renExpr f e) (renExpr f n) (renExpr (liftRen f) s)
  | _, _, _, f, .caseSum e l r =>
    .caseSum (renExpr f e) (renExpr (liftRen f) l) (renExpr (liftRen f) r)
  | _, _, _, f, .letE e b => .letE (renExpr f e) (renExpr (liftRen f) b)
  | _, _, _, f, .op o a => .op o (renExpr f a)
  | _, _, _, _, .nil => .nil
  | _, _, _, f, .cons x l => .cons (renExpr f x) (renExpr f l)
  | _, _, _, f, .len l => .len (renExpr f l)
  | _, _, _, f, .take n l => .take (renExpr f n) (renExpr f l)
  | _, _, _, f, .appendL Kb a b => .appendL Kb (renExpr f a) (renExpr f b)
  | _, _, _, f, .findB Kb l p => .findB Kb (renExpr f l) (renExpr (liftRen f) p)
  | _, _, _, f, .anyB Kb l p => .anyB Kb (renExpr f l) (renExpr (liftRen f) p)
  | _, _, _, f, .mapB Kb l g => .mapB Kb (renExpr f l) (renExpr (liftRen f) g)
  | _, _, _, f, .foldrB Kb l z g =>
    .foldrB Kb (renExpr f l) (renExpr f z) (renExpr (liftRen (liftRen f)) g)
  | _, _, _, f, .tconst a => .tconst (renExpr f a)
  | _, _, _, f, .tget m i => .tget (renExpr f m) (renExpr f i)
  | _, _, _, f, .tset m i a => .tset (renExpr f m) (renExpr f i) (renExpr f a)

@[simp] theorem renExpr_cost {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) :
    (renExpr f e).cost = e.cost := by
  induction e generalizing Γ₂ <;> simp [renExpr, ReductionDsl.Expr.cost, *]

theorem renExpr_eval {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) (ρ : Env Γ₂) :
    (renExpr f e).eval ρ = e.eval (pullEnv f ρ) := by
  induction e generalizing Γ₂ with
  | var v => exact (pullEnv_get f ρ v).symm
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb | and _ _ iha ihb
  | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb | appendL _ _ _ iha ihb
  | tget _ _ iha ihb =>
    simp [renExpr, ReductionDsl.Expr.eval, iha, ihb]
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | op _ _ iha | len _ iha | tconst _ iha =>
    simp [renExpr, ReductionDsl.Expr.eval, iha]
  | ite _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp [renExpr, ReductionDsl.Expr.eval, ihc, iha, ihb]
  | caseOpt e n s ihe ihn ihs =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihe f ρ]
    rcases e.eval (pullEnv f ρ) with _ | x <;> dsimp only
    · exact ihn f ρ
    · rw [ihs (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | caseSum e l r ihe ihl ihr =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihe f ρ]
    rcases e.eval (pullEnv f ρ) with x | y <;> dsimp only
    · rw [ihl (liftRen f) (.cons x ρ), pullEnv_liftRen]
    · rw [ihr (liftRen f) (.cons y ρ), pullEnv_liftRen]
  | letE e b ihe ihb =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihe f ρ, ihb (liftRen f), pullEnv_liftRen]
  | findB Kb l p ihl ihp =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihl f ρ]
    congr 1; funext x
    rw [ihp (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | anyB Kb l p ihl ihp =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihl f ρ]
    congr 1; funext x
    rw [ihp (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | mapB Kb l g ihl ihg =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihl f ρ]
    congr 1; funext x
    rw [ihg (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | foldrB Kb l z g ihl ihz ihg =>
    simp only [renExpr, ReductionDsl.Expr.eval, ihl f ρ, ihz f ρ]
    congr 2; funext x acc
    rw [ihg (liftRen (liftRen f)) (.cons x (.cons acc ρ)), pullEnv_liftRen, pullEnv_liftRen]

def renComp {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} :
    {Γ₁ Γ₂ : List (Ty S0)} → {t : Ty S0} →
    (∀ {u}, Var Γ₁ u → Var Γ₂ u) → Comp O0 I0 Γ₁ t → Comp O0 I0 Γ₂ t
  | _, _, _, f, .ret e => .ret (renExpr f e)
  | _, _, _, f, .bind c k => .bind (renComp f c) (renComp (liftRen f) k)
  | _, _, _, f, .ite b c d => .ite (renExpr f b) (renComp f c) (renComp f d)
  | _, _, _, f, .caseOpt e n s => .caseOpt (renExpr f e) (renComp f n) (renComp (liftRen f) s)
  | _, _, _, f, .caseSum e l r =>
    .caseSum (renExpr f e) (renComp (liftRen f) l) (renComp (liftRen f) r)
  | _, _, _, f, .sample s a => .sample s (renExpr f a)
  | _, _, _, f, .query g a => .query g (renExpr f a)
  | _, _, _, f, .iter n e body => .iter n (renExpr f e) (renComp (liftRen f) body)
  | _, _, _, f, .findM Kb l p => .findM Kb (renExpr f l) (renComp (liftRen f) p)
  | _, _, _, f, .anyM Kb l p => .anyM Kb (renExpr f l) (renComp (liftRen f) p)
  | _, _, _, f, .mapM Kb l g => .mapM Kb (renExpr f l) (renComp (liftRen f) g)
  | _, _, _, f, .consumeFirstM Kb l p mk =>
    .consumeFirstM Kb (renExpr f l) (renComp (liftRen f) p) (renExpr (liftRen f) mk)
  | _, _, _, f, .foldM Kb l z g =>
    .foldM Kb (renExpr f l) (renExpr f z) (renComp (liftRen (liftRen f)) g)

@[simp] theorem renComp_queries {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t)
    (w : I0.Tag → ℕ) (ws : I0.smp.Samp → ℕ) :
    (renComp f c).queries w ws = c.queries w ws := by
  induction c generalizing Γ₂ <;> simp [renComp, ReductionDsl.Comp.queries, *]

@[simp] theorem renComp_cost {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) :
    (renComp f c).cost = c.cost := by
  induction c generalizing Γ₂ <;> simp [renComp, ReductionDsl.Comp.cost, renExpr_cost, *]

theorem renComp_eval {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) (ρ : Env Γ₂) :
    (renComp f c).eval ρ = c.eval (pullEnv f ρ) := by
  induction c generalizing Γ₂ with
  | ret e => simp [renComp, ReductionDsl.Comp.eval, renExpr_eval]
  | bind c k ihc ihk =>
    simp only [renComp, ReductionDsl.Comp.eval, ihc f ρ]
    refine bind_congr fun x => ?_
    rw [ihk (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | ite b c d ihc ihd =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f b ρ]
    cases b.eval (pullEnv f ρ)
    · exact ihd f ρ
    · exact ihc f ρ
  | caseOpt e n s ihn ihs =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f e ρ]
    rcases e.eval (pullEnv f ρ) with _ | x <;> dsimp only
    · exact ihn f ρ
    · rw [ihs (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | caseSum e l r ihl ihr =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f e ρ]
    rcases e.eval (pullEnv f ρ) with x | y <;> dsimp only
    · rw [ihl (liftRen f) (.cons x ρ), pullEnv_liftRen]
    · rw [ihr (liftRen f) (.cons y ρ), pullEnv_liftRen]
  | sample s a => simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f a ρ]
  | query g a =>
    dsimp only [renComp, ReductionDsl.Comp.eval]
    rw [renExpr_eval f a ρ]
  | iter n e body ihb =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f e ρ]
    congr 1; funext x
    rw [ihb (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | findM Kb l p ihp =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f l ρ]
    congr 1; funext x
    rw [ihp (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | anyM Kb l p ihp =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f l ρ]
    congr 1; funext x
    rw [ihp (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | mapM Kb l g ihg =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f l ρ]
    congr 1; funext x
    rw [ihg (liftRen f) (.cons x ρ), pullEnv_liftRen]
  | consumeFirstM Kb l p mk ihp =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f l ρ]
    congr 1
    · funext x; rw [ihp (liftRen f) (.cons x ρ), pullEnv_liftRen]
    · funext x; rw [renExpr_eval (liftRen f) mk (.cons x ρ), pullEnv_liftRen]
  | foldM Kb l z g ihg =>
    simp only [renComp, ReductionDsl.Comp.eval, renExpr_eval f l ρ, renExpr_eval f z ρ]
    congr 1; funext x acc
    rw [ihg (liftRen (liftRen f)) (.cons x (.cons acc ρ)), pullEnv_liftRen, pullEnv_liftRen]

def wk1Ren {a : Ty S0} {Γ : List (Ty S0)} : ∀ {t}, Var [a] t → Var (a :: Γ) t
  | _, .zero => .zero

def wk1Expr {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b) : Expr O0 (a :: Γ) b :=
  renExpr wk1Ren e

@[simp] theorem wk1Expr_cost {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b) :
    (wk1Expr (Γ := Γ) e).cost = e.cost :=
  renExpr_cost wk1Ren e

@[simp] theorem wk1Expr_eval {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b)
    (x : a.denote) (ρ : Env Γ) :
    (wk1Expr e).eval (.cons x ρ) = e.eval (.cons x .nil) :=
  renExpr_eval wk1Ren e (.cons x ρ)

def wk1Comp {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} {a b : Ty S0} {Γ : List (Ty S0)}
    (c : Comp O0 I0 [a] b) : Comp O0 I0 (a :: Γ) b :=
  renComp wk1Ren c

@[simp] theorem wk1Comp_queries {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b)
    (w : I0.Tag → ℕ) (ws : I0.smp.Samp → ℕ) :
    (wk1Comp (Γ := Γ) c).queries w ws = c.queries w ws :=
  renComp_queries wk1Ren c w ws

@[simp] theorem wk1Comp_cost {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b) :
    (wk1Comp (Γ := Γ) c).cost = c.cost :=
  renComp_cost wk1Ren c

@[simp] theorem wk1Comp_eval {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b)
    (x : a.denote) (ρ : Env Γ) :
    (wk1Comp c).eval (.cons x ρ) = c.eval (.cons x .nil) :=
  renComp_eval wk1Ren c (.cons x ρ)

end Renaming

/-! ## SPQR and Double Ratchet step simulators -/

section StepSimulators

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT

/-- Closed SPQR V1 send simulator over `atomicSessionOps` and any `I' : Iface ASig T`. -/
def spqrSendAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) BV512)) :
    Comp AOps I' Γ (.opt (.prod (B 32) (.prod (.opt BV256) (B 32)))) :=
  .bind (.ret inpE)
    (wk1Comp
      (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (I' := I')
        (spqrSendComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
          (emptyE2EIface I') (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512]) .v0)))

theorem spqrSendAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) BV512))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).queries w ws = 0 := by
  simp [spqrSendAtomicC, ReductionDsl.Comp.queries]

theorem spqrSendAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) BV512)) :
    (spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤ inpE.cost + 32 * 67000 := by
  have h1 := liftCompEmpty_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (spqrSendComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
      (emptyE2EIface I') (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512]) .v0)
  have h2 := spqrSendComp_cost (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512] (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))
  simp only [spqrSendAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem spqrSendAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) BV512)) (ρ : Env Γ)
    (htight : TopStateTight C.F K (inpE.eval ρ).1) :
    (spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).eval ρ =
      pure (
        let (pq, r) := inpE.eval ρ
        let spqr := CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
        if spqr.sendPanics pq r then none
        else (spqr.send pq r).map fun (pq', saltVec?, pqMsg) =>
          (pq', (saltVec?.map (fun v => bytesToKey32 v.toList), pqMsg))) := by
  rcases h : inpE.eval ρ with ⟨st, coins⟩
  rw [h] at htight
  simp only [spqrSendAtomicC, ReductionDsl.Comp.eval, pure_bind, h, wk1Comp_eval]
  let body := spqrSendComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512]) .v0
  have hev := liftCompEmpty_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') body (.cons (st, coins) .nil)
  have hspqr := spqrSendComp_eval (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512] (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))
    (.cons (st, coins) .nil) htight
  change (liftCompEmpty body).eval (.cons (st, coins) .nil) =
    liftVal (Pt := Pt) <$> body.eval (.cons (st, coins) .nil) at hev
  change body.eval (.cons (st, coins) .nil) = _ at hspqr
  change (liftCompEmpty body).eval (.cons (st, coins) .nil) = _
  rw [hev, hspqr]
  simp only [map_pure]
  exact congrArg pure (eq_of_heq (liftVal_heq (Pt := Pt)
    (t := .opt (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (.prod (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))) _))

/-- Closed SPQR V1 receive simulator over `atomicSessionOps` and any `I' : Iface ASig T`. -/
def spqrRecvAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (B 32))) :
    Comp AOps I' Γ (.opt (.prod (B 32) (.opt BV256))) :=
  .bind (.ret inpE)
    (wk1Comp
      (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (I' := I')
        (spqrRecvComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
          (emptyE2EIface I') (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)]) .v0)))

theorem spqrRecvAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (B 32)))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).queries w ws = 0 := by
  simp [spqrRecvAtomicC, ReductionDsl.Comp.queries]

theorem spqrRecvAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (B 32))) :
    (spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤ inpE.cost + 32 * 4100010 := by
  have h1 := liftCompEmpty_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (spqrRecvComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
      (emptyE2EIface I') (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)]) .v0)
  have h2 := spqrRecvComp_cost (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)] (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))
  simp only [spqrRecvAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem spqrRecvAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (B 32))) (ρ : Env Γ)
    (htight : TopStateTight C.F K (inpE.eval ρ).1) :
    (spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).eval ρ =
      pure (
        let (pq, pqMsg) := inpE.eval ρ
        let spqr := CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
        if spqr.recvPanics pq pqMsg then none
        else match spqr.recv pq pqMsg with
          | .ok (pq', saltVec?) =>
            some (pq', saltVec?.map (fun v => bytesToKey32 v.toList))
          | .error _ => none) := by
  rcases h : inpE.eval ρ with ⟨st, msg⟩
  rw [h] at htight
  simp only [spqrRecvAtomicC, ReductionDsl.Comp.eval, pure_bind, h, wk1Comp_eval]
  let body := spqrRecvComp (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (Γ := [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)]) .v0
  have hev := liftCompEmpty_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') body (.cons (st, msg) .nil)
  have hspqr := spqrRecvComp_eval (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)] (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))
    (.cons (st, msg) .nil) htight
  change (liftCompEmpty body).eval (.cons (st, msg) .nil) =
    liftVal (Pt := Pt) <$> body.eval (.cons (st, msg) .nil) at hev
  change body.eval (.cons (st, msg) .nil) = _ at hspqr
  change (liftCompEmpty body).eval (.cons (st, msg) .nil) = _
  rw [hev, hspqr]
  simp only [map_pure]
  exact congrArg pure (eq_of_heq (liftVal_heq (Pt := Pt)
    (t := .opt (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) _))

/-- Full Double Ratchet + SPQR V1 `Params.send` simulator over `atomicSessionOps`. -/
def drSendAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    Comp AOps I' Γ (.prod GhostStT (B 32)) :=
  .bind (.ret inpE)
    (wk1Comp
      (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (I' := I')
        (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
          (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)))

theorem drSendAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512)))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).queries w ws = 0 := by
  simp [drSendAtomicC, ReductionDsl.Comp.queries]

theorem drSendAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 32 * 67810 + 320 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)
  have h2 := drSendC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))
  simp only [drSendAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem drSendAtomicC_eval_params {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) (ρ : Env Γ)
    (idA idB : IdentityKey) (hg : PartyReachInv C K (inpE.eval ρ).1) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).eval ρ =
      pure ((paramsIdsWithSpqr C
        (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB).send
        (inpE.eval ρ).1 (inpE.eval ρ).2.1.toList (inpE.eval ρ).2.2) := by
  rcases h : inpE.eval ρ with ⟨g, ⟨m, r⟩⟩
  rw [h] at hg
  simp only [drSendAtomicC, ReductionDsl.Comp.eval, pure_bind, h, wk1Comp_eval]
  let body := drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0
  have hev := liftCompEmpty_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') body (.cons (g, (m, r)) .nil)
  have hdr := drSendC_eval_params (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))
    (.cons (g, (m, r)) .nil) idA idB hg
  change (liftCompEmpty body).eval (.cons (g, (m, r)) .nil) =
    liftVal (Pt := Pt) <$> body.eval (.cons (g, (m, r)) .nil) at hev
  change body.eval (.cons (g, (m, r)) .nil) =
    pure ((paramsIdsWithSpqr C
      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB).send
      g m.toList r) at hdr
  change (liftCompEmpty body).eval (.cons (g, (m, r)) .nil) = _
  rw [hev, hdr]
  simp only [map_pure]
  exact congrArg pure (eq_of_heq (liftVal_heq (Pt := Pt)
    (t := .prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)) _))

@[reducible] def drRecvAtomicOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .opt (.prod GhostStT (.prod .nat (.prod .nat PlainT)))

/-- Full Double Ratchet + SPQR V1 `Params.receive` simulator over `atomicSessionOps`. -/
def drReceiveAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    Comp AOps I' Γ (drRecvAtomicOutT ℓ Pt) :=
  .bind (.ret inpE)
    (wk1Comp
      (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (I' := I')
        (drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
          (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0)))

theorem drReceiveAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256)))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).queries w ws = 0 := by
  simp [drReceiveAtomicC, ReductionDsl.Comp.queries]

theorem drReceiveAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 32 * 5104010 + 256 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0)
  have h2 := drReceiveC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)))
  simp only [drReceiveAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0, ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem drReceiveAtomicC_eval_params {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) (ρ : Env Γ)
    (idA idB : IdentityKey) (hg : PartyReachInv C K (inpE.eval ρ).1) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).eval ρ =
      pure (
        ((paramsIdsWithSpqr C
          (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB).receive
          (inpE.eval ρ).1 (inpE.eval ρ).2.1 (inpE.eval ρ).2.2).map
        fun (g', t, idx, ptBytes) => (g', (t, (idx, padOrTruncatePlain ℓ ptBytes)))) := by
  rcases h : inpE.eval ρ with ⟨g, ⟨c, rc⟩⟩
  rw [h] at hg
  simp only [drReceiveAtomicC, ReductionDsl.Comp.eval, pure_bind, h, wk1Comp_eval]
  let body := drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0
  have hev := liftCompEmpty_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I') body (.cons (g, (c, rc)) .nil)
  have hdr := drReceiveC_eval_params (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT)
    (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32) Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)))
    (.cons (g, (c, rc)) .nil) idA idB hg
  change (liftCompEmpty body).eval (.cons (g, (c, rc)) .nil) =
    liftVal (Pt := Pt) <$> body.eval (.cons (g, (c, rc)) .nil) at hev
  change body.eval (.cons (g, (c, rc)) .nil) =
    pure (((paramsIdsWithSpqr C
      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB).receive
      g c rc).map fun (g', t, idx, ptBytes) => (g', (t, (idx, padOrTruncatePlain ℓ ptBytes)))) at hdr
  change (liftCompEmpty body).eval (.cons (g, (c, rc)) .nil) = _
  rw [hev, hdr]
  simp only [map_pure]
  exact congrArg pure (eq_of_heq (liftVal_heq (Pt := Pt) (t := drRecvOutT ℓ) _))

end StepSimulators

end Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
