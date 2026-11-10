/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import

/-!
# Expression and Coin-Computation Lifter to `atomicE2EOps`

Provides a cost- and size-preserving lifter for expressions and coin-only computations from
`e2eOps` into `atomicE2EOps`, together with bounded list lookup and update combinators.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag
  atomicSig atomicE2EOps atomicBaseSamplers AtomicBaseUnif
  AtomicPureOp AtomicCurveCheckOp AtomicSymOp AtomicSpqrKemOp AtomicPqxdhOp
  bits iterM findML anyML mapML consumeFirstML foldML)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E.Costed (E2EPureOp E2ECurveCheckOp E2ECryptoOp E2EUnifBase
  e2eSig e2eOps e2eSamplers)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftSort liftTy liftCtx liftVal liftVal_heq liftTy_denote_eq liftVar liftEnv liftEnv_get
   readProstVarint_eq splitSpqrPrev_eq)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.DrSessionSim (E2ECoinSamplers e2eStepACoinSamplers)

/-! ## Lifting from `e2eOps` to `atomicE2EOps` -/

@[expose] def liftPureOp : E2EPureOp → AtomicPureOp
  | .pbytesLit w v => .pbytesLit w v | .pbytesCat m n => .pbytesCat m n
  | .pbytesCons b w => .pbytesCons b w | .pbytesWiden w d => .pbytesWiden w d
  | .pbytesTakeK w k => .pbytesTakeK w k | .pbytesTake w => .pbytesTake w
  | .pbytesDrop w => .pbytesDrop w | .pbytesLen w => .pbytesLen w | .pbytesEq m n => .pbytesEq m n
  | .bytesLit w v => .bytesLit w v | .bytesCat m n => .bytesCat m n
  | .bytesCons b w => .bytesCons b w | .bytesWiden w d => .bytesWiden w d
  | .bytesTakeK w k => .bytesTakeK w k | .bytesTake w => .bytesTake w
  | .bytesDrop w => .bytesDrop w | .bytesLen w => .bytesLen w | .bytesEq m n => .bytesEq m n
  | .bytesLtOp m n => .bytesLtOp m n | .pbytesToBytes w => .pbytesToBytes w
  | .bytesToPbytes w => .bytesToPbytes w | .pu32Lit k => .pu32Lit k | .pu32OfNat => .pu32OfNat
  | .pu32ToNat => .pu32ToNat | .pu32Eq => .pu32Eq | .pu32ToU32 => .pu32ToU32
  | .u32ToPu32 => .u32ToPu32 | .u8Lit v => .u8Lit v | .u8OfNat => .u8OfNat | .u8ToNat => .u8ToNat
  | .u8Eq => .u8Eq | .u8Lt => .u8Lt | .u32Lit v => .u32Lit v | .u32OfNat => .u32OfNat
  | .u32ToNat => .u32ToNat | .u32Eq => .u32Eq | .u32Lt => .u32Lt | .u32Add => .u32Add
  | .u32Sub => .u32Sub | .u32BeBytes => .u32BeBytes | .u64Lit v => .u64Lit v
  | .u64OfNat => .u64OfNat | .u64ToNat => .u64ToNat | .u64Eq => .u64Eq | .u64Lt => .u64Lt
  | .u64Add => .u64Add | .u64Sub => .u64Sub | .u64Trunc8 => .u64Trunc8 | .finVal n => .finVal n
  | .finEq n => .finEq n | .bv128Eq => .bv128Eq | .bv256Lit v => .bv256Lit v
  | .bv256Eq => .bv256Eq | .bv256ToPbytes32 => .bv256ToPbytes32
  | .pbytesToBv256 => .pbytesToBv256 | .bv256ToBytes32 => .bv256ToBytes32
  | .bytesToBv256 => .bytesToBv256 | .bv512Lit v => .bv512Lit v
  | .bv512ToBytes64 => .bv512ToBytes64 | .idKeyOfPbytes => .idKeyOfPbytes
  | .idKeySerialize => .idKeySerialize | .idKeyEq => .idKeyEq | .pkOfPbytes => .pkOfPbytes
  | .pkDeserialize => .pkDeserialize | .pkSerialize => .pkSerialize | .pkEq => .pkEq
  | .plainDefault => .plainDefault | .plainToBytes => .plainToBytes
  | .bytesToPlain => .bytesToPlain | .plainEq => .plainEq
  | .checkShortCiphertext => .checkShortCiphertext | .parsePreKeyWire => .parsePreKeyWire
  | .partneredInnerBytes => .partneredInnerBytes | .wireInnerBytes => .wireInnerBytes
  | .splitWhisperWire => .splitWhisperWire | .isValidSignalWire => .isValidSignalWire
  | .signalMsgParse => .signalMsgParse | .wrapWhisperWire => .wrapWhisperWire
  | .wrapPreKeyWire => .wrapPreKeyWire | .spqrParsePreamble => .spqrParsePreamble
  | .spqrAssembleMsg => .spqrAssembleMsg | .spqrStateSplit => .spqrStateSplit
  | .spqrStateJoin => .spqrStateJoin | .ghostStateSplit => .ghostStateSplit
  | .ghostStateJoin => .ghostStateJoin | .encodeSessionRecord => .encodeSessionRecord

@[expose] def liftCurveCheckOp : E2ECurveCheckOp → AtomicCurveCheckOp
  | .decEncCheck => .decEncCheck
  | .checkRatchetKeyOnCurve => .checkRatchetKeyOnCurve

@[expose] def liftE2EOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eOps ℓ P C K decT encT).Op → (atomicE2EOps ℓ P C K decT encT).Op
  | .inl o => .inl (.inl (liftPureOp o))
  | .inr (.inl cc) => .inl (.inr (liftCurveCheckOp cc))
  | .inr (.inr c) =>
    match c with
    | .x25519 => .inr (.inr (.inr (.inr .x25519))) | .x25519Base => .inr (.inr (.inr (.inr .x25519Base)))
    | .pow8 => .inr (.inr (.inr (.inr .pow8))) | .isCanonical => .inr (.inr (.inr (.inr .isCanonical)))
    | .sigSign => .inr (.inr (.inr (.inr .sigSign))) | .sigVerify => .inr (.inr (.inr (.inr .sigVerify)))
    | .kemKeyGen => .inr (.inr (.inr (.inr .kemKeyGen))) | .kemEncaps => .inr (.inr (.inr (.inr .kemEncaps)))
    | .kemDecaps => .inr (.inr (.inr (.inr .kemDecaps))) | .hkdfDerive96 => .inr (.inr (.inr (.inr .hkdfDerive96)))
    | .sessionKeyPairGen => .inr (.inr (.inl .sessionKeyPairGen))
    | .sessionRootCreateChain => .inr (.inr (.inl .sessionRootCreateChain))
    | .chainStep => .inr (.inr (.inl .chainStep)) | .deriveMsgKeys => .inr (.inr (.inl .deriveMsgKeys))
    | .aes256CbcEnc => .inr (.inr (.inl .aes256CbcEnc)) | .aes256CbcDec => .inr (.inr (.inl .aes256CbcDec))
    | .signalMsgEncode => .inr (.inr (.inl .signalMsgEncode))
    | .signalMsgVerifyMac => .inr (.inr (.inl .signalMsgVerifyMac))
    | .spqrV1InitOp => .inr (.inr (.inr (.inl .spqrV1InitOp)))
    | .spqrNegotiateInit => .inr (.inr (.inr (.inl .spqrNegotiateInit)))
    | .spqrBraidSend => .inr (.inr (.inr (.inl .spqrBraidSend)))
    | .spqrBraidRecv => .inr (.inr (.inr (.inl .spqrBraidRecv)))
    | .spqrChainFromVn => .inr (.inr (.inr (.inl .spqrChainFromVn)))
    | .spqrChainAddEpoch => .inr (.inr (.inr (.inl .spqrChainAddEpoch)))
    | .spqrChainNextKey => .inr (.inr (.inr (.inl .spqrChainNextKey)))

@[simp] theorem liftE2EOp_dom {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o) =
      liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).dom o) := by
  rcases o with o | cc | c
  · cases o <;> rfl
  · cases cc <;> rfl
  · cases c <;> rfl

@[simp] theorem liftE2EOp_cod {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cod (liftE2EOp (Pt := Pt) o) =
      liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).cod o) := by
  rcases o with o | cc | c
  · cases o <;> rfl
  · cases cc <;> rfl
  · cases c <;> rfl

@[simp] theorem liftE2EOp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cost (liftE2EOp (Pt := Pt) o) =
      (e2eOps ℓ P C K decT encT).cost o := by
  rcases o with o | cc | c
  · cases o <;> rfl
  · cases cc <;> rfl
  · cases c <;> rfl

private theorem liftE2EOp_opSize {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).opSize (liftE2EOp (Pt := Pt) o) =
      (e2eOps ℓ P C K decT encT).opSize o := by
  rcases o with o | cc | c
  · cases o <;> rfl
  · cases cc <;> rfl
  · cases c <;> rfl

@[expose] def castExprTy {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : Expr O Γ u :=
  h ▸ e

@[simp] theorem castExprTy_cost {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : (castExprTy h e).cost = e.cost := by
  cases h; rfl

@[simp] theorem castExprTy_size {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) : (castExprTy h e).size = e.size := by
  cases h; rfl

private theorem castExprTy_eval_heq {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (h : t = u) (e : Expr O Γ t) (ρ : Env Γ) :
    HEq ((castExprTy h e).eval ρ) (e.eval ρ) := by
  cases h; rfl

/-- Lift an `e2eOps` expression into `atomicE2EOps`. -/
@[expose] def liftE2EExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    Expr (e2eOps ℓ P C K decT encT) Γ t →
    Expr (atomicE2EOps ℓ P C K decT encT) (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .var v => .var (liftVar v)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .sub a b => .sub (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .mulK k e => .mulK k (liftE2EExpr e)
  | _, _, .divK k e => .divK k (liftE2EExpr e)
  | _, _, .modK k e => .modK k (liftE2EExpr e)
  | _, _, .lt a b => .lt (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .eqN a b => .eqN (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .not e => .not (liftE2EExpr e)
  | _, _, .and a b => .and (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .ite c t f => .ite (liftE2EExpr c) (liftE2EExpr t) (liftE2EExpr f)
  | _, _, .pair a b => .pair (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .fst e => .fst (liftE2EExpr e)
  | _, _, .snd e => .snd (liftE2EExpr e)
  | _, _, .inl e => .inl (liftE2EExpr e)
  | _, _, .inr e => .inr (liftE2EExpr e)
  | _, _, .none => .none
  | _, _, .some e => .some (liftE2EExpr e)
  | _, _, .caseOpt e n s => .caseOpt (liftE2EExpr e) (liftE2EExpr n) (liftE2EExpr s)
  | _, _, .caseSum e l r => .caseSum (liftE2EExpr e) (liftE2EExpr l) (liftE2EExpr r)
  | _, _, .letE a b => .letE (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .op o e =>
    castExprTy (liftE2EOp_cod (Pt := Pt) o)
      (.op (liftE2EOp (Pt := Pt) o)
        (castExprTy (liftE2EOp_dom (Pt := Pt) o).symm (liftE2EExpr e)))
  | _, _, .nil => .nil
  | _, _, .cons x xs => .cons (liftE2EExpr x) (liftE2EExpr xs)
  | _, _, .len xs => .len (liftE2EExpr xs)
  | _, _, .take n xs => .take (liftE2EExpr n) (liftE2EExpr xs)
  | _, _, .appendL K xs ys => .appendL K (liftE2EExpr xs) (liftE2EExpr ys)
  | _, _, .findB K xs p => .findB K (liftE2EExpr xs) (liftE2EExpr p)
  | _, _, .anyB K xs p => .anyB K (liftE2EExpr xs) (liftE2EExpr p)
  | _, _, .mapB K xs f => .mapB K (liftE2EExpr xs) (liftE2EExpr f)
  | _, _, .foldrB K xs z f => .foldrB K (liftE2EExpr xs) (liftE2EExpr z) (liftE2EExpr f)
  | _, _, .tconst d => .tconst (liftE2EExpr d)
  | _, _, .tget m i => .tget (liftE2EExpr m) (liftE2EExpr i)
  | _, _, .tset m i v => .tset (liftE2EExpr m) (liftE2EExpr i) (liftE2EExpr v)

@[simp] theorem liftE2EExpr_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) →
    (liftE2EExpr (Pt := Pt) e).cost = e.cost := by
  intro Γ t e
  induction e <;> simp_all [liftE2EExpr, Expr.cost]

@[simp] theorem liftE2EExpr_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) →
    (liftE2EExpr (Pt := Pt) e).size = e.size := by
  intro Γ t e
  induction e <;> simp_all [liftE2EExpr, Expr.size, liftE2EOp_opSize]

private theorem list_find_map {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) : ∀ xs : List α, (xs.map g).find? q = (xs.find? p).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hpq x]
    cases p x
    · exact list_find_map g q p hpq xs
    · rfl

private theorem list_any_map_eq {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) : ∀ xs : List α, (xs.map g).any q = xs.any p
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.any_cons, hpq x, list_any_map_eq g q p hpq xs]

private theorem list_map_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ) (f : α → γ) (hfg : ∀ x, f' (g x) = h (f x)) :
    ∀ xs : List α, (xs.map g).map f' = (xs.map f).map h
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, hfg x, list_map_map_eq g h f' f hfg xs]

private theorem list_foldr_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ → δ) (f : α → γ → γ) (hf : ∀ x acc, f' (g x) (h acc) = h (f x acc)) (z : γ) :
    ∀ xs : List α, (xs.map g).foldr f' (h z) = h (xs.foldr f z)
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.foldr_cons, list_foldr_map_eq g h f' f hf z xs, hf x]

private theorem e2eParseOptPreKeyId_eq :
    ReductionDsl.e2eParseOptPreKeyId = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseOptPreKeyId := by
  funext xs; cases xs with
  | nil => rfl
  | cons b rest =>
    dsimp only [ReductionDsl.e2eParseOptPreKeyId, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseOptPreKeyId]
    rw [readProstVarint_eq]

private theorem e2eParseUint32Field_eq :
    ReductionDsl.e2eParseUint32Field = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseUint32Field := by
  funext kb xs; cases xs with
  | nil => rfl
  | cons k rest =>
    dsimp only [ReductionDsl.e2eParseUint32Field, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseUint32Field]
    rw [readProstVarint_eq]

private theorem e2eParseDjbKeyField_eq :
    ReductionDsl.e2eParseDjbKeyField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseDjbKeyField := rfl

private theorem e2eParseInnerMsgField_eq :
    ReductionDsl.e2eParseInnerMsgField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField := by
  funext xs; cases xs with
  | nil => rfl
  | cons b rest =>
    by_cases h : b = 0x22#8
    · subst h; simp [ReductionDsl.e2eParseInnerMsgField,
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField, readProstVarint_eq]
    · simp [ReductionDsl.e2eParseInnerMsgField,
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseInnerMsgField, h]

private theorem e2eParseKyberCtField_eq :
    ReductionDsl.e2eParseKyberCtField = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eParseKyberCtField := rfl

private theorem e2eDecodePreKeyRaw_eq :
    ReductionDsl.e2eDecodePreKeyRaw = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyRaw := by
  funext c; rcases c with _ | ⟨t, _ | ⟨v, proto⟩⟩
  · rfl
  · rfl
  · dsimp only [ReductionDsl.e2eDecodePreKeyRaw, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eDecodePreKeyRaw]
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

private theorem spqrParamsToV_eq {ℓ : ℕ} {Pt : Type} (p : CryptoVerification.LibsignalSpqrV1.ChainParamsPB) :
    ReductionDsl.spqrParamsToV (ℓ := ℓ) (Pt := Pt) p =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsToV (ℓ := ℓ) p := rfl

private theorem spqrVnToV_eq {ℓ : ℕ} {Pt : Type} (vn : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB) :
    ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) vn =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnToV (ℓ := ℓ) vn := rfl

private theorem spqrVnOfV_eq {ℓ : ℕ} {Pt : Type}
    (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) v =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV (ℓ := ℓ) v := rfl

private theorem spqrDirToV_eq {ℓ : ℕ} {Pt : Type} (d : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB) :
    ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) d =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV (ℓ := ℓ) d := by
  dsimp only [ReductionDsl.spqrDirToV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV]
  rw [splitSpqrPrev_eq]

private theorem spqrChainToV_eq {ℓ : ℕ} {Pt : Type} (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) c =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV (ℓ := ℓ) c := by
  dsimp only [ReductionDsl.spqrChainToV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV]
  have hd : ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrDirToV (ℓ := ℓ) := funext spqrDirToV_eq
  have hp : ReductionDsl.spqrParamsToV (ℓ := ℓ) (Pt := Pt) =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrParamsToV (ℓ := ℓ) := funext spqrParamsToV_eq
  rw [hd, hp]

private theorem spqrChainOfV_eq {ℓ : ℕ} {Pt : Type}
    (v : (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainT (ℓ := ℓ)).denote) :
    ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) v =
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV (ℓ := ℓ) v := rfl

private theorem e2eRecordExtras_eq :
    ReductionDsl.e2eRecordExtras = Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eRecordExtras := by
  funext regIdA regIdB bobRemoteRegId hdr p; cases p <;> rfl

private theorem partyToBool_eq :
    @ReductionDsl.partyToBool = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.partyToBool := by
  funext p; cases p <;> rfl

private theorem boolToParty_eq :
    @ReductionDsl.boolToParty = @Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.boolToParty := by
  funext b; cases b <;> rfl

private theorem heq_app_of_heq_fn {A' A B' B : Type} {f' : A' → B'} {f : A → B}
    (hA : A' = A) (hB : B' = B) (hf : HEq f' f) {x' : A'} {x : A} (hx : HEq x' x) :
    HEq (f' x') (f x) := by
  subst hA; subst hB; cases hf; cases hx; rfl

set_option maxHeartbeats 800000 in
private theorem liftPureOp_eval_fn_heq {ℓ : ℕ} {Pt : Type} (o : E2EPureOp) :
    HEq (AtomicPureOp.eval ℓ Pt (liftPureOp o))
        (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval ℓ o) := by
  cases o
  case parsePreKeyWire =>
    apply heq_of_eq; funext x
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.hdrV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrV]
    rw [e2eDecodePreKeyMsg_eq, e2eHdrOfPreKeyMsg_eq]
  case partneredInnerBytes =>
    apply heq_of_eq; funext ⟨bobAcc, regIdA, hdr, c⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2ePartneredInnerBytes_eq]
  case wireInnerBytes =>
    apply heq_of_eq; funext x
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    rw [e2eWireInnerBytes_eq]
  case wrapPreKeyWire =>
    apply heq_of_eq; funext ⟨regIdA, hdr, inner⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2eExpectedPreKeyMsg_eq]
  case spqrStateSplit =>
    apply heq_of_eq; funext x
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.spqrSplitEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrSplitEval]
    have hvn : ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) =
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnToV (ℓ := ℓ) := funext spqrVnToV_eq
    have hch : ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) =
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainToV (ℓ := ℓ) := funext spqrChainToV_eq
    rw [hvn, hch]
    cases CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState x <;> rfl
  case spqrStateJoin =>
    apply heq_of_eq; funext ⟨v1?, vn?, ch?⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.spqrJoinEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrJoinEval]
    have hvn : ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) =
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV (ℓ := ℓ) := funext spqrVnOfV_eq
    have hch : ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) =
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV (ℓ := ℓ) := funext spqrChainOfV_eq
    rw [hvn, hch]
    cases v1? <;> rfl
  case checkShortCiphertext =>
    apply heq_of_eq; funext ⟨c, inner?⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    cases inner? <;> rfl
  case splitWhisperWire =>
    apply heq_of_eq; funext x
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    cases x <;> rfl
  case ghostStateSplit =>
    apply heq_of_eq; funext x
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.ghostSplitEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostSplitEval]
    rw [partyToBool_eq]
  case ghostStateJoin =>
    apply heq_of_eq; funext ⟨isB, ver, locId, remId?, rk, prevCtr, pend, ep, cEps, sc?, rcs, pqSt⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.ghostJoinEval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostJoinEval]
    rw [boolToParty_eq]
  case encodeSessionRecord =>
    apply heq_of_eq; funext ⟨⟨regIdA, regIdB, bobRemoteRegId, hdrV0⟩, g⟩
    dsimp only [liftPureOp, AtomicPureOp.eval, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval,
      ReductionDsl.e2eEncodeSessionRecord, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eEncodeSessionRecord,
      ReductionDsl.hdrOfV, Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.hdrOfV]
    rw [e2eRecordExtras_eq]
  all_goals
    apply heq_of_eq
    dsimp only [liftPureOp, AtomicPureOp.eval,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp.eval]
    rfl

private theorem liftCurveCheckOp_eval_fn_heq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} (cc : E2ECurveCheckOp) :
    HEq ((ReductionDsl.atomicCurveCheckOps ℓ decT encT).eval (liftCurveCheckOp cc))
        ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).eval cc) := by
  cases cc <;> rfl

set_option maxHeartbeats 400000 in
private theorem liftCryptoOp_eval_fn_heq {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (c : E2ECryptoOp) :
    HEq ((atomicE2EOps ℓ P C K decT encT).eval (liftE2EOp (Pt := Pt) (.inr (.inr c))))
        (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval ℓ P C K c) := by
  cases c
  case spqrChainFromVn =>
    dsimp only [atomicE2EOps, Ops.sum, liftE2EOp, ReductionDsl.atomicSpqrKemOps]
    apply heq_of_eq; funext vn
    dsimp only [AtomicSpqrKemOp.eval,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval,
      ReductionDsl.spqrChainFromVnEval,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainFromVnEval]
    rw [spqrVnOfV_eq]
    cases CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrVnOfV (ℓ := ℓ) vn) with
    | error _ => rfl
    | ok c0 =>
      dsimp only
      exact congrArg some (spqrChainToV_eq c0.intoPb)
  case spqrChainAddEpoch =>
    dsimp only [atomicE2EOps, Ops.sum, liftE2EOp, ReductionDsl.atomicSpqrKemOps]
    apply heq_of_eq; funext ⟨ch, ep, sec⟩
    dsimp only [AtomicSpqrKemOp.eval,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.eval,
      ReductionDsl.spqrChainAddEpochEval,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainAddEpochEval]
    rw [spqrChainOfV_eq]
    cases CryptoVerification.LibsignalSpqrV1.Chain.fromPb
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.spqrChainOfV (ℓ := ℓ) ch) with
    | error _ => rfl
    | ok c0 =>
      dsimp only
      cases c0.addEpoch
          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
          ⟨ep, CryptoGames.HMAC.keyToBytes32 sec⟩ with
      | error _ => rfl
      | ok c1 =>
        dsimp only
        exact congrArg (Prod.mk false) (congrArg some (spqrChainToV_eq c1.intoPb))
  all_goals rfl

private theorem liftE2EOp_eval_heq {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op)
    (x' : ((atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o)).denote)
    (x : ((e2eOps ℓ P C K decT encT).dom o).denote)
    (hx : HEq x' x) :
    HEq ((atomicE2EOps ℓ P C K decT encT).eval (liftE2EOp (Pt := Pt) o) x')
        ((e2eOps ℓ P C K decT encT).eval o x) := by
  refine heq_app_of_heq_fn
    (by rw [liftE2EOp_dom, liftTy_denote_eq])
    (by rw [liftE2EOp_cod, liftTy_denote_eq])
    ?_ hx
  rcases o with o | cc | c
  · exact liftPureOp_eval_fn_heq o
  · exact liftCurveCheckOp_eval_fn_heq cc
  · exact liftCryptoOp_eval_fn_heq c

set_option maxHeartbeats 400000 in
theorem liftE2EExpr_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) → (ρ : Env Γ) →
    (liftE2EExpr (Pt := Pt) e).eval (liftEnv (Pt := Pt) ρ) = liftVal (Pt := Pt) (e.eval ρ) := by
  intro Γ t e
  induction e with
  | var v => intro ρ; exact liftEnv_get ρ v
  | unit | bool _ | nat _ | none | nil => intro _; rfl
  | add a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | sub a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | mulK _ a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | divK _ a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | modK _ a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | lt a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | eqN a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | not a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | and a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | ite c a b ihc iha ihb =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihc ρ]
    cases c.eval ρ
    · exact ihb ρ
    · exact iha ρ
  | pair a b iha ihb => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | fst a iha =>
    intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rcases a.eval ρ with ⟨_, _⟩; rfl
  | snd a iha =>
    intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rcases a.eval ρ with ⟨_, _⟩; rfl
  | inl a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | inr a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | some a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | caseOpt e n s ihe ihn ihs =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihe ρ]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihe ρ]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    intro ρ
    dsimp only [liftE2EExpr]
    apply eq_of_heq
    have h1 := castExprTy_eval_heq (liftE2EOp_cod (Pt := Pt) o)
      (.op (liftE2EOp (Pt := Pt) o)
        (castExprTy (liftE2EOp_dom (Pt := Pt) o).symm (liftE2EExpr (Pt := Pt) a)))
      (liftEnv (Pt := Pt) ρ)
    have hdom := (castExprTy_eval_heq (liftE2EOp_dom (Pt := Pt) o).symm
      (liftE2EExpr (Pt := Pt) a) (liftEnv (Pt := Pt) ρ)).trans
      ((heq_of_eq (iha ρ)).trans (liftVal_heq (Pt := Pt) (a.eval ρ)))
    have h2 := liftE2EOp_eval_heq (Pt := Pt) o _ (a.eval ρ) hdom
    exact (h1.trans h2).trans (liftVal_heq (Pt := Pt) ((e2eOps ℓ P C K decT encT).eval o (a.eval ρ))).symm
  | cons x l ihx ihl => intro ρ; simp only [liftE2EExpr, Expr.eval, ihx ρ, ihl ρ]; rfl
  | len l ihl => intro ρ; simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, List.length_map]
  | take n l ihn ihl =>
    intro ρ; simp only [liftE2EExpr, Expr.eval, ihn ρ, ihl ρ, liftVal, List.map_take]
  | appendL Kb a b iha ihb =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ, liftVal, ← List.map_append, List.map_take]
  | findB Kb l p ihl ihp =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_find_map liftVal (fun y => (liftE2EExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | anyB Kb l p ihl ihp =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_any_map_eq liftVal (fun y => (liftE2EExpr p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ)) (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | mapB Kb l f ihl ihf =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_map_map_eq liftVal liftVal (fun y => (liftE2EExpr f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ)) (fun x => ihf (.cons x ρ)) ((l.eval ρ).take Kb)
  | foldrB Kb l z f ihl ihz ihf =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihl ρ, ihz ρ]
    change (((l.eval ρ).map liftVal).take Kb).foldr _ (liftVal (z.eval ρ)) = _
    rw [← List.map_take]
    exact list_foldr_map_eq liftVal liftVal
      (fun y acc => (liftE2EExpr f).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      (z.eval ρ) ((l.eval ρ).take Kb)
  | tconst a iha => intro ρ; simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | tget m i ihm ihi => intro ρ; simp only [liftE2EExpr, Expr.eval, ihm ρ, ihi ρ]; rfl
  | tset m i a ihm ihi iha =>
    intro ρ
    simp only [liftE2EExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ]
    funext j
    by_cases hj : j = i.eval ρ <;> simp [hj, liftVal]

@[expose] def emptyTargetE2EIface (ℓ : ℕ) : Iface (e2eSig ℓ) unifSpec where
  fwdU n := query (spec := unifSpec) n
  uCost := 8
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc g := g.elim
  dec g := g.elim
  qCost := Empty.elim
  smp := e2eSamplers ℓ

@[expose] def stepACoinSamplers (ℓ : ℕ) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    E2ECoinSamplers ℓ P C K decT encT (stepAIface ℓ (emptyTargetE2EIface ℓ)) :=
  e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ)

@[expose] def liftSampleComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} :
    (I : Iface (atomicSig ℓ Pt) T) →
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) →
    {Γ : List (Ty (atomicSig ℓ Pt))} →
    (s : UniformSamplerTag E2EUnifBase) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .unit →
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (liftTy (Pt := Pt) ((e2eSamplers ℓ).sTy s))
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .bool, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicBaseSamplers ℓ Pt⟩) .bool a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .index N, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicBaseSamplers ℓ Pt⟩) (.index N) a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .base .bv256, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicBaseSamplers ℓ Pt⟩)
      (.base .bv256) a
  | ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, _⟩, rfl, _, .base .bv512, a =>
    .sample (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicBaseSamplers ℓ Pt⟩)
      (.base .bv512) a

private theorem liftSampleComp_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag E2EUnifBase)
    (a : Expr (atomicE2EOps ℓ P C K decT encT) Γ .unit) (w : I.Tag → ℕ) :
    (liftSampleComp I hsmp s a).queries w (fun _ => 0) = 0 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

private theorem liftSampleComp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag E2EUnifBase)
    (a : Expr (atomicE2EOps ℓ P C K decT encT) Γ .unit) :
    (liftSampleComp I hsmp s a).cost = a.cost + (e2eSamplers ℓ).sCost s := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

private theorem liftSampleComp_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) {Γ : List (Ty (atomicSig ℓ Pt))}
    (s : UniformSamplerTag E2EUnifBase)
    (a : Expr (atomicE2EOps ℓ P C K decT encT) Γ .unit) :
    (liftSampleComp I hsmp s a).size = a.size + 1 := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

/-- Lift a coin-only `e2eOps` computation into any `atomicSig ℓ Pt` interface with `atomicBaseSamplers`. -/
@[expose] def liftE2ECoinComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t →
    Comp (atomicE2EOps ℓ P C K decT encT) I (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .ret e => .ret (liftE2EExpr e)
  | _, _, .bind c k => .bind (liftE2ECoinComp I hsmp c) (liftE2ECoinComp I hsmp k)
  | _, _, .ite b t f => .ite (liftE2EExpr b) (liftE2ECoinComp I hsmp t) (liftE2ECoinComp I hsmp f)
  | _, _, .caseOpt e n s =>
    .caseOpt (liftE2EExpr e) (liftE2ECoinComp I hsmp n) (liftE2ECoinComp I hsmp s)
  | _, _, .caseSum e l r =>
    .caseSum (liftE2EExpr e) (liftE2ECoinComp I hsmp l) (liftE2ECoinComp I hsmp r)
  | _, _, .query q _ => Empty.elim q
  | _, _, .sample s a => liftSampleComp I hsmp s (liftE2EExpr a)
  | _, _, .iter K init step =>
    .iter K (liftE2EExpr init) (liftE2ECoinComp I hsmp step)
  | _, _, .findM K xs p => .findM K (liftE2EExpr xs) (liftE2ECoinComp I hsmp p)
  | _, _, .anyM K xs p => .anyM K (liftE2EExpr xs) (liftE2ECoinComp I hsmp p)
  | _, _, .mapM K xs f => .mapM K (liftE2EExpr xs) (liftE2ECoinComp I hsmp f)
  | _, _, .consumeFirstM K xs p mk =>
    .consumeFirstM K (liftE2EExpr xs) (liftE2ECoinComp I hsmp p) (liftE2EExpr mk)
  | _, _, .foldM K xs init step =>
    .foldM K (liftE2EExpr xs) (liftE2EExpr init) (liftE2ECoinComp I hsmp step)

@[simp] theorem liftE2ECoinComp_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (w : I.Tag → ℕ) :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t) →
    (liftE2ECoinComp (Pt := Pt) I hsmp c).queries w (fun _ => 0) = 0 := by
  intro Γ t c
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [liftE2ECoinComp, Comp.queries, ih1, ih2]
  | query q _ => exact Empty.elim q
  | sample s a => exact liftSampleComp_queries_zero I hsmp s (liftE2EExpr a) w
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [liftE2ECoinComp, Comp.queries, ih]

@[simp] theorem liftE2ECoinComp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t) →
    (liftE2ECoinComp (Pt := Pt) I hsmp c).cost = c.cost := by
  intro Γ t c
  induction c with
  | query q _ => exact Empty.elim q
  | sample s a =>
    dsimp only [liftE2ECoinComp, Comp.cost, stepAIface]
    rw [liftSampleComp_cost I hsmp s (liftE2EExpr a), liftE2EExpr_cost]
  | _ => simp_all [liftE2ECoinComp, Comp.cost]

@[simp] theorem liftE2ECoinComp_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t) →
    (liftE2ECoinComp (Pt := Pt) I hsmp c).size = c.size := by
  intro Γ t c
  induction c with
  | query q _ => exact Empty.elim q
  | sample s a =>
    dsimp only [liftE2ECoinComp, Comp.size]
    rw [liftSampleComp_size I hsmp s (liftE2EExpr a), liftE2EExpr_size]
  | _ => simp_all [liftE2ECoinComp, Comp.size]

private theorem stepAIface_emptyTarget_liftP_eq {ℓ : ℕ} {α : Type} (p : ProbComp α) :
    (stepAIface ℓ (emptyTargetE2EIface ℓ)).liftP p = p := by
  unfold Iface.liftP stepAIface emptyTargetE2EIface
  exact simulateQ_id' p

private theorem iterM_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β : Type} (g : α → β) (f' : β → OracleComp T β) (f : α → ProbComp α)
    (hf : ∀ a, f' (g a) = I.liftP (g <$> f a)) :
    ∀ (n : ℕ) (a : α), iterM f' n (g a) = I.liftP (g <$> iterM f n a)
  | 0, a => by unfold iterM Iface.liftP; simp
  | n + 1, a => by
    simp only [iterM, hf a, Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun a' => ?_
    have ih := iterM_liftP_eq I g f' f hf n a'
    simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure] at ih
    exact ih

private theorem findML_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β : Type} (g : α → β) (q : β → OracleComp T Bool) (p : α → ProbComp Bool)
    (hpq : ∀ x, q (g x) = I.liftP (p x)) :
    ∀ xs : List α, findML q (xs.map g) = I.liftP (Option.map g <$> findML p xs)
  | [] => by unfold findML Iface.liftP; simp
  | x :: xs => by
    simp only [List.map_cons, findML, hpq x, Iface.liftP, map_eq_bind_pure_comp,
      Function.comp_def, simulateQ_bind, bind_assoc]
    refine bind_congr fun b => ?_
    cases b
    · have ih := findML_liftP_eq I g q p hpq xs
      simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def] at ih
      simpa using ih
    · simp

private theorem anyML_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β : Type} (g : α → β) (q : β → OracleComp T Bool) (p : α → ProbComp Bool)
    (hpq : ∀ x, q (g x) = I.liftP (p x)) :
    ∀ xs : List α, anyML q (xs.map g) = I.liftP (anyML p xs)
  | [] => by unfold anyML Iface.liftP; simp
  | x :: xs => by
    simp only [List.map_cons, anyML, hpq x, Iface.liftP, simulateQ_bind]
    refine bind_congr fun b => ?_
    cases b
    · have ih := anyML_liftP_eq I g q p hpq xs
      dsimp only [Iface.liftP] at ih
      simpa using ih
    · simp

private theorem mapML_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β γ δ : Type} (g : α → β) (h : γ → δ) (f' : β → OracleComp T δ) (f : α → ProbComp γ)
    (hf : ∀ x, f' (g x) = I.liftP (h <$> f x)) :
    ∀ xs : List α, mapML f' (xs.map g) = I.liftP (List.map h <$> mapML f xs)
  | [] => by unfold mapML Iface.liftP; simp
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, Iface.liftP, map_eq_bind_pure_comp,
      Function.comp_def, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun y => ?_
    have ih := mapML_liftP_eq I g h f' f hf xs
    simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure] at ih
    rw [ih, bind_assoc]
    simp

private theorem consumeFirstML_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S₀ T) {α β : Type} (g : α → β)
    (q : β → OracleComp T Bool) (p : α → ProbComp Bool) (mk' : β → β) (mk : α → α)
    (hpq : ∀ x, q (g x) = I.liftP (p x)) (hmk : ∀ x, mk' (g x) = g (mk x)) :
    ∀ xs : List α, consumeFirstML q mk' (xs.map g) =
      I.liftP ((fun r => (r.1, r.2.map g)) <$> consumeFirstML p mk xs)
  | [] => by unfold consumeFirstML Iface.liftP; simp
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hpq x, Iface.liftP, map_eq_bind_pure_comp,
      Function.comp_def, simulateQ_bind, bind_assoc]
    refine bind_congr fun b => ?_
    cases b
    · have ih := consumeFirstML_liftP_eq I g q p mk' mk hpq hmk xs
      simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
        simulateQ_bind, simulateQ_pure] at ih
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp
    · rw [hmk x]; simp

private theorem foldML_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ → OracleComp T δ) (f : α → γ → ProbComp γ)
    (hf : ∀ x acc, f' (g x) (h acc) = I.liftP (h <$> f x acc)) :
    ∀ (xs : List α) (z : γ), foldML f' (h z) (xs.map g) = I.liftP (h <$> foldML f z xs)
  | [], z => by unfold foldML Iface.liftP; simp
  | x :: xs, z => by
    simp only [List.map_cons, foldML, hf x z, Iface.liftP, map_eq_bind_pure_comp,
      Function.comp_def, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun z' => ?_
    have ih := foldML_liftP_eq I g h f' f hf xs z'
    simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure] at ih
    exact ih

private theorem liftSampleComp_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) {Γ : List (Ty (e2eSig ℓ))}
    (s : UniformSamplerTag E2EUnifBase)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ .unit) (ρ : Env Γ) :
    (liftSampleComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I hsmp s (liftE2EExpr a)).eval (liftEnv (Pt := Pt) ρ) =
      I.liftP (liftVal (Pt := Pt) <$>
        (Comp.sample (I := stepAIface ℓ (emptyTargetE2EIface ℓ)) s a).eval ρ) := by
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rw [Comp.eval, stepAIface_emptyTarget_liftP_eq]
  rcases s with _ | N | (_ | _) <;>
    exact congrArg
      (Iface.liftP ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, atomicBaseSamplers ℓ Pt⟩)
      (id_map _).symm

set_option maxHeartbeats 400000 in
theorem liftE2ECoinComp_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t) →
    (ρ : Env Γ) →
    (liftE2ECoinComp (Pt := Pt) I hsmp c).eval (liftEnv (Pt := Pt) ρ) =
      I.liftP (liftVal (Pt := Pt) <$> c.eval ρ) := by
  intro Γ t c
  induction c with
  | ret e =>
    intro ρ
    dsimp only [liftE2ECoinComp, Comp.eval]
    rw [liftE2EExpr_eval e ρ]
    unfold Iface.liftP; simp
  | bind c k ihc ihk =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, ihc ρ, Iface.liftP, map_eq_bind_pure_comp,
      Function.comp_def, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun x => ?_
    have ihx : (liftE2ECoinComp I hsmp k).eval (.cons (liftVal x) (liftEnv ρ)) =
        I.liftP (liftVal <$> k.eval (.cons x ρ)) := ihk (.cons x ρ)
    simp only [Iface.liftP, map_eq_bind_pure_comp, Function.comp_def,
      simulateQ_bind, simulateQ_pure] at ihx
    exact ihx
  | ite b t f iht ihf =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval b ρ]
    cases b.eval ρ
    · exact ihf ρ
    · exact iht ρ
  | caseOpt e n s ihn ihs =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval e ρ]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval e ρ]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | query q _ => exact Empty.elim q
  | sample s a => intro ρ; exact liftSampleComp_eval I hsmp s a ρ
  | iter K init step ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval init ρ]
    exact iterM_liftP_eq I liftVal
      (fun y => (liftE2ECoinComp I hsmp step).eval (.cons y (liftEnv ρ)))
      (fun x => step.eval (.cons x ρ))
      (fun x => ih (.cons x ρ))
      K (init.eval ρ)
  | findM K xs p ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval xs ρ, liftVal, ← List.map_take]
    exact findML_liftP_eq I liftVal
      (fun y => (liftE2ECoinComp I hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ih (.cons x ρ)).trans (congrArg I.liftP (id_map _)))
      ((xs.eval ρ).take K)
  | anyM K xs p ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval xs ρ, liftVal, ← List.map_take]
    exact (anyML_liftP_eq I liftVal
      (fun y => (liftE2ECoinComp I hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => (ih (.cons x ρ)).trans (congrArg I.liftP (id_map _)))
      ((xs.eval ρ).take K)).trans (congrArg I.liftP (id_map _).symm)
  | mapM K xs f ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval xs ρ, liftVal, ← List.map_take]
    exact mapML_liftP_eq I liftVal liftVal
      (fun y => (liftE2ECoinComp I hsmp f).eval (.cons y (liftEnv ρ)))
      (fun x => f.eval (.cons x ρ))
      (fun x => ih (.cons x ρ))
      ((xs.eval ρ).take K)
  | consumeFirstM K xs p mk ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval xs ρ, liftVal, ← List.map_take]
    exact consumeFirstML_liftP_eq I liftVal
      (fun y => (liftE2ECoinComp I hsmp p).eval (.cons y (liftEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun y => (liftE2EExpr mk).eval (.cons y (liftEnv ρ)))
      (fun x => mk.eval (.cons x ρ))
      (fun x => (ih (.cons x ρ)).trans (congrArg I.liftP (id_map _)))
      (fun x => liftE2EExpr_eval mk (.cons x ρ))
      ((xs.eval ρ).take K)
  | foldM K xs init step ih =>
    intro ρ
    simp only [liftE2ECoinComp, Comp.eval, liftE2EExpr_eval xs ρ, liftE2EExpr_eval init ρ]
    change foldML _ (liftVal (init.eval ρ)) (((xs.eval ρ).map liftVal).take K) = _
    rw [← List.map_take]
    exact foldML_liftP_eq I liftVal liftVal
      (fun y acc => (liftE2ECoinComp I hsmp step).eval (.cons y (.cons acc (liftEnv ρ))))
      (fun x acc => step.eval (.cons x (.cons acc ρ)))
      (fun x acc => ih (.cons x (.cons acc ρ)))
      ((xs.eval ρ).take K) (init.eval ρ)

theorem liftE2ECoinComp_eval_prob {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt)
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) Γ t)
    (ρ : Env Γ) (m : ProbComp t.denote)
    (hc : c.eval ρ = (stepAIface ℓ (emptyTargetE2EIface ℓ)).liftP m) :
    (liftE2ECoinComp (Pt := Pt) I hsmp c).eval (liftEnv (Pt := Pt) ρ) =
      I.liftP (liftVal (Pt := Pt) <$> m) := by
  rw [liftE2ECoinComp_eval I hsmp c ρ, hc, stepAIface_emptyTarget_liftP_eq]

/-! ## Bounded list combinators -/

@[expose] def atomicListGetOptE {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) : Expr O Γ (.opt t) :=
  .letE (.pair lE iE) (.letE (.len (.fst .v0)) (.snd
    (.foldrB K (.fst .v1) (.pair (.nat 0) .none)
      (.pair (.add (.fst .v1) (.nat 1))
        (.ite (.eqN (.add (.add (.fst .v1) (.nat 1)) (.snd .v3)) .v2) (.some .v0) (.snd .v1))))))

@[expose] def atomicListSetE {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (xE : Expr O Γ t) : Expr O Γ (.list t) :=
  .letE (.pair lE (.pair iE xE)) (.letE (.len (.fst .v0)) (.snd
    (.foldrB K (.fst .v1) (.pair (.nat 0) .nil)
      (.pair (.add (.fst .v1) (.nat 1))
        (.cons (.ite (.eqN (.add (.add (.fst .v1) (.nat 1)) (.fst (.snd .v3))) .v2)
          (.snd (.snd .v3)) .v0) (.snd .v1))))))

private def foldGetStep {α : Type} (L i : ℕ) (x : α) (acc : ℕ × Option α) : ℕ × Option α :=
  (acc.1 + 1, if decide (acc.1 + 1 + i = L) = true then some x else acc.2)

private theorem foldGetStep_fst {α : Type} (L i : ℕ) :
    ∀ (xs : List α), (xs.foldr (foldGetStep L i) (0, none)).1 = xs.length
  | [] => rfl | _ :: xs => by simp [foldGetStep, foldGetStep_fst L i xs]

private theorem foldGetStep_snd {α : Type} (L i : ℕ) :
    ∀ (xs : List α) (off : ℕ), off + xs.length = L →
      (xs.foldr (foldGetStep L i) (0, none)).2 = if off ≤ i then xs[i - off]? else none
  | [], _, _ => by split_ifs <;> rfl
  | x :: xs, off, hL => by
    simp only [List.length_cons] at hL
    simp only [List.foldr_cons, foldGetStep, foldGetStep_fst L i xs,
      foldGetStep_snd L i xs (off + 1) (by omega)]
    by_cases hi : i = off
    · subst hi; have hcond : xs.length + 1 + i = L := (by omega); simp [hcond]
    · have hcond : ¬(xs.length + 1 + i = L) := by omega
      simp only [decide_eq_false hcond, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : off ≤ i
      · have hle' : off + 1 ≤ i := by omega
        have hsub : i - off = (i - (off + 1)) + 1 := (by omega); simp [hle, hle', hsub]
      · have hle' : ¬(off + 1 ≤ i) := (by omega); simp [hle, hle']

private theorem env_get_zero' {S₀ : Sig} {Γ : List (Ty S₀)} {τ : Ty S₀}
    (x : τ.denote) (ρ : Env Γ) : Env.get (.cons x ρ) .zero = x := rfl

private theorem env_get_succ' {S₀ : Sig} {Γ : List (Ty S₀)} {σ τ : Ty S₀}
    (x : σ.denote) (ρ : Env Γ) (i : Var Γ τ) : Env.get (.cons x ρ) (.succ i) = Env.get ρ i := rfl

theorem atomicListGetOptE_eval {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (ρ : Env Γ)
    (hlen : (lE.eval ρ).length ≤ K) :
    (atomicListGetOptE K lE iE).eval ρ = (lE.eval ρ)[iE.eval ρ]? := by
  have htake : (lE.eval ρ).take K = lE.eval ρ := List.take_of_length_le hlen
  dsimp only [atomicListGetOptE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval,
    env_get_zero', env_get_succ']; rw [htake]
  exact foldGetStep_snd (lE.eval ρ).length (iE.eval ρ) (lE.eval ρ) 0 (Nat.zero_add _)

private def foldSetStep {α : Type} (L i : ℕ) (val : α) (x : α) (acc : ℕ × List α) : ℕ × List α :=
  (acc.1 + 1, (if decide (acc.1 + 1 + i = L) = true then val else x) :: acc.2)

private theorem foldSetStep_fst {α : Type} (L i : ℕ) (val : α) :
    ∀ (xs : List α), (xs.foldr (foldSetStep L i val) (0, [])).1 = xs.length
  | [] => rfl | _ :: xs => by simp [foldSetStep, foldSetStep_fst L i val xs]

private theorem foldSetStep_snd {α : Type} (L i : ℕ) (val : α) :
    ∀ (xs : List α) (off : ℕ), off + xs.length = L →
      (xs.foldr (foldSetStep L i val) (0, [])).2 = if off ≤ i then xs.set (i - off) val else xs
  | [], _, _ => by split_ifs <;> rfl
  | x :: xs, off, hL => by
    simp only [List.length_cons] at hL
    simp only [List.foldr_cons, foldSetStep, foldSetStep_fst L i val xs,
      foldSetStep_snd L i val xs (off + 1) (by omega)]
    by_cases hi : i = off
    · subst hi; have hcond : xs.length + 1 + i = L := by omega
      have hnle : ¬(i + 1 ≤ i) := (by omega); simp [hcond, hnle]
    · have hcond : ¬(xs.length + 1 + i = L) := by omega
      simp only [decide_eq_false hcond, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : off ≤ i
      · have hle' : off + 1 ≤ i := by omega
        have hsub : i - off = (i - (off + 1)) + 1 := (by omega); simp [hle, hle', hsub]
      · have hle' : ¬(off + 1 ≤ i) := (by omega); simp [hle, hle']

theorem atomicListSetE_eval {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (xE : Expr O Γ t) (ρ : Env Γ)
    (hlen : (lE.eval ρ).length ≤ K) :
    (atomicListSetE K lE iE xE).eval ρ = (lE.eval ρ).set (iE.eval ρ) (xE.eval ρ) := by
  have htake : (lE.eval ρ).take K = lE.eval ρ := List.take_of_length_le hlen
  dsimp only [atomicListSetE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval,
    env_get_zero', env_get_succ']; rw [htake]
  exact foldSetStep_snd (lE.eval ρ).length (iE.eval ρ) (xE.eval ρ) (lE.eval ρ) 0 (Nat.zero_add _)

theorem atomicListGetOptE_cost {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) :
    (atomicListGetOptE K lE iE).cost ≤ lE.cost + iE.cost + 18 * K + 15 := by
  dsimp only [atomicListGetOptE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.cost]
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl; rw [hb0, hb1]
  have hmul :
      K * (1 + 1 + 1 + 1 + (1 + 1 + 1 + 1 + (1 + 1) + 1 + 1 + 1 + max (1 + 1) (1 + 1) + 1) + 1 + 1) ≤
        K * 18 := Nat.mul_le_mul_left K (by decide)
  omega

theorem atomicListSetE_cost {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (xE : Expr O Γ t) :
    (atomicListSetE K lE iE xE).cost ≤ lE.cost + iE.cost + xE.cost + 23 * K + 15 := by
  dsimp only [atomicListSetE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.cost]
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl; rw [hb0, hb1]
  have hmul :
      K * (1 + 1 + 1 + 1 + (1 + 1 + 1 + 1 + (1 + 1 + 1) + 1 + 1 + 1 + max (1 + 1 + 1) 1 + 1 + (1 + 1) + 1) + 1 + 1) ≤
        K * 23 := Nat.mul_le_mul_left K (by decide)
  omega

theorem atomicListGetOptE_size {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) :
    (atomicListGetOptE K lE iE).size ≤ lE.size + iE.size + 40 + bits K := by
  dsimp only [atomicListGetOptE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.size]
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl; rw [hb0, hb1]; omega

theorem atomicListSetE_size {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (xE : Expr O Γ t) :
    (atomicListSetE K lE iE xE).size ≤ lE.size + iE.size + xE.size + 45 + bits K := by
  dsimp only [atomicListSetE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.size]
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl; rw [hb0, hb1]; omega

end Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter
