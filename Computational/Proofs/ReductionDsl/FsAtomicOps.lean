/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicMacros
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import Computational.Proofs.ReductionDsl.AtomicTablesHonest

/-!
# Atomic `ReductionDsl` Primitive Macros for FS-AEAD Reductions

First-order `Expr` and `Comp` macros over `atomicFsOps` and `atomicBaseSamplers` implementing
FS-AEAD public headers, chain PRG, clamped AEAD, equality checks, and uniform/ideal ciphertext
samplers, together with evaluation and `CoinSimEquiv` soundness lemmas.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl (Sig Ty Var Env Expr Comp Samplers Ops Iface GameCodec CostedReduction
  UniformSamplerTag OpsSizeHonest SampSizeHonest bits
  AtomicSort atomicSig AtomicBaseUnif atomicBaseSamplers
  AtomicPureOp atomicPureOps AtomicPtEncOp atomicPtEncOps AtomicSymOp atomicSymOps atomicFsOps
  PB B U8 U32 U64 BV128 BV256 PK IdKey PlainT PtT signalHdrT signalParsedT
  toLEBytes bytesToWordLE fitBytesN
  salt32V salt32OfV wireSignalHdrT wireSignalHdrV wireSignalHdrOfV
  lpubT lpubV lpubOfV wireSaltCtT wireSaltCtV wireSaltCtOfV
  lctT lctV lctOfV fig8HdrT fig8PubAdT fig8PubAdV fig8PubAdOfV
  slotAdT slotAdV slotAdOfV derivedMsgKeysT iterM)

namespace Computational.Proofs.ReductionDsl.FsAtomicOps

open OracleSpec OracleComp
open CryptoGames (Party AEADScheme MACScheme WireAEAD)
open CryptoGames.HMAC (keyToBytes32 hmacSha256Trunc8 hmacWith sha256With toBEBytes
  bytesToWord64LE hmacScheme)
open CryptoGames.HKDF (bytesToKey32 deriveMessageKeys DerivedMessageKeys)
open CryptoGames.CBC (Plain Block nBlocks blockToBytesLE cbcDecRaw cbcPkcs7EncryptOnly)
open CryptoGames.LibsignalAead (SerializedIdentityKeys addressCheckPasses libsignalReceiveWire
  libsignalWireAead wireEncode)
open CryptoGames.Ratchet (keyToBytesVec32 padOrTruncatePlain chainHmac messageKeySeed chainKeySeed
  hmacPRF)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lIds lHeader lWire lAeadK lAead lPubOf lChainPRG lAeadR lIdeal)
open CryptoGames.SM.Construction (Header)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey SignalHeader
  SignalMessage SignalMessageProtoCodec MessageKeyGenerator currentVersion
  macLength macIds serializeContent computeMac aesCbcEncrypt aesCbcDecrypt signalWireCodec
  maxForwardJumps rustLenBound)
open CryptoVerification.E2E (Bytes ofU8 toU8 u8Vec vecU8)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB atomicShortB_iff
  ValidCoinSim CoinSimEquiv bytesToKey32_keyToBytes32 keyToBytes32_bytesToKey32
  salt32OfV_salt32V salt32V_salt32OfV wireSignalHdrOfV_wireSignalHdrV
  wireSignalHdrV_wireSignalHdrOfV lpubOfV_lpubV lpubV_lpubOfV
  wireSaltCtOfV_wireSaltCtV wireSaltCtV_wireSaltCtOfV lctOfV_lctV lctV_lctOfV
  fig8PubAdOfV_fig8PubAdV fig8PubAdV_fig8PubAdOfV slotAdOfV_slotAdV slotAdV_slotAdOfV
  u8Vec_vecU8 fitBytesN_toList aesCbcEncrypt_length_eq atomicSymOps_aes256CbcEnc_lossless
  signalMsgNew_serialized_length_le atomicSymOps_signalMsgEncode_lossless
  atomicPureOps_signalMsgParse_lossless hmacWith_length computeMac_length
  sample_derivedMsgKeys_evalDistEq sample_u64_of_bv128_evalDistEq
  sample_bool_of_bv128_evalDistEq sample_blocks_iter_evalDistEq)

section OpInjections

variable (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey)

local notation "S" => atomicSig ℓ Pt
local notation "O" => atomicFsOps ℓ Pt C encT

def opPure {Γ : List (Ty S)} (o : AtomicPureOp)
    (e : Expr O Γ (o.dom ℓ Pt)) : Expr O Γ (o.cod ℓ Pt) :=
  @Expr.op S O Γ (Sum.inl o) e

def opPtEncPk {Γ : List (Ty S)} (e : Expr O Γ PtT) : Expr O Γ PK :=
  @Expr.op S O Γ (Sum.inr (Sum.inl AtomicPtEncOp.ptEncPk)) e

def opSym {Γ : List (Ty S)} (o : AtomicSymOp)
    (e : Expr O Γ (o.dom ℓ Pt)) : Expr O Γ (o.cod ℓ Pt) :=
  @Expr.op S O Γ (Sum.inr (Sum.inr o)) e

@[simp] theorem opPure_eval {Γ : List (Ty S)} (o : AtomicPureOp)
    (e : Expr O Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (opPure ℓ Pt C encT o e).eval ρ = o.eval ℓ Pt (e.eval ρ) := rfl

@[simp] theorem opPtEncPk_eval {Γ : List (Ty S)} (e : Expr O Γ PtT) (ρ : Env Γ) :
    (opPtEncPk ℓ Pt C encT e).eval ρ = encT (e.eval ρ) := rfl

@[simp] theorem opSym_eval {Γ : List (Ty S)} (o : AtomicSymOp)
    (e : Expr O Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (opSym ℓ Pt C encT o e).eval ρ = o.eval ℓ Pt C (e.eval ρ) := rfl

@[simp] theorem opPure_cost {Γ : List (Ty S)} (o : AtomicPureOp)
    (e : Expr O Γ (o.dom ℓ Pt)) :
    (opPure ℓ Pt C encT o e).cost = e.cost + o.cost ℓ := rfl

@[simp] theorem opPtEncPk_cost {Γ : List (Ty S)} (e : Expr O Γ PtT) :
    (opPtEncPk ℓ Pt C encT e).cost = e.cost + 4 := rfl

@[simp] theorem opSym_cost {Γ : List (Ty S)} (o : AtomicSymOp)
    (e : Expr O Γ (o.dom ℓ Pt)) :
    (opSym ℓ Pt C encT o e).cost = e.cost + o.cost ℓ := rfl

@[simp] theorem env_get_zero {Γ : List (Ty S)} {t : Ty S} (x : t.denote) (ρ : Env Γ) :
    (Env.cons x ρ).get Var.zero = x := rfl

@[simp] theorem env_get_succ {Γ : List (Ty S)} {t u : Ty S} (x : u.denote) (ρ : Env Γ)
    (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

private theorem vecU8_length32 (v : List.Vector (BitVec 8) 32) : (vecU8 v).length = 32 := by
  simp [vecU8, toU8, v.toList_length]

def pkLitExpr {Γ : List (Ty S)} (pk : PublicKey) : Expr O Γ PK :=
  opPure ℓ Pt C encT .pkOfPbytes
    (opPure ℓ Pt C encT (.pbytesLit 32 (vecU8 pk.bytes)) .unit)

@[simp] theorem pkLitExpr_eval {Γ : List (Ty S)} (pk : PublicKey) (ρ : Env Γ) :
    (pkLitExpr ℓ Pt C encT pk).eval ρ = pk := by
  rcases pk with ⟨v⟩
  simp [pkLitExpr, AtomicPureOp.eval, u8Vec_vecU8]

theorem pkLitExpr_cost {Γ : List (Ty S)} (pk : PublicKey) :
    (pkLitExpr ℓ Pt C encT (Γ := Γ) pk).cost = 98 := by
  simp [pkLitExpr, AtomicPureOp.cost, Expr.cost, vecU8_length32]

def idKeyLitExpr {Γ : List (Ty S)} (ik : IdentityKey) : Expr O Γ IdKey :=
  opPure ℓ Pt C encT .idKeyOfPbytes
    (opPure ℓ Pt C encT (.pbytesLit 32 (vecU8 ik.publicKey.bytes)) .unit)

@[simp] theorem idKeyLitExpr_eval {Γ : List (Ty S)} (ik : IdentityKey) (ρ : Env Γ) :
    (idKeyLitExpr ℓ Pt C encT ik).eval ρ = ik := by
  rcases ik with ⟨⟨v⟩⟩
  simp [idKeyLitExpr, AtomicPureOp.eval, u8Vec_vecU8]

theorem idKeyLitExpr_cost {Γ : List (Ty S)} (ik : IdentityKey) :
    (idKeyLitExpr ℓ Pt C encT (Γ := Γ) ik).cost = 98 := by
  simp [idKeyLitExpr, AtomicPureOp.cost, Expr.cost, vecU8_length32]

def optBytesEqExpr {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) : Expr O Γ .bool :=
  .caseOpt x
    (.caseOpt y (.bool true) (.bool false))
    (.caseOpt (Expr.renameM (Δ := B 32 :: Γ) (fun ⦃_⦄ v => Var.succ v) y) (.bool false)
      (opPure ℓ Pt C encT (.bytesEq 32 32) (.pair (.var (.succ .zero)) (.var .zero))))

theorem optBytesEqExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) (ρ : Env Γ) :
    (optBytesEqExpr ℓ Pt C encT x y).eval ρ = (x.eval ρ == y.eval ρ) := by
  have hr : ∀ (z : (B (ℓ := ℓ) (Pt := Pt) 32).denote),
      (Expr.renameM (Δ := B 32 :: Γ) (fun ⦃_⦄ v => Var.succ v) y).eval (.cons z ρ) = y.eval ρ :=
    fun z => Expr.renameM_eval (Δ := B 32 :: Γ) y (ρ₁ := ρ) (ρ₂ := .cons z ρ) (fun _ _ => rfl)
  dsimp only [optBytesEqExpr, Expr.eval]
  cases hx : x.eval ρ with
  | none => cases hy : y.eval ρ <;> simp
  | some a =>
    cases hy : y.eval ρ with
    | none => simp [hr, hy]
    | some b => simp [hr, hy, AtomicPureOp.eval, Expr.eval]

theorem optBytesEqExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) :
    (optBytesEqExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 70 := by
  simp only [optBytesEqExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, Expr.renameM_cost,
    PNat.val_ofNat]
  omega

def optPtEqExpr {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) : Expr O Γ .bool :=
  .caseOpt x
    (.caseOpt y (.bool true) (.bool false))
    (.caseOpt (Expr.renameM (Δ := PtT :: Γ) (fun ⦃_⦄ v => Var.succ v) y) (.bool false)
      (opPure ℓ Pt C encT .pkEq
        (.pair (opPtEncPk ℓ Pt C encT (.var (.succ .zero)))
               (opPtEncPk ℓ Pt C encT (.var .zero)))))

theorem optPtEqExpr_eval [DecidableEq Pt] (hinj : Function.Injective encT)
    {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) (ρ : Env Γ) :
    (optPtEqExpr ℓ Pt C encT x y).eval ρ = (x.eval ρ == y.eval ρ) := by
  have hr : ∀ (z : (PtT (ℓ := ℓ) (Pt := Pt)).denote),
      (Expr.renameM (Δ := PtT :: Γ) (fun ⦃_⦄ v => Var.succ v) y).eval (.cons z ρ) = y.eval ρ :=
    fun z => Expr.renameM_eval (Δ := PtT :: Γ) y (ρ₁ := ρ) (ρ₂ := .cons z ρ) (fun _ _ => rfl)
  dsimp only [optPtEqExpr, Expr.eval]
  cases hx : x.eval ρ with
  | none => cases hy : y.eval ρ <;> simp
  | some a =>
    cases hy : y.eval ρ with
    | none => simp [hr, hy]
    | some b =>
      simp only [hr, hy, opPure_eval, opPtEncPk_eval, AtomicPureOp.eval, Expr.eval,
        env_get_zero, env_get_succ]
      apply Bool.eq_iff_iff.mpr
      simp [beq_iff_eq, hinj.eq_iff]

theorem optPtEqExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) :
    (optPtEqExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 16 := by
  simp only [optPtEqExpr, opPure_cost, opPtEncPk_cost, AtomicPureOp.cost, Expr.cost,
    Expr.renameM_cost]
  omega

def eqLpubExpr {Γ : List (Ty S)} (x y : Expr O Γ lpubT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod lpubT lpubT :: Γ) (.prod lpubT lpubT) := .var .zero
     let a := Expr.fst p
     let b := Expr.snd p
     .and (opPure ℓ Pt C encT .u32Eq (.pair (.fst a) (.fst b)))
       (.and (opPure ℓ Pt C encT (.bytesEq 32 32) (.pair (.fst (.snd a)) (.fst (.snd b))))
         (.and (opPure ℓ Pt C encT .bv256Eq
             (.pair (.fst (.snd (.snd a))) (.fst (.snd (.snd b)))))
           (optBytesEqExpr ℓ Pt C encT
             (.snd (.snd (.snd a))) (.snd (.snd (.snd b)))))))

theorem eqLpubExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ lpubT) (ρ : Env Γ) :
    (eqLpubExpr ℓ Pt C encT x y).eval ρ = (lpubOfV (x.eval ρ) == lpubOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨pn₁, pq₁, s₁, ad₁⟩
  rcases hy : y.eval ρ with ⟨pn₂, pq₂, s₂, ad₂⟩
  have hopt := optBytesEqExpr_eval ℓ Pt C encT
    (.snd (.snd (.snd (.fst (.var .zero)))))
    (.snd (.snd (.snd (.snd (.var .zero)))))
    (.cons ((pn₁, (pq₁, (s₁, ad₁))), (pn₂, (pq₂, (s₂, ad₂)))) ρ)
  dsimp only [eqLpubExpr, Expr.eval]
  rw [hx, hy, hopt]
  dsimp only [Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval, lpubOfV]
  have hs : (s₁ == s₂) = (salt32OfV s₁ == salt32OfV s₂) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨congrArg salt32OfV, fun h => by
      have := congrArg salt32V h; simpa [salt32V_salt32OfV] using this⟩
  rw [hs]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, LibsignalMsgPublicPart.mk.injEq]

theorem eqLpubExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ lpubT) :
    (eqLpubExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 200 := by
  have hopt := optBytesEqExpr_cost ℓ Pt C encT (Γ := .prod lpubT lpubT :: Γ)
    (.snd (.snd (.snd (.fst (.var .zero)))))
    (.snd (.snd (.snd (.snd (.var .zero)))))
  simp only [Expr.cost] at hopt
  simp only [eqLpubExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat]
  omega

def eqFig8PubAdExpr {Γ : List (Ty S)} (x y : Expr O Γ fig8PubAdT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod fig8PubAdT fig8PubAdT :: Γ) (.prod fig8PubAdT fig8PubAdT) := .var .zero
     let a := Expr.fst p
     let b := Expr.snd p
     .and (.eqN (.fst (.fst a)) (.fst (.fst b)))
       (.and (optPtEqExpr ℓ Pt C encT (.snd (.fst a)) (.snd (.fst b)))
         (eqLpubExpr ℓ Pt C encT (.snd a) (.snd b))))

theorem eqFig8PubAdExpr_eval [DecidableEq Pt] (hinj : Function.Injective encT)
    {Γ : List (Ty S)} (x y : Expr O Γ fig8PubAdT) (ρ : Env Γ) :
    (eqFig8PubAdExpr ℓ Pt C encT x y).eval ρ =
      decide (fig8PubAdOfV (x.eval ρ) = fig8PubAdOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨⟨t₁, T₁⟩, pub₁⟩
  rcases hy : y.eval ρ with ⟨⟨t₂, T₂⟩, pub₂⟩
  let ρ' : Env (.prod fig8PubAdT fig8PubAdT :: Γ) := .cons (((t₁, T₁), pub₁), ((t₂, T₂), pub₂)) ρ
  have hpt := optPtEqExpr_eval ℓ Pt C encT hinj (.snd (.fst (.fst (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) ρ'
  have hpub := eqLpubExpr_eval ℓ Pt C encT (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero))) ρ'
  dsimp only [eqFig8PubAdExpr, Expr.eval]
  rw [hx, hy]
  change (decide (t₁ = t₂) && ((optPtEqExpr ℓ Pt C encT _ _).eval ρ' &&
    (eqLpubExpr ℓ Pt C encT _ _).eval ρ')) = _
  rw [hpt, hpub]
  dsimp only [ρ', Expr.eval, env_get_zero, fig8PubAdOfV]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq]
  tauto

theorem eqFig8PubAdExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ fig8PubAdT) :
    (eqFig8PubAdExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 250 := by
  have hpt := optPtEqExpr_cost ℓ Pt C encT (Γ := .prod fig8PubAdT fig8PubAdT :: Γ)
    (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))
  have hpub := eqLpubExpr_cost ℓ Pt C encT (Γ := .prod fig8PubAdT fig8PubAdT :: Γ)
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost] at hpt hpub
  simp only [eqFig8PubAdExpr, Expr.cost]
  omega

def eqSlotAdExpr {Γ : List (Ty S)} (x y : Expr O Γ slotAdT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod slotAdT slotAdT :: Γ) (.prod slotAdT slotAdT) := .var .zero
     .and (.eqN (.fst (.fst p)) (.fst (.snd p)))
       (eqFig8PubAdExpr ℓ Pt C encT (.snd (.fst p)) (.snd (.snd p))))

theorem eqSlotAdExpr_eval [DecidableEq Pt] (hinj : Function.Injective encT)
    {Γ : List (Ty S)} (x y : Expr O Γ slotAdT) (ρ : Env Γ) :
    (eqSlotAdExpr ℓ Pt C encT x y).eval ρ =
      decide (slotAdOfV (x.eval ρ) = slotAdOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨i₁, ad₁⟩
  rcases hy : y.eval ρ with ⟨i₂, ad₂⟩
  let ρ' : Env (.prod slotAdT slotAdT :: Γ) := .cons ((i₁, ad₁), (i₂, ad₂)) ρ
  have had :
      (eqFig8PubAdExpr ℓ Pt C encT (.snd (.fst (.var .zero)))
        (.snd (.snd (.var .zero)))).eval ρ' =
      decide (fig8PubAdOfV ad₁ = fig8PubAdOfV ad₂) :=
    eqFig8PubAdExpr_eval ℓ Pt C encT hinj (.snd (.fst (.var .zero)))
      (.snd (.snd (.var .zero))) ρ'
  dsimp only [eqSlotAdExpr, Expr.eval]
  rw [hx, hy]
  change (decide (i₁ = i₂) && (eqFig8PubAdExpr ℓ Pt C encT _ _).eval ρ') = _
  rw [had]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, slotAdOfV, Prod.mk.injEq]

theorem eqSlotAdExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ slotAdT) :
    (eqSlotAdExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 270 := by
  have had := eqFig8PubAdExpr_cost ℓ Pt C encT (Γ := .prod slotAdT slotAdT :: Γ)
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost] at had
  simp only [eqSlotAdExpr, Expr.cost]
  omega

def eqWireSaltCtExpr {Γ : List (Ty S)} (x y : Expr O Γ wireSaltCtT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod wireSaltCtT wireSaltCtT :: Γ) (.prod wireSaltCtT wireSaltCtT) := .var .zero
     let a := Expr.fst p
     let b := Expr.snd p
     .and (opPure ℓ Pt C encT (.bytesEq 32 32) (.pair (.fst (.fst a)) (.fst (.fst b))))
       (.and (opPure ℓ Pt C encT .u64Eq (.pair (.snd (.fst a)) (.snd (.fst b))))
         (opPure ℓ Pt C encT .bv256Eq (.pair (.snd a) (.snd b)))))

theorem eqWireSaltCtExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ wireSaltCtT) (ρ : Env Γ) :
    (eqWireSaltCtExpr ℓ Pt C encT x y).eval ρ =
      decide (wireSaltCtOfV (x.eval ρ) = wireSaltCtOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨⟨ser₁, tag₁⟩, s₁⟩
  rcases hy : y.eval ρ with ⟨⟨ser₂, tag₂⟩, s₂⟩
  dsimp only [eqWireSaltCtExpr, Expr.eval]
  rw [hx, hy]
  dsimp only [Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval]
  have hs : (s₁ == s₂) = (salt32OfV s₁ == salt32OfV s₂) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨congrArg salt32OfV, fun h => by
      have := congrArg salt32V h; simpa [salt32V_salt32OfV] using this⟩
  rw [hs]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, wireSaltCtOfV, Prod.mk.injEq]
  tauto

theorem eqWireSaltCtExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ wireSaltCtT) :
    (eqWireSaltCtExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 130 := by
  simp only [eqWireSaltCtExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat]
  omega

def eqLctExpr {Γ : List (Ty S)} (x y : Expr O Γ lctT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod lctT lctT :: Γ) (.prod lctT lctT) := .var .zero
     .and (.eqN (.fst (.fst p)) (.fst (.snd p)))
       (eqWireSaltCtExpr ℓ Pt C encT (.snd (.fst p)) (.snd (.snd p))))

theorem eqLctExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ lctT) (ρ : Env Γ) :
    (eqLctExpr ℓ Pt C encT x y).eval ρ =
      decide (lctOfV (x.eval ρ) = lctOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨i₁, c₁⟩
  rcases hy : y.eval ρ with ⟨i₂, c₂⟩
  let ρ' : Env (.prod lctT lctT :: Γ) := .cons ((i₁, c₁), (i₂, c₂)) ρ
  have hc :
      (eqWireSaltCtExpr ℓ Pt C encT (.snd (.fst (.var .zero)))
        (.snd (.snd (.var .zero)))).eval ρ' =
      decide (wireSaltCtOfV c₁ = wireSaltCtOfV c₂) :=
    eqWireSaltCtExpr_eval ℓ Pt C encT (.snd (.fst (.var .zero)))
      (.snd (.snd (.var .zero))) ρ'
  dsimp only [eqLctExpr, Expr.eval]
  rw [hx, hy]
  change (decide (i₁ = i₂) && (eqWireSaltCtExpr ℓ Pt C encT _ _).eval ρ') = _
  rw [hc]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, lctOfV, Prod.mk.injEq]

theorem eqLctExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ lctT) :
    (eqLctExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 150 := by
  have hc := eqWireSaltCtExpr_cost ℓ Pt C encT (Γ := .prod lctT lctT :: Γ)
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost] at hc
  simp only [eqLctExpr, Expr.cost]
  omega

def lPubOfExpr {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) : Expr O Γ (.opt lpubT) :=
  .letE cV
    (.caseOpt
      (opPure ℓ Pt C encT .signalMsgParse
        (opPure ℓ Pt C encT .bytesAppend8
          (.pair (.fst (.fst (.var .zero)))
            (opPure ℓ Pt C encT (.bytesLit 8 (List.replicate 8 0#8)) .unit))))
      .none
      (.some
        (.pair (.snd (.snd (.snd (.fst (.var .zero)))))
          (.pair (.fst (.snd (.snd (.var .zero))))
            (.pair (.snd (.var (.succ .zero)))
              (.snd (.snd (.snd (.var .zero)))))))))

theorem lPubOfExpr_eval {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) (ρ : Env Γ) :
    (lPubOfExpr ℓ Pt C encT cV).eval ρ =
      (lPubOf protoSignalCodec (wireSaltCtOfV (cV.eval ρ))).map lpubV := by
  rcases hcv : cV.eval ρ with ⟨⟨ser, tag⟩, saltBv⟩
  have hparse := atomicPureOps_signalMsgParse_lossless ℓ Pt (ser ++ List.replicate 8 0#8)
  have happ : (opPure ℓ Pt C encT .bytesAppend8
      (.pair (.fst (.fst (.var .zero)))
        (opPure ℓ Pt C encT (.bytesLit 8 (List.replicate 8 0#8)) .unit))).eval
      (.cons ((ser, tag), saltBv) ρ) = ser ++ List.replicate 8 0#8 := by
    simp [opPure_eval, AtomicPureOp.eval, Expr.eval]
  dsimp only [lPubOfExpr, Expr.eval]
  rw [hcv, opPure_eval, happ, hparse]
  dsimp only [wireSaltCtOfV, lPubOf, signalWireCodec, macLength]
  rcases htf : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0#8) with _ | m
  · rfl
  · simp [SignalMessage.header, lpubV, salt32V_salt32OfV]

theorem lPubOfExpr_cost {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) :
    (lPubOfExpr ℓ Pt C encT cV).cost ≤ cV.cost + (ℓ / 32 + 65) := by
  simp only [lPubOfExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, List.length_replicate,
    PNat.val_ofNat]
  omega

def chainGenExpr {Γ : List (Ty S)} (ck : Expr O Γ BV256) : Expr O Γ (.prod BV256 BV256) :=
  .letE ck
    (.pair
      (opSym ℓ Pt C encT (.hmacSha256Op 1)
        (.pair (.var .zero)
          (opPure ℓ Pt C encT (.bytesLit 1 [chainKeySeed]) .unit)))
      (opSym ℓ Pt C encT (.hmacSha256Op 1)
        (.pair (.var .zero)
          (opPure ℓ Pt C encT (.bytesLit 1 [messageKeySeed]) .unit))))

@[simp] theorem chainGenExpr_eval {Γ : List (Ty S)} (ck : Expr O Γ BV256) (ρ : Env Γ) (p : ℕ) :
    (chainGenExpr ℓ Pt C encT ck).eval ρ =
      (lChainPRG C.F p).gen (ck.eval ρ) := by
  dsimp only [chainGenExpr, lChainPRG, hmacPRF, MACScheme.tag, chainHmac,
    Expr.eval, env_get_zero, opSym_eval, opPure_eval, AtomicSymOp.eval, AtomicPureOp.eval]

theorem chainGenExpr_cost {Γ : List (Ty S)} (ck : Expr O Γ BV256) :
    (chainGenExpr ℓ Pt C encT ck).cost ≤ ck.cost + 40 := by
  simp only [chainGenExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost, Expr.cost,
    List.length_singleton, PNat.val_ofNat]
  omega

def lIdsExpr (idOf : Party → IdentityKey) {Γ : List (Ty S)} (tE : Expr O Γ .nat) :
    Expr O Γ (B 66) :=
  .ite (.eqN (.modK 2 tE) (.nat 1))
    (opPure ℓ Pt C encT (.bytesLit 66 (lIds idOf 1).toList) .unit)
    (opPure ℓ Pt C encT (.bytesLit 66 (lIds idOf 0).toList) .unit)

theorem lIdsExpr_eval (idOf : Party → IdentityKey) {Γ : List (Ty S)} (tE : Expr O Γ .nat)
    (ρ : Env Γ) :
    (lIdsExpr ℓ Pt C encT idOf tE).eval ρ = (lIds idOf (tE.eval ρ)).toList := by
  dsimp only [lIdsExpr, Expr.eval, opPure_eval, AtomicPureOp.eval, lIds, Party.senderOf]
  by_cases h : tE.eval ρ % 2 = 1 <;> simp [h]

theorem lIdsExpr_cost (idOf : Party → IdentityKey) {Γ : List (Ty S)} (tE : Expr O Γ .nat) :
    (lIdsExpr ℓ Pt C encT idOf tE).cost ≤ tE.cost + 145 := by
  simp only [lIdsExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat,
    List.Vector.toList_length]
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  omega

def lHeaderExpr {Γ : List (Ty S)} (aE : Expr O Γ slotAdT) : Expr O Γ wireSignalHdrT :=
  .letE aE
    (let v : Expr O (slotAdT :: Γ) slotAdT := .var .zero
     let i := Expr.fst v
     let T? := Expr.snd (Expr.fst (Expr.snd v))
     let pub := Expr.snd (Expr.snd v)
     let srk := Expr.caseOpt T? (pkLitExpr ℓ Pt C encT dummyKey)
       (opPtEncPk ℓ Pt C encT (.var .zero))
     .pair
       (.pair (opPure ℓ Pt C encT (.u8Lit currentVersion) .unit)
         (.pair srk
           (.pair (opPure ℓ Pt C encT .u32OfNat (.sub i (.nat 1))) (Expr.fst pub))))
       (.pair (Expr.fst (Expr.snd pub)) (Expr.snd (Expr.snd (Expr.snd pub)))))

theorem lHeaderExpr_eval {Γ : List (Ty S)} (aE : Expr O Γ slotAdT) (ρ : Env Γ) :
    (lHeaderExpr ℓ Pt C encT aE).eval ρ =
      wireSignalHdrV
        (let a := slotAdOfV (aE.eval ρ); lHeader encT a.1 a.2.1 a.2.2) := by
  rcases ha : aE.eval ρ with ⟨i, ⟨t, T?⟩, ⟨pn, pq, saltBv, addrs⟩⟩
  dsimp only [lHeaderExpr, Expr.eval]
  rw [ha]
  dsimp only [slotAdOfV, fig8PubAdOfV, lpubOfV, lHeader, wireSignalHdrV,
    Expr.eval, env_get_zero, opPure_eval, opPtEncPk_eval, AtomicPureOp.eval]
  cases T? <;> simp

theorem lHeaderExpr_cost {Γ : List (Ty S)} (aE : Expr O Γ slotAdT) :
    (lHeaderExpr ℓ Pt C encT aE).cost ≤ aE.cost + 140 := by
  have hpk := pkLitExpr_cost ℓ Pt C encT (Γ := slotAdT :: Γ) dummyKey
  simp only [lHeaderExpr, opPure_cost, opPtEncPk_cost, AtomicPureOp.cost, Expr.cost, hpk]
  have hb1 : bits 1 ≤ 2 := by decide
  omega

def eqWireSignalHdrExpr {Γ : List (Ty S)} (x y : Expr O Γ wireSignalHdrT) : Expr O Γ .bool :=
  .letE (.pair x y)
    (let p : Expr O (.prod wireSignalHdrT wireSignalHdrT :: Γ)
         (.prod wireSignalHdrT wireSignalHdrT) := .var .zero
     let a := Expr.fst p
     let b := Expr.snd p
     .and (opPure ℓ Pt C encT .u8Eq (.pair (.fst (.fst a)) (.fst (.fst b))))
       (.and (opPure ℓ Pt C encT .pkEq
           (.pair (.fst (.snd (.fst a))) (.fst (.snd (.fst b)))))
         (.and (opPure ℓ Pt C encT .u32Eq
             (.pair (.fst (.snd (.snd (.fst a)))) (.fst (.snd (.snd (.fst b))))))
           (.and (opPure ℓ Pt C encT .u32Eq
               (.pair (.snd (.snd (.snd (.fst a)))) (.snd (.snd (.snd (.fst b))))))
             (.and (opPure ℓ Pt C encT (.bytesEq 32 32)
                 (.pair (.fst (.snd a)) (.fst (.snd b))))
               (optBytesEqExpr ℓ Pt C encT (.snd (.snd a)) (.snd (.snd b))))))))

theorem eqWireSignalHdrExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ wireSignalHdrT) (ρ : Env Γ) :
    (eqWireSignalHdrExpr ℓ Pt C encT x y).eval ρ =
      (wireSignalHdrOfV (x.eval ρ) == wireSignalHdrOfV (y.eval ρ)) := by
  rcases hx : x.eval ρ with ⟨⟨v₁, rk₁, c₁, pc₁⟩, pq₁, ad₁⟩
  rcases hy : y.eval ρ with ⟨⟨v₂, rk₂, c₂, pc₂⟩, pq₂, ad₂⟩
  let ρ' : Env (.prod wireSignalHdrT wireSignalHdrT :: Γ) :=
    .cons (((v₁, (rk₁, (c₁, pc₁))), (pq₁, ad₁)), ((v₂, (rk₂, (c₂, pc₂))), (pq₂, ad₂))) ρ
  have hopt := optBytesEqExpr_eval ℓ Pt C encT (.snd (.snd (.fst (.var .zero))))
    (.snd (.snd (.snd (.var .zero)))) ρ'
  dsimp only [eqWireSignalHdrExpr, Expr.eval]
  rw [hx, hy]
  change ((v₁ == v₂) && ((rk₁ == rk₂) && ((c₁ == c₂) && ((pc₁ == pc₂) &&
    ((pq₁ == pq₂) && (optBytesEqExpr ℓ Pt C encT _ _).eval ρ'))))) = _
  rw [hopt]
  dsimp only [ρ', Expr.eval, env_get_zero, wireSignalHdrOfV]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, SignalHeader.mk.injEq]

theorem eqWireSignalHdrExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ wireSignalHdrT) :
    (eqWireSignalHdrExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 230 := by
  have hopt := optBytesEqExpr_cost ℓ Pt C encT (Γ := .prod wireSignalHdrT wireSignalHdrT :: Γ)
    (.snd (.snd (.fst (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  simp only [Expr.cost] at hopt
  simp only [eqWireSignalHdrExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat]
  omega

def fitPlainExpr {Γ : List (Ty S)} (m : Expr O Γ (B 32)) : Expr O Γ PlainT :=
  opPure ℓ Pt C encT .fitPlain m

@[simp] theorem fitPlainExpr_eval {Γ : List (Ty S)} (m : Expr O Γ (B 32)) (ρ : Env Γ) :
    (fitPlainExpr ℓ Pt C encT m).eval ρ = padOrTruncatePlain ℓ (m.eval ρ) := rfl

theorem fitPlainExpr_cost {Γ : List (Ty S)} (m : Expr O Γ (B 32)) :
    (fitPlainExpr ℓ Pt C encT m).cost ≤ m.cost + (ℓ / 32 + 4) := by
  simp only [fitPlainExpr, opPure_cost, AtomicPureOp.cost]
  omega

def eqPlainExpr {Γ : List (Ty S)} (x y : Expr O Γ PlainT) : Expr O Γ .bool :=
  opPure ℓ Pt C encT .plainEq (.pair x y)

@[simp] theorem eqPlainExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ PlainT) (ρ : Env Γ) :
    (eqPlainExpr ℓ Pt C encT x y).eval ρ = decide (x.eval ρ = y.eval ρ) := rfl

theorem eqPlainExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ PlainT) :
    (eqPlainExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + (ℓ / 32 + 4) := by
  simp only [eqPlainExpr, opPure_cost, AtomicPureOp.cost, Expr.cost]
  omega

def eqSaltExpr {Γ : List (Ty S)} (x y : Expr O Γ BV256) : Expr O Γ .bool :=
  opPure ℓ Pt C encT .bv256Eq (.pair x y)

theorem eqSaltExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ BV256) (ρ : Env Γ) :
    (eqSaltExpr ℓ Pt C encT x y).eval ρ = (salt32OfV (x.eval ρ) == salt32OfV (y.eval ρ)) := by
  dsimp only [eqSaltExpr, Expr.eval, opPure_eval, AtomicPureOp.eval]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨congrArg salt32OfV, fun h => by
    have := congrArg salt32V h; simpa [salt32V_salt32OfV] using this⟩

theorem eqSaltExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ BV256) :
    (eqSaltExpr ℓ Pt C encT x y).cost ≤ x.cost + y.cost + 4 := by
  simp only [eqSaltExpr, opPure_cost, AtomicPureOp.cost, Expr.cost]
  omega

def saltOfSlotAdExpr {Γ : List (Ty S)} (a : Expr O Γ slotAdT) : Expr O Γ BV256 :=
  .fst (.snd (.snd (.snd (.snd a))))

@[simp] theorem saltOfSlotAdExpr_eval {Γ : List (Ty S)} (a : Expr O Γ slotAdT) (ρ : Env Γ) :
    (saltOfSlotAdExpr ℓ Pt C encT a).eval ρ = salt32V (slotAdOfV (a.eval ρ)).2.2.salt := by
  rcases ha : a.eval ρ with ⟨i, h, pn, pq, s, ad⟩
  simp [saltOfSlotAdExpr, Expr.eval, ha, slotAdOfV, fig8PubAdOfV, lpubOfV, salt32V_salt32OfV]

theorem saltOfSlotAdExpr_cost {Γ : List (Ty S)} (a : Expr O Γ slotAdT) :
    (saltOfSlotAdExpr ℓ Pt C encT a).cost = a.cost + 5 := by
  simp only [saltOfSlotAdExpr, Expr.cost]

end OpInjections

section ClampedCodecAndByteHelpers

/-- Protobuf `SignalMessage` codec clamping `pqRatchet` to 96 bytes and `addresses` to 128 bytes on
`encode`, agreeing with `protoSignalCodec` under `atomicShortB`. -/
def clampedProtoSignalCodec : SignalMessageProtoCodec where
  encode p := protoSignalCodec.encode
    { p with
      pqRatchet := p.pqRatchet.map (·.take 96)
      addresses := p.addresses.map (·.take 128) }
  decode := protoSignalCodec.decode

@[simp] theorem clampedProtoSignalCodec_decode :
    clampedProtoSignalCodec.decode = protoSignalCodec.decode := rfl

theorem serializeContent_clampedProtoSignalCodec
    (v : BitVec 8) (rk : PublicKey) (ctr pctr : BitVec 32) (ct pq : Bytes) (addrs : Option Bytes) :
    serializeContent clampedProtoSignalCodec v rk ctr pctr ct pq addrs =
      serializeContent protoSignalCodec v rk ctr pctr ct (pq.take 96) (addrs.map (·.take 128)) := by
  have hpq : (if pq.isEmpty then none else some pq).map (·.take 96) =
      if (pq.take 96).isEmpty then none else some (pq.take 96) := by
    cases pq <;> rfl
  simp only [serializeContent, clampedProtoSignalCodec, hpq]

theorem serializeContent_clampedProtoSignalCodec_of_short
    (v : BitVec 8) (rk : PublicKey) (ctr pctr : BitVec 32) (ct pq : Bytes) (addrs : Option Bytes)
    (hpq : pq.length ≤ 96) (haddr : ∀ a ∈ addrs, a.length ≤ 128) :
    serializeContent clampedProtoSignalCodec v rk ctr pctr ct pq addrs =
      serializeContent protoSignalCodec v rk ctr pctr ct pq addrs := by
  rw [serializeContent_clampedProtoSignalCodec, List.take_of_length_le hpq]
  have hm : addrs.map (·.take 128) = addrs := by
    cases ha : addrs with
    | none => rfl
    | some a => dsimp only [Option.map]; rw [List.take_of_length_le (haddr a ha)]
  rw [hm]

@[simp] theorem lWire_clamped_dec_eq (C : Crypto) (ℓ : ℕ) :
    (lWire C clampedProtoSignalCodec ℓ).dec = (lWire C protoSignalCodec ℓ).dec := rfl

@[simp] theorem lAeadK_clamped_dec_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    (lAeadK C clampedProtoSignalCodec ℓ encT idOf).dec =
      (lAeadK C protoSignalCodec ℓ encT idOf).dec := rfl

@[simp] theorem lAead_clamped_dec_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    (lAead C clampedProtoSignalCodec ℓ encT idOf).dec =
      (lAead C protoSignalCodec ℓ encT idOf).dec := rfl

@[simp] theorem lAeadR_clamped_dec_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec =
      (lAeadR C protoSignalCodec ℓ encT idOf).dec := rfl

@[simp] theorem lPubOf_clamped_eq :
    lPubOf clampedProtoSignalCodec = lPubOf protoSignalCodec := rfl

theorem lAeadK_clamped_enc_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (mk : DerivedMessageKeys)
    (a : (ℕ × Header Pt) × LibsignalMsgPublicPart) (m : Plain ℓ)
    (hshort : atomicShortB a.2 = true) :
    (lAeadK C clampedProtoSignalCodec ℓ encT idOf).enc mk a m =
      (lAeadK C protoSignalCodec ℓ encT idOf).enc mk a m := by
  obtain ⟨hpq, haddr⟩ := (atomicShortB_iff a.2).mp hshort
  dsimp only [lAeadK, lWire, libsignalWireAead, wireEncode, signalWireCodec, lHeader]
  rw [serializeContent_clampedProtoSignalCodec_of_short _ _ _ _ _ _ _ hpq haddr]

theorem lAeadR_clamped_enc_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (seed : BitVec 256)
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (m : Plain ℓ)
    (hshort : atomicShortB a.2.2 = true) :
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf).enc seed a m =
      (lAeadR C protoSignalCodec ℓ encT idOf).enc seed a m := by
  exact lAeadK_clamped_enc_eq C ℓ encT idOf _ ((a.1, a.2.1), a.2.2) m hshort

theorem lIdeal_clamped_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart))
    (hshort : atomicShortB a.2.2 = true) :
    lIdeal C clampedProtoSignalCodec ℓ encT a =
      lIdeal C protoSignalCodec ℓ encT a := by
  obtain ⟨hpq, haddr⟩ := (atomicShortB_iff a.2.2).mp hshort
  dsimp only [lIdeal, WireAEAD.idealEnc, lWire, libsignalWireAead, wireEncode, signalWireCodec,
    lHeader]
  simp only [serializeContent_clampedProtoSignalCodec_of_short _ _ _ _ _ _ _ hpq haddr]

private theorem extractLsb'_zero_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h64 : i < 64 := by omega
  simp [hi, h64]

private theorem extractLsb'_succ_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) (j : ℕ)
    (hj : j + 1 < 8) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 64 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToWordLE64 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h8 : j < 8) :
    (bytesToWordLE 64 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToWordLE] using
        extractLsb'_zero_bytesToWordLE64_cons b (bytesToWordLE 64 rest)
    | succ j =>
      have hcons : bytesToWordLE 64 (b :: rest) =
          (bytesToWordLE 64 rest <<< 8) ||| b.zeroExtend 64 := rfl
      rw [hcons, extractLsb'_succ_bytesToWordLE64_cons b (bytesToWordLE 64 rest) j h8,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

@[simp] theorem toLEBytes8_length (v : BitVec 64) : (toLEBytes 8 v).length = 8 := by
  simp [toLEBytes]

theorem bytesToWordLE64_eq_bytesToWord64LE (bs : List (BitVec 8)) :
    bytesToWordLE 64 bs = bytesToWord64LE bs := rfl

theorem bytesToWordLE64_toLEBytes8 (v : BitVec 64) :
    bytesToWordLE 64 (toLEBytes 8 v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE64 (toLEBytes 8 v) (i / 8) (by simp [toLEBytes, hj]) hj)
  simp only [toLEBytes, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem toLEBytes8_bytesToWordLE64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    toLEBytes 8 (bytesToWordLE 64 bs) = bs := by
  refine List.ext_getElem (by simp [toLEBytes, h]) fun j h1 h2 => ?_
  simp only [toLEBytes, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE64 bs j h2 (by omega)

theorem tryFrom_append_sfx8 (codec : SignalMessageProtoCodec)
    (ser mac₁ mac₂ : List (BitVec 8))
    (hm₁ : mac₁.length = macLength) (hm₂ : mac₂.length = macLength) :
    SignalMessage.tryFrom codec (ser ++ mac₁) =
      (SignalMessage.tryFrom codec (ser ++ mac₂)).map
        (fun m => { m with serialized := ser ++ mac₁ }) := by
  cases ser with
  | nil =>
    unfold SignalMessage.tryFrom
    simp only [List.nil_append, hm₁, hm₂, macLength, show (8 : ℕ) < 8 + 1 by decide, ↓reduceIte]
    rfl
  | cons hd tl =>
    have hlen : (hd :: tl ++ mac₁).length = (hd :: tl ++ mac₂).length := by simp [hm₁, hm₂]
    have hhead : (hd :: tl ++ mac₁).headD 0 = (hd :: tl ++ mac₂).headD 0 := rfl
    have htake₁ :
        (hd :: tl ++ mac₁).take ((hd :: tl ++ mac₁).length - macLength) = hd :: tl := by
      rw [List.length_append, hm₁, Nat.add_sub_cancel,
        List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    have htake₂ :
        (hd :: tl ++ mac₂).take ((hd :: tl ++ mac₂).length - macLength) = hd :: tl := by
      rw [List.length_append, hm₂, Nat.add_sub_cancel,
        List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    unfold SignalMessage.tryFrom
    rw [htake₁, htake₂, hlen, hhead]
    dsimp only [Bind.bind, Except.bind]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> rfl

theorem macIds_ite_mod2 (idOf : Party → IdentityKey) (t : ℕ) :
    (let p := if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
     macIds p.1 p.2) = lIds idOf t := by
  unfold lIds Party.senderOf Party.other
  by_cases h : t % 2 = 1 <;> simp [h]

theorem addressCheckPasses_self (x : Option (List (BitVec 8))) :
    addressCheckPasses x x = true := by
  cases x with
  | none => rfl
  | some a => simp [addressCheckPasses]

theorem verifyMacWithAddresses_append_tag (F : ShaCompress)
    (m : SignalMessage) (ser : List (BitVec 8)) (tag : BitVec 64)
    (idOf : Party → IdentityKey) (t : ℕ) (macKey : BitVec 256) :
    let ids := if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
    ({ m with serialized := ser ++ toLEBytes 8 tag }).verifyMacWithAddresses
      F m.addresses ids.1 ids.2 macKey =
    ((hmacScheme F).tag macKey ((lIds idOf t).toList ++ ser) == tag) := by
  intro ids
  dsimp only [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac]
  have hlen : (toLEBytes 8 tag).length = macLength := toLEBytes8_length tag
  have htake : (ser ++ toLEBytes 8 tag).take ((ser ++ toLEBytes 8 tag).length - macLength) = ser := by
    rw [List.length_append, hlen, Nat.add_sub_cancel,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop : (ser ++ toLEBytes 8 tag).drop ((ser ++ toLEBytes 8 tag).length - macLength) =
      toLEBytes 8 tag := by
    rw [List.length_append, hlen, Nat.add_sub_cancel,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  rw [htake, hdrop, addressCheckPasses_self, Bool.and_true]
  have hids : macIds ids.1 ids.2 = lIds idOf t := macIds_ite_mod2 idOf t
  have hcmlen : (computeMac F ids.1 ids.2 macKey ser).length = 8 :=
    computeMac_length F ids.1 ids.2 macKey ser
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have hw := congrArg (bytesToWordLE 64) h
    rw [bytesToWordLE64_toLEBytes8] at hw
    dsimp only [computeMac, hmacScheme] at hw ⊢
    rw [← bytesToWordLE64_eq_bytesToWord64LE, ← hids]
    exact hw
  · intro h
    dsimp only [hmacScheme] at h
    rw [← bytesToWordLE64_eq_bytesToWord64LE, ← hids] at h
    have hw := congrArg (toLEBytes 8) h
    change toLEBytes 8 (bytesToWordLE 64 (computeMac F ids.1 ids.2 macKey ser)) =
      toLEBytes 8 tag at hw
    rwa [toLEBytes8_bytesToWordLE64 _ hcmlen] at hw

theorem aesCbcEncrypt_eq_cbcPkcs7 {ℓ : ℕ} (E : BitVec 256 → Block → Block)
    (k : BitVec 256) (iv : Block) (m : Plain ℓ) :
    aesCbcEncrypt E k iv m.toList =
      ((cbcPkcs7EncryptOnly E ℓ).enc (k, iv) m).toList.flatMap blockToBytesLE := by
  rcases m with ⟨mList, rfl⟩
  rfl

end ClampedCodecAndByteHelpers

section AeadMacros

variable (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

local notation "S" => atomicSig ℓ Pt
local notation "O" => atomicFsOps ℓ Pt C encT

@[reducible] def exprWkTop1 {Γ : List (Ty S)} {a b : Ty S} (e : Expr O [a] b) :
    Expr O (a :: Γ) b :=
  Expr.renameM (fun ⦃_⦄ v => match v with | .zero => .zero | .succ w => nomatch w) e

theorem exprWkTop1_eval {Γ : List (Ty S)} {a b : Ty S} (e : Expr O [a] b)
    (x : a.denote) (ρ : Env Γ) :
    (exprWkTop1 ℓ Pt C encT e).eval (.cons x ρ) = e.eval (.cons x .nil) :=
  Expr.renameM_eval e fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

@[simp] theorem exprWkTop1_cost {Γ : List (Ty S)} {a b : Ty S} (e : Expr O [a] b) :
    (exprWkTop1 ℓ Pt C encT (Γ := Γ) e).cost = e.cost := by
  simp [exprWkTop1]

private theorem eval_pair {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ a) (y : Expr O Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

private theorem eval_fst {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.fst x).eval ρ = (x.eval ρ).1 := rfl

private theorem eval_snd {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.snd x).eval ρ = (x.eval ρ).2 := rfl

def aeadKEncExpr :
    Expr O [.prod derivedMsgKeysT (.prod slotAdT PlainT)] wireSaltCtT :=
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT PlainT)
  let Γ₀ : List (Ty S) := [argT]
  let Γ₁ : List (Ty S) := B 32 :: Γ₀
  let vArg : Expr O Γ₀ argT := .var .zero
  let mk := Expr.fst vArg
  let ad := Expr.fst (Expr.snd vArg)
  let m := Expr.snd (Expr.snd vArg)
  let i := Expr.fst ad
  let hdr := Expr.fst (Expr.snd ad)
  let pub := Expr.snd (Expr.snd ad)
  let ct := opSym ℓ Pt C encT .aes256CbcEnc
    (.pair (Expr.fst (Expr.fst mk)) (.pair (Expr.snd (Expr.fst mk)) m))
  let srk : Expr O Γ₀ PK := Expr.caseOpt (Expr.snd hdr)
    (pkLitExpr ℓ Pt C encT dummyKey)
    (opPtEncPk ℓ Pt C encT (.var .zero))
  let ids : Expr O Γ₀ (.prod IdKey IdKey) :=
    Expr.ite (.eqN (.modK 2 (Expr.fst hdr)) (.nat 1))
      (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
      (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))
  let pqClamp := opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 96) (Expr.fst (Expr.snd pub)))
  let addrsClamp : Expr O Γ₀ (.opt (B 32)) :=
    Expr.caseOpt (Expr.snd (Expr.snd (Expr.snd pub))) .none
      (.some (opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 128) (.var .zero))))
  let sHdr := Expr.pair (opPure ℓ Pt C encT (.u8Lit currentVersion) .unit)
    (.pair srk (.pair (opPure ℓ Pt C encT .u32OfNat (.sub i (.nat 1))) (Expr.fst pub)))
  let raw := opSym ℓ Pt C encT .signalMsgEncode
    (.pair sHdr (.pair ct (.pair pqClamp
      (.pair addrsClamp (.pair (Expr.fst ids) (.pair (Expr.snd ids) (Expr.snd mk)))))))
  .letE raw
    (let vRaw : Expr O Γ₁ (B 32) := .var .zero
     let vArg1 : Expr O Γ₁ argT := .var (.succ .zero)
     let n := Expr.sub (opPure ℓ Pt C encT (.bytesLen 32) vRaw) (.nat 8)
     let ser := opPure ℓ Pt C encT (.bytesTake 32) (.pair n vRaw)
     let tag := opPure ℓ Pt C encT .bytesToU64Le
       (opPure ℓ Pt C encT (.bytesTakeK 32 8)
         (opPure ℓ Pt C encT (.bytesDrop 32) (.pair n vRaw)))
     .pair (.pair ser tag) (saltOfSlotAdExpr ℓ Pt C encT (Expr.fst (Expr.snd vArg1))))

theorem aeadKEncExpr_eval (mk : DerivedMessageKeys)
    (adV : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ) :
    (aeadKEncExpr ℓ Pt C encT idOf).eval (.cons (mk, (adV, m)) .nil) =
      wireSaltCtV
        (let a := slotAdOfV adV
         (lAeadK C clampedProtoSignalCodec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m) := by
  rcases mk with ⟨⟨ck, iv⟩, macKey⟩
  rcases adV with ⟨i, ⟨t, T?⟩, ⟨pn, pq, saltBv, addrs⟩⟩
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT PlainT)
  let ρ₀ : Env [argT] := .cons (((ck, iv), macKey), ((i, ((t, T?), (pn, (pq, (saltBv, addrs))))), m)) .nil
  have hct_len : (aesCbcEncrypt C.E ck iv m.toList).length ≤ 32 * (ℓ / 32 + 2) := by
    rw [aesCbcEncrypt_length_eq]; omega
  have hpq_len : (pq.take 96).length ≤ 96 := List.length_take_le 96 pq
  have haddr_len : ∀ a ∈ addrs.map (·.take 128), a.length ≤ 128 := by
    intro a ha; rcases addrs with _ | b
    · cases ha
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq] at ha
      subst ha; exact List.length_take_le 128 b
  have hsrk :
      (Expr.caseOpt (Expr.snd (Expr.fst (Expr.snd (Expr.fst (Expr.snd (.var .zero))))))
        (pkLitExpr ℓ Pt C encT dummyKey)
        (opPtEncPk ℓ Pt C encT (.var .zero))).eval ρ₀ = (T?.map encT).getD dummyKey := by
    cases T? <;> simp [ρ₀, Expr.eval]
  let idsVal : IdentityKey × IdentityKey :=
    if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
  have hids :
      (Expr.ite (.eqN (.modK 2 (Expr.fst (Expr.fst (Expr.snd (Expr.fst (Expr.snd (.var .zero))))))) (.nat 1))
        (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
        (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))).eval ρ₀ = idsVal := by
    by_cases ht : t % 2 = 1 <;> simp [ρ₀, idsVal, Expr.eval, ht]
  have haddrs_eval :
      (Expr.caseOpt (Expr.snd (Expr.snd (Expr.snd (Expr.snd (Expr.snd (Expr.fst (Expr.snd (.var .zero))))))))
        .none
        (.some (opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 128) (.var .zero))))).eval ρ₀ =
        addrs.map (·.take 128) := by
    cases addrs <;> rfl
  change (aeadKEncExpr ℓ Pt C encT idOf).eval ρ₀ = _
  dsimp only [aeadKEncExpr]
  rw [Expr.eval, opSym_eval]
  simp only [eval_pair, eval_fst, eval_snd]
  rw [hsrk, hids, haddrs_eval, opSym_eval, atomicSymOps_aes256CbcEnc_lossless]
  dsimp only [ρ₀, Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval]
  rw [atomicSymOps_signalMsgEncode_lossless ℓ Pt C currentVersion ((T?.map encT).getD dummyKey)
    (BitVec.ofNat 32 (i - 1)) pn (aesCbcEncrypt C.E ck iv m.toList) (pq.take 96)
    (addrs.map (·.take 128)) idsVal.1 idsVal.2 macKey hct_len hpq_len haddr_len]
  rw [saltOfSlotAdExpr_eval]
  dsimp only [SignalMessage.new, ρ₀, Expr.eval, env_get_zero, env_get_succ, AtomicPureOp.eval,
    PNat.val_ofNat, lAeadK, lWire, libsignalWireAead, wireEncode, signalWireCodec, lHeader,
    slotAdOfV, fig8PubAdOfV, lpubOfV, wireSaltCtV]
  set ser := serializeContent protoSignalCodec currentVersion ((T?.map encT).getD dummyKey)
    (BitVec.ofNat 32 (i - 1)) pn (aesCbcEncrypt C.E ck iv m.toList) (pq.take 96)
    (addrs.map (·.take 128))
  set mac := computeMac C.F idsVal.1 idsVal.2 macKey ser
  have hmac_len : mac.length = 8 := computeMac_length C.F idsVal.1 idsVal.2 macKey ser
  have htake_ser : (ser ++ mac).take ((ser ++ mac).length - 8) = ser := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop_mac : ((ser ++ mac).drop ((ser ++ mac).length - 8)).take 8 = mac := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append,
      List.take_of_length_le (Nat.le_of_eq hmac_len)]
  rw [htake_ser, hdrop_mac, salt32V_salt32OfV]
  have hmacIds : macIds idsVal.1 idsVal.2 = lIds idOf t := macIds_ite_mod2 idOf t
  dsimp only [mac, computeMac, hmacScheme, ser]
  rw [← serializeContent_clampedProtoSignalCodec, aesCbcEncrypt_eq_cbcPkcs7,
    bytesToWordLE64_eq_bytesToWord64LE, hmacIds]

theorem aeadKEncExpr_cost :
    (aeadKEncExpr ℓ Pt C encT idOf).cost ≤ 12 * (ℓ / 32) + 1250 := by
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT PlainT)
  have hpk := pkLitExpr_cost ℓ Pt C encT (Γ := [argT]) dummyKey
  have hidA := idKeyLitExpr_cost ℓ Pt C encT (Γ := [argT]) (idOf .A)
  have hidB := idKeyLitExpr_cost ℓ Pt C encT (Γ := [argT]) (idOf .B)
  have hsalt := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [B 32, argT])
    (Expr.fst (Expr.snd (.var (.succ .zero))))
  simp only [Expr.cost] at hsalt
  simp only [aeadKEncExpr, opSym_cost, opPure_cost, opPtEncPk_cost,
    AtomicSymOp.cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat, hpk, hidA, hidB, hsalt]
  have hdiv16 : ℓ / 16 ≤ 2 * (ℓ / 32) + 1 := by omega
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  have hb8 : bits 8 ≤ 4 := by decide
  have hb32 : bits 32 ≤ 6 := by decide
  have hb96 : bits 96 ≤ 8 := by decide
  have hb128 : bits 128 ≤ 9 := by decide
  omega

def aeadKDecExpr :
    Expr O [.prod derivedMsgKeysT (.prod slotAdT wireSaltCtT)] (.opt PlainT) :=
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT wireSaltCtT)
  let Γ₀ : List (Ty S) := [argT]
  let Γ₁ : List (Ty S) := signalParsedT :: Γ₀
  let vArg : Expr O Γ₀ argT := .var .zero
  .caseOpt
    (opPure ℓ Pt C encT .signalMsgParse
      (opPure ℓ Pt C encT .bytesAppend8
        (.pair (Expr.fst (Expr.fst (Expr.snd (Expr.snd vArg))))
          (opPure ℓ Pt C encT (.bytesLit 8 (List.replicate 8 0#8)) .unit))))
    .none
    (let vP : Expr O Γ₁ signalParsedT := .var .zero
     let vArg1 : Expr O Γ₁ argT := .var (.succ .zero)
     let mk1 := Expr.fst vArg1
     let ad1 := Expr.fst (Expr.snd vArg1)
     let w1 := Expr.fst (Expr.snd (Expr.snd vArg1))
     let hdr1 := Expr.fst (Expr.snd ad1)
     let ids : Expr O Γ₁ (.prod IdKey IdKey) :=
       Expr.ite (.eqN (.modK 2 (Expr.fst hdr1)) (.nat 1))
         (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
         (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))
     let fullWire := opPure ℓ Pt C encT .bytesAppend8
       (.pair (Expr.fst w1) (opPure ℓ Pt C encT .u64LeBytes (Expr.snd w1)))
     let macOk := opSym ℓ Pt C encT .signalMsgVerifyMac
       (.pair fullWire (.pair (Expr.snd (Expr.snd (Expr.snd vP)))
         (.pair (Expr.fst ids) (.pair (Expr.snd ids) (Expr.snd mk1)))))
     let hdrOk := eqWireSignalHdrExpr ℓ Pt C encT
       (.pair (Expr.fst vP) (Expr.snd (Expr.snd vP)))
       (lHeaderExpr ℓ Pt C encT ad1)
     .ite (.and macOk hdrOk)
       (opSym ℓ Pt C encT .aes256CbcDec
         (.pair (Expr.fst (Expr.fst mk1)) (.pair (Expr.snd (Expr.fst mk1)) (Expr.fst (Expr.snd vP)))))
       .none)

theorem aeadKDecExpr_eval (mk : DerivedMessageKeys)
    (adV : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote)
    (cV : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) :
    (aeadKDecExpr ℓ Pt C encT idOf).eval (.cons (mk, (adV, cV)) .nil) =
      (let a := slotAdOfV adV
       (lAeadK C clampedProtoSignalCodec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2)
         (wireSaltCtOfV cV)) := by
  rcases mk with ⟨⟨ck, iv⟩, macKey⟩
  rcases adV with ⟨i, ⟨t, T?⟩, ⟨pn, pq, aSaltBv, addrs⟩⟩
  rcases cV with ⟨⟨ser, tag⟩, cSaltBv⟩
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT wireSaltCtT)
  let ρ₀ : Env [argT] :=
    .cons (((ck, iv), macKey), ((i, ((t, T?), (pn, (pq, (aSaltBv, addrs))))), ((ser, tag), cSaltBv))) .nil
  have happ_lit : (opPure ℓ Pt C encT .bytesAppend8
      (.pair (Expr.fst (Expr.fst (Expr.snd (Expr.snd (.var .zero)))))
        (opPure ℓ Pt C encT (.bytesLit 8 (List.replicate 8 0#8)) .unit))).eval ρ₀ =
      ser ++ List.replicate 8 0#8 := rfl
  have hparse := atomicPureOps_signalMsgParse_lossless ℓ Pt (ser ++ List.replicate 8 0#8)
  rw [lAeadK_clamped_dec_eq]
  change (aeadKDecExpr ℓ Pt C encT idOf).eval ρ₀ = _
  dsimp only [aeadKDecExpr]
  rw [Expr.eval, opPure_eval, happ_lit, hparse]
  rcases htf : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0#8) with err | m
  · have htf0 : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0) = .error err := htf
    dsimp only [Option.map, lAeadK, lWire, libsignalWireAead, libsignalReceiveWire,
      signalWireCodec, wireSaltCtOfV, macLength]
    simp only [htf0, ite_self]
    rfl
  · dsimp only [Option.map]
    let pVal : (signalParsedT (ℓ := ℓ) (Pt := Pt)).denote :=
      ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
       (m.ciphertext, (m.pqRatchet, m.addresses)))
    let ρ₁ : Env [signalParsedT, argT] := .cons pVal ρ₀
    have hids :
        (Expr.ite (.eqN (.modK 2 (Expr.fst (Expr.fst (Expr.snd (Expr.fst (Expr.snd (.var (.succ .zero)))))))) (.nat 1))
          (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
          (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))).eval ρ₁ =
        (if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)) := by
      by_cases ht : t % 2 = 1 <;> simp [ρ₁, ρ₀, Expr.eval, ht]
    have happTag : AtomicPureOp.bytesAppend8.eval ℓ Pt
        (ser, AtomicPureOp.u64LeBytes.eval ℓ Pt tag) = ser ++ toLEBytes 8 tag := by
      simp [AtomicPureOp.eval, List.take_of_length_le (Nat.le_of_eq (toLEBytes8_length tag))]
    have htfTag := tryFrom_append_sfx8 protoSignalCodec ser (toLEBytes 8 tag)
      (List.replicate 8 0#8) (toLEBytes8_length tag) (by simp [macLength])
    rw [htf] at htfTag; dsimp only [Except.map] at htfTag
    have hmacEq := verifyMacWithAddresses_append_tag C.F m ser tag idOf t macKey
    have hmacOk :
        (opSym ℓ Pt C encT .signalMsgVerifyMac
          (.pair (opPure ℓ Pt C encT .bytesAppend8
              (.pair (Expr.fst (Expr.fst (Expr.snd (Expr.snd (.var (.succ .zero))))))
                (opPure ℓ Pt C encT .u64LeBytes
                  (Expr.snd (Expr.fst (Expr.snd (Expr.snd (.var (.succ .zero)))))))))
            (.pair (Expr.snd (Expr.snd (Expr.snd (.var .zero))))
              (.pair (Expr.fst (Expr.ite (.eqN (.modK 2 (Expr.fst (Expr.fst (Expr.snd (Expr.fst (Expr.snd (.var (.succ .zero)))))))) (.nat 1))
                  (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
                  (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))))
                (.pair (Expr.snd (Expr.ite (.eqN (.modK 2 (Expr.fst (Expr.fst (Expr.snd (Expr.fst (Expr.snd (.var (.succ .zero)))))))) (.nat 1))
                    (.pair (idKeyLitExpr ℓ Pt C encT (idOf .A)) (idKeyLitExpr ℓ Pt C encT (idOf .B)))
                    (.pair (idKeyLitExpr ℓ Pt C encT (idOf .B)) (idKeyLitExpr ℓ Pt C encT (idOf .A)))))
                  (Expr.snd (Expr.fst (.var (.succ .zero))))))))).eval ρ₁ =
        ((hmacScheme C.F).tag macKey ((lIds idOf t).toList ++ ser) == tag) := by
      rw [opSym_eval]
      simp only [eval_pair, eval_fst, eval_snd]
      rw [hids, opPure_eval]
      simp only [eval_pair, eval_fst, eval_snd, opPure_eval]
      dsimp only [ρ₁, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ, AtomicSymOp.eval]
      rw [happTag, htfTag]; exact hmacEq
    have hhdrOk :
        (eqWireSignalHdrExpr ℓ Pt C encT
          (.pair (Expr.fst (.var .zero)) (Expr.snd (Expr.snd (.var .zero))))
          (lHeaderExpr ℓ Pt C encT (Expr.fst (Expr.snd (.var (.succ .zero)))))).eval ρ₁ =
        (m.header == lHeader encT i (t, T?) ⟨pn, pq, salt32OfV aSaltBv, addrs⟩) := by
      rw [eqWireSignalHdrExpr_eval, lHeaderExpr_eval]
      dsimp only [ρ₁, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ,
        wireSignalHdrOfV_wireSignalHdrV, slotAdOfV, fig8PubAdOfV, lpubOfV]
      rfl
    change (Expr.ite _ _ _).eval ρ₁ = _
    rw [Expr.eval, Expr.eval, hmacOk, hhdrOk]
    dsimp only [lAeadK, lWire, libsignalWireAead, libsignalReceiveWire,
      signalWireCodec, slotAdOfV, fig8PubAdOfV, lpubOfV, wireSaltCtOfV, macLength]
    have htf0 : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0) = .ok m := htf
    rw [htf0]
    cases hmacB : ((hmacScheme C.F).tag macKey ((lIds idOf t).toList ++ ser) == tag)
    · simp [Expr.eval]
    · dsimp only [Bool.true_and, ↓reduceIte, addressCheckPasses,
        ρ₁, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ,
        opSym_eval, AtomicSymOp.eval, aesCbcDecrypt]
      cases hdec : cbcDecRaw C.D ck iv m.ciphertext <;>
        by_cases hh : m.header = lHeader encT i (t, T?) ⟨pn, pq, salt32OfV aSaltBv, addrs⟩ <;>
        simp [hh]

theorem aeadKDecExpr_cost :
    (aeadKDecExpr ℓ Pt C encT idOf).cost ≤ 14 * (ℓ / 32) + 1250 := by
  let argT : Ty S := .prod derivedMsgKeysT (.prod slotAdT wireSaltCtT)
  have hidA := idKeyLitExpr_cost ℓ Pt C encT (Γ := [signalParsedT, argT]) (idOf .A)
  have hidB := idKeyLitExpr_cost ℓ Pt C encT (Γ := [signalParsedT, argT]) (idOf .B)
  have hlhdr := lHeaderExpr_cost ℓ Pt C encT (Γ := [signalParsedT, argT])
    (Expr.fst (Expr.snd (.var (.succ .zero))))
  have heqhdr := eqWireSignalHdrExpr_cost ℓ Pt C encT (Γ := [signalParsedT, argT])
    (.pair (Expr.fst (.var .zero)) (Expr.snd (Expr.snd (.var .zero))))
    (lHeaderExpr ℓ Pt C encT (Expr.fst (Expr.snd (.var (.succ .zero)))))
  simp only [Expr.cost] at hlhdr heqhdr
  simp only [aeadKDecExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost,
    Expr.cost, List.length_replicate, PNat.val_ofNat, hidA, hidB]
  have hdiv16 : ℓ / 16 ≤ 2 * (ℓ / 32) + 1 := by omega
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  omega

def aeadREncExpr :
    Expr O [.prod BV256 (.prod slotAdT PlainT)] wireSaltCtT :=
  let argT : Ty S := .prod BV256 (.prod slotAdT PlainT)
  let mksT : Ty S := .prod BV256 (.prod BV256 (.prod BV128 U32))
  let vArg : Expr O [argT] argT := .var .zero
  let mks := opSym ℓ Pt C encT .deriveMsgKeys
    (.pair (Expr.fst vArg)
      (.pair (opPure ℓ Pt C encT (.u32Lit 0#32) .unit)
        (.some (saltOfSlotAdExpr ℓ Pt C encT (Expr.fst (Expr.snd vArg))))))
  .letE mks
    (let vMks : Expr O [mksT, argT] mksT := .var .zero
     let vArg1 : Expr O [mksT, argT] argT := .var (.succ .zero)
     let mk := Expr.pair (.pair (Expr.fst vMks) (Expr.fst (Expr.snd (Expr.snd vMks))))
       (Expr.fst (Expr.snd vMks))
     .letE (.pair mk (Expr.snd vArg1))
       (exprWkTop1 ℓ Pt C encT (aeadKEncExpr ℓ Pt C encT idOf)))

theorem aeadREncExpr_eval (seed : BitVec 256)
    (adV : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote) (m : Plain ℓ) :
    (aeadREncExpr ℓ Pt C encT idOf).eval (.cons (seed, (adV, m)) .nil) =
      wireSaltCtV ((lAeadR C clampedProtoSignalCodec ℓ encT idOf).enc seed (slotAdOfV adV) m) := by
  dsimp only [aeadREncExpr, Expr.eval, env_get_zero, env_get_succ, opSym_eval, opPure_eval,
    AtomicSymOp.eval, AtomicPureOp.eval]
  rw [saltOfSlotAdExpr_eval, exprWkTop1_eval, aeadKEncExpr_eval]
  dsimp only [Expr.eval, env_get_zero, Option.map, MessageKeyGenerator.generateKeys, lAeadR, lAead]
  rw [show keyToBytesVec32 (salt32V (slotAdOfV adV).2.2.salt) = (slotAdOfV adV).2.2.salt from
    salt32OfV_salt32V _]

theorem aeadREncExpr_cost :
    (aeadREncExpr ℓ Pt C encT idOf).cost ≤ 12 * (ℓ / 32) + 1300 := by
  have hk := aeadKEncExpr_cost ℓ Pt C encT idOf
  have hsalt := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [.prod BV256 (.prod slotAdT PlainT)])
    (Expr.fst (Expr.snd (.var .zero)))
  simp only [Expr.cost] at hsalt
  simp only [aeadREncExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost,
    Expr.cost, exprWkTop1_cost, hsalt]
  omega

def aeadRDecExpr :
    Expr O [.prod BV256 (.prod slotAdT wireSaltCtT)] (.opt PlainT) :=
  let argT : Ty S := .prod BV256 (.prod slotAdT wireSaltCtT)
  let mksT : Ty S := .prod BV256 (.prod BV256 (.prod BV128 U32))
  let vArg : Expr O [argT] argT := .var .zero
  let aSalt := saltOfSlotAdExpr ℓ Pt C encT (Expr.fst (Expr.snd vArg))
  let cSalt := Expr.snd (Expr.snd (Expr.snd vArg))
  .ite (opPure ℓ Pt C encT .bv256Eq (.pair cSalt aSalt))
    (.letE
      (opSym ℓ Pt C encT .deriveMsgKeys
        (.pair (Expr.fst vArg)
          (.pair (opPure ℓ Pt C encT (.u32Lit 0#32) .unit) (.some aSalt))))
      (let vMks : Expr O [mksT, argT] mksT := .var .zero
       let vArg1 : Expr O [mksT, argT] argT := .var (.succ .zero)
       let mk := Expr.pair (.pair (Expr.fst vMks) (Expr.fst (Expr.snd (Expr.snd vMks))))
         (Expr.fst (Expr.snd vMks))
       .letE (.pair mk (Expr.snd vArg1))
         (exprWkTop1 ℓ Pt C encT (aeadKDecExpr ℓ Pt C encT idOf))))
    .none

theorem aeadRDecExpr_eval (seed : BitVec 256)
    (adV : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote)
    (cV : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) :
    (aeadRDecExpr ℓ Pt C encT idOf).eval (.cons (seed, (adV, cV)) .nil) =
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec seed (slotAdOfV adV)
        (wireSaltCtOfV cV) := by
  unfold aeadRDecExpr
  simp only [Expr.eval, env_get_zero, env_get_succ, opSym_eval, opPure_eval,
    AtomicSymOp.eval, AtomicPureOp.eval, saltOfSlotAdExpr_eval]
  by_cases hs : cV.2 = salt32V (slotAdOfV adV).2.2.salt
  · have hbeq : (cV.2 == salt32V (slotAdOfV adV).2.2.salt) = true := by simp [hs]
    have hsalt : (wireSaltCtOfV cV).2 = (slotAdOfV adV).2.2.salt := by
      dsimp only [wireSaltCtOfV]; rw [hs, salt32OfV_salt32V]
    rw [hbeq]
    simp only [↓reduceIte, exprWkTop1_eval, Option.map,
      MessageKeyGenerator.generateKeys, lAeadR, lAead, hsalt, ne_eq, not_true_eq_false]
    rw [show keyToBytesVec32 (salt32V (slotAdOfV adV).2.2.salt) = (slotAdOfV adV).2.2.salt from
      salt32OfV_salt32V _]
    exact aeadKDecExpr_eval ℓ Pt C encT idOf _ adV cV
  · have hbeq : (cV.2 == salt32V (slotAdOfV adV).2.2.salt) = false := beq_false_of_ne hs
    have hsalt : (wireSaltCtOfV cV).2 ≠ (slotAdOfV adV).2.2.salt := by
      intro heq; apply hs; rw [← heq]; exact (salt32V_salt32OfV cV.2).symm
    simp [hbeq, lAeadR, lAead, hsalt]

theorem aeadRDecExpr_cost :
    (aeadRDecExpr ℓ Pt C encT idOf).cost ≤ 14 * (ℓ / 32) + 1310 := by
  have hk := aeadKDecExpr_cost ℓ Pt C encT idOf
  have hsalt := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [.prod BV256 (.prod slotAdT wireSaltCtT)])
    (Expr.fst (Expr.snd (.var .zero)))
  simp only [Expr.cost] at hsalt
  simp only [aeadRDecExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost,
    Expr.cost, exprWkTop1_cost, hsalt]
  omega

end AeadMacros

section SamplerMacros

open Computational.Proofs.ReductionDsl.FsAtomicMacros (coinSimEquiv_liftP)

variable (ℓ : ℕ) (Pt : Type) (C : Crypto) (encT : Pt → PublicKey)

local notation "S" => atomicSig ℓ Pt
local notation "O" => atomicFsOps ℓ Pt C encT

def signalEncodeSerOnlyExpr : Expr O [.prod wireSignalHdrT (B 32)] (B 32) :=
  let argT : Ty S := .prod wireSignalHdrT (B 32)
  let hdr := Expr.fst (.var .zero : Expr O [argT] argT)
  let ctBody := Expr.snd (.var .zero : Expr O [argT] argT)
  let pq96 := opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 96) (Expr.fst (Expr.snd hdr)))
  let addrs128 : Expr O [argT] (.opt (B 32)) :=
    Expr.caseOpt (Expr.snd (Expr.snd hdr)) .none
      (.some (opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 128) (.var .zero))))
  let dId : IdentityKey := ⟨dummyKey⟩
  let full := opSym ℓ Pt C encT .signalMsgEncode
    (.pair (Expr.fst hdr) (.pair ctBody (.pair pq96 (.pair addrs128
      (.pair (idKeyLitExpr ℓ Pt C encT dId)
        (.pair (idKeyLitExpr ℓ Pt C encT dId) (opPure ℓ Pt C encT (.bv256Lit 0#256) .unit)))))))
  .letE full
    (opPure ℓ Pt C encT (.bytesTake 32)
      (.pair (.sub (opPure ℓ Pt C encT (.bytesLen 32) (.var .zero)) (.nat 8)) (.var .zero)))

theorem signalEncodeSerOnlyExpr_eval (h : SignalHeader) (ctBody : Bytes)
    (hct : ctBody.length ≤ 32 * (ℓ / 32 + 2)) :
    (signalEncodeSerOnlyExpr ℓ Pt C encT).eval (.cons (wireSignalHdrV h, ctBody) .nil) =
      (signalWireCodec clampedProtoSignalCodec).encode h ctBody := by
  rcases h with ⟨v, rk, ctr, pctr, pq, addrs⟩
  let argT : Ty S := .prod wireSignalHdrT (B 32)
  let ρ₀ : Env [argT] := .cons (((v, (rk, (ctr, pctr))), (pq, addrs)), ctBody) .nil
  have hpq : (pq.take 96).length ≤ 96 := List.length_take_le 96 pq
  have haddr : ∀ a ∈ addrs.map (·.take 128), a.length ≤ 128 := by
    cases addrs with
    | none => intro a ha; cases ha
    | some b =>
      intro a ha; simp only [Option.map_some, Option.mem_def, Option.some.injEq] at ha
      subst ha; exact List.length_take_le 128 b
  have had_ev :
      (Expr.caseOpt (Expr.snd (Expr.snd (Expr.fst (.var .zero)))) .none
        (.some (opPure ℓ Pt C encT (.bytesTake 32) (.pair (.nat 128) (.var .zero))))).eval ρ₀ =
      addrs.map (·.take 128) := by
    cases addrs <;> rfl
  change (signalEncodeSerOnlyExpr ℓ Pt C encT).eval ρ₀ = _
  dsimp only [signalEncodeSerOnlyExpr]
  rw [Expr.eval, opSym_eval]
  simp only [eval_pair, eval_fst, eval_snd]
  rw [had_ev, idKeyLitExpr_eval]
  dsimp only [ρ₀, Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval]
  rw [atomicSymOps_signalMsgEncode_lossless ℓ Pt C v rk ctr pctr ctBody (pq.take 96)
    (addrs.map (·.take 128)) ⟨dummyKey⟩ ⟨dummyKey⟩ 0#256 hct hpq haddr]
  dsimp only [SignalMessage.new, opPure_eval, Expr.eval, env_get_zero, AtomicPureOp.eval,
    signalWireCodec]
  rw [← serializeContent_clampedProtoSignalCodec v rk ctr pctr ctBody pq addrs]
  set ser := serializeContent clampedProtoSignalCodec v rk ctr pctr ctBody pq addrs
  set mac := computeMac C.F ⟨dummyKey⟩ ⟨dummyKey⟩ 0#256 ser
  have hmac_len : mac.length = 8 := computeMac_length C.F ⟨dummyKey⟩ ⟨dummyKey⟩ 0#256 ser
  have hsub : (ser ++ mac).length - 8 = ser.length := by rw [List.length_append, hmac_len]; omega
  rw [hsub, List.take_left]

theorem signalEncodeSerOnlyExpr_cost :
    (signalEncodeSerOnlyExpr ℓ Pt C encT).cost ≤ 4 * (ℓ / 32) + 850 := by
  let argT : Ty S := .prod wireSignalHdrT (B 32)
  have hid := idKeyLitExpr_cost ℓ Pt C encT (Γ := [argT]) ⟨dummyKey⟩
  have hb8 : bits 8 ≤ 4 := by decide
  have hb32 : bits 32 ≤ 6 := by decide
  have hb96 : bits 96 ≤ 8 := by decide
  have hb128 : bits 128 ≤ 9 := by decide
  simp only [signalEncodeSerOnlyExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost,
    Expr.cost, PNat.val_ofNat, hid]
  omega

private theorem liftP_pure {ι : Type} {T : OracleSpec.{0, 0} ι} (I : Iface S T) {α : Type} (x : α) :
    I.liftP (pure x) = pure x := by simp [Iface.liftP]

private theorem liftP_bind {ι : Type} {T : OracleSpec.{0, 0} ι} (I : Iface S T)
    {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    I.liftP (p >>= k) = (I.liftP p >>= fun x => I.liftP (k x)) := by simp [Iface.liftP]

private theorem liftP_map {ι : Type} {T : OracleSpec.{0, 0} ι} (I : Iface S T)
    {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by simp [Iface.liftP]

private theorem iterM_liftP {ι : Type} {T : OracleSpec.{0, 0} ι} (I : Iface S T)
    {α : Type} (f : α → ProbComp α) :
    ∀ (n : ℕ) (z : α), iterM (fun a => I.liftP (f a)) n z = I.liftP (iterM f n z)
  | 0, z => (liftP_pure ℓ Pt I z).symm
  | n + 1, z => by
    dsimp only [iterM]; rw [liftP_bind ℓ Pt I]; exact bind_congr fun a => iterM_liftP I f n a

private theorem flatMap_blockToBytesLE_len :
    ∀ l : List Block, (l.flatMap blockToBytesLE).length = 16 * l.length
  | [] => rfl
  | _ :: bs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, blockToBytesLE,
      List.length_ofFn, flatMap_blockToBytesLE_len bs]; omega

def sampleU64Comp {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    {Γ : List (Ty S)} : Comp O I Γ U64 :=
  .bind (sampU .bv128)
    (.ret (opPure ℓ Pt C encT .bytesToU64Le
      (opPure ℓ Pt C encT (.bytesTakeK 16 8)
        (opPure ℓ Pt C encT .bv128ToBytes16 (.var .zero)))))

def sampleMsgKeyComp {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    {Γ : List (Ty S)} : Comp O I Γ derivedMsgKeysT :=
  .bind (sampU .bv256) (.bind (sampU .bv128) (.bind (sampU .bv256)
    (.ret (.pair (.pair (.var (.succ (.succ .zero))) (.var (.succ .zero))) (.var .zero)))))

def sampleIdealComp {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort)) :
    Comp O I [slotAdT] wireSaltCtT :=
  let blocksC : Comp O I [slotAdT] (B 32) :=
    .iter (nBlocks ℓ) (opPure ℓ Pt C encT (.bytesLit 32 []) .unit)
      (.bind (sampU .bv128)
        (.ret (opPure ℓ Pt C encT .bytesAppend16
          (.pair (.var (.succ .zero)) (opPure ℓ Pt C encT .bv128ToBytes16 (.var .zero))))))
  .bind blocksC (.bind (sampleU64Comp ℓ Pt C encT sampU)
    (.ret
      (let a : Expr O [U64, B 32, slotAdT] slotAdT := .var (.succ (.succ .zero))
       let hdr := lHeaderExpr ℓ Pt C encT a
       let ser := .letE (.pair hdr (.var (.succ .zero)))
         (exprWkTop1 ℓ Pt C encT (signalEncodeSerOnlyExpr ℓ Pt C encT))
       .pair (.pair ser (.var .zero)) (saltOfSlotAdExpr ℓ Pt C encT a))))

theorem sampleU64Comp_coinSimEquiv {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif) (ρ : Env Γ),
      (sampU b).eval ρ = I.liftP ($ᵗ ((atomicSig ℓ Pt).den b.sort)))
    {Γ : List (Ty S)} (ρ : Env Γ) :
    CoinSimEquiv I.fwdU ((sampleU64Comp ℓ Pt C encT sampU).eval ρ)
      (I.liftP ($ᵗ (BitVec 64) : ProbComp (BitVec 64))) := by
  refine (CoinSimEquiv.of_eq ?_).trans (coinSimEquiv_liftP I sample_u64_of_bv128_evalDistEq)
  simp only [sampleU64Comp, Comp.eval, opPure_eval, Expr.eval,
    AtomicPureOp.eval, PNat.val_ofNat, hU, liftP_bind ℓ Pt I, liftP_pure ℓ Pt I]
  rfl

theorem sampleU64Comp_cost {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hc : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).cost ≤ 3)
    {Γ : List (Ty S)} :
    (sampleU64Comp ℓ Pt C encT sampU (Γ := Γ)).cost ≤ 60 := by
  have h1 := hc (Γ := Γ) .bv128
  simp only [sampleU64Comp, Comp.cost, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat]
  omega

theorem sampleU64Comp_queries {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hq : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).queries = 0)
    {Γ : List (Ty S)} :
    (sampleU64Comp ℓ Pt C encT sampU (Γ := Γ)).queries = 0 := by
  simp [sampleU64Comp, Comp.queries, hq]

theorem sampleMsgKeyComp_coinSimEquiv {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif) (ρ : Env Γ),
      (sampU b).eval ρ = I.liftP ($ᵗ ((atomicSig ℓ Pt).den b.sort)))
    {Γ : List (Ty S)} (ρ : Env Γ) :
    CoinSimEquiv I.fwdU ((sampleMsgKeyComp ℓ Pt C encT sampU).eval ρ)
      (I.liftP ($ᵗ DerivedMessageKeys : ProbComp DerivedMessageKeys)) := by
  have heq :
      (sampleMsgKeyComp ℓ Pt C encT sampU).eval ρ =
      I.liftP (do
        let ck ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let iv ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
        let mk ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        pure ((ck, iv), mk)) := by
    simp only [sampleMsgKeyComp, Comp.eval, Expr.eval, Env.get,
      hU, liftP_bind ℓ Pt I, liftP_pure ℓ Pt I]
    rfl
  rw [heq]
  exact coinSimEquiv_liftP I sample_derivedMsgKeys_evalDistEq

theorem sampleMsgKeyComp_cost {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hc : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).cost ≤ 3)
    {Γ : List (Ty S)} :
    (sampleMsgKeyComp ℓ Pt C encT sampU (Γ := Γ)).cost ≤ 20 := by
  have h1 := hc (Γ := Γ) .bv256
  have h2 := hc (Γ := .base AtomicBaseUnif.bv256.sort :: Γ) .bv128
  have h3 := hc (Γ := .base AtomicBaseUnif.bv128.sort :: .base AtomicBaseUnif.bv256.sort :: Γ) .bv256
  simp only [sampleMsgKeyComp, Comp.cost, Expr.cost]
  omega

theorem sampleMsgKeyComp_queries {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hq : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).queries = 0)
    {Γ : List (Ty S)} :
    (sampleMsgKeyComp ℓ Pt C encT sampU (Γ := Γ)).queries = 0 := by
  funext w ws
  have hq' : ∀ {Δ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Δ) b).queries w ws = 0 :=
    fun b => congrFun (congrFun (hq b) w) ws
  simp [sampleMsgKeyComp, Comp.queries, hq']

theorem sampleIdealComp_coinSimEquiv {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif) (ρ : Env Γ),
      (sampU b).eval ρ = I.liftP ($ᵗ ((atomicSig ℓ Pt).den b.sort)))
    (adV : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote) :
    CoinSimEquiv I.fwdU ((sampleIdealComp ℓ Pt C encT sampU).eval (.cons adV .nil))
      (wireSaltCtV <$> I.liftP (lIdeal C clampedProtoSignalCodec ℓ encT (slotAdOfV adV))) := by
  dsimp only [sampleIdealComp, Comp.eval]
  have hstep : ∀ acc : (B (ℓ := ℓ) (Pt := Pt) 32).denote,
      ((sampU .bv128).eval (Env.cons (t := B 32) acc (.cons adV .nil)) >>= fun b =>
        pure (AtomicPureOp.eval ℓ Pt .bytesAppend16 (acc, toLEBytes 16 b))) =
      I.liftP (do
        let b ← ($ᵗ Block : ProbComp Block)
        pure (acc ++ (toLEBytes 16 b).take 16)) := by
    intro acc
    rw [hU .bv128, liftP_bind ℓ Pt I]
    exact bind_congr fun b => (liftP_pure ℓ Pt I _).symm
  have hiter :
      iterM (fun acc : (B (ℓ := ℓ) (Pt := Pt) 32).denote =>
        (sampU .bv128).eval (Env.cons (t := B 32) acc (.cons adV .nil)) >>= fun b =>
          pure (AtomicPureOp.eval ℓ Pt .bytesAppend16 (acc, toLEBytes 16 b))) (nBlocks ℓ) [] =
      I.liftP (iterM (fun acc : Bytes => do
        let b ← ($ᵗ Block : ProbComp Block)
        pure (acc ++ (toLEBytes 16 b).take 16)) (nBlocks ℓ) []) := by
    simp only [hstep]
    exact iterM_liftP ℓ Pt I _ (nBlocks ℓ) []
  change CoinSimEquiv I.fwdU
    (iterM (fun acc : (B (ℓ := ℓ) (Pt := Pt) 32).denote =>
      (sampU .bv128).eval (Env.cons (t := B 32) acc (.cons adV .nil)) >>= fun b =>
        pure (AtomicPureOp.eval ℓ Pt .bytesAppend16 (acc, toLEBytes 16 b))) (nBlocks ℓ) [] >>=
      fun ctBody =>
        (sampleU64Comp ℓ Pt C encT sampU).eval (Env.cons (t := B 32) ctBody (.cons adV .nil)) >>=
          fun tag => _) _
  rw [hiter]
  have hblk := (coinSimEquiv_liftP I (sample_blocks_iter_evalDistEq (nBlocks ℓ) [])).trans
    (CoinSimEquiv.of_eq (liftP_map ℓ Pt I _ _))
  refine (hblk.bind fun ctBody =>
    (sampleU64Comp_coinSimEquiv ℓ Pt C encT sampU hU _).bind fun _ => CoinSimEquiv.refl _).trans ?_
  rw [bind_map_left]
  have hrhs :
      (wireSaltCtV (ℓ := ℓ) (Pt := Pt) <$>
        I.liftP (lIdeal C clampedProtoSignalCodec ℓ encT (slotAdOfV adV))) =
      (I.liftP ($ᵗ (List.Vector Block (nBlocks ℓ))) >>= fun v =>
        I.liftP ($ᵗ (BitVec 64)) >>= fun tag =>
          pure (wireSaltCtV (ℓ := ℓ) (Pt := Pt)
            ((wireEncode (signalWireCodec clampedProtoSignalCodec)
                (lHeader encT (slotAdOfV adV).1 (slotAdOfV adV).2.1 (slotAdOfV adV).2.2) v,
              tag), (slotAdOfV adV).2.2.salt))) := by
    dsimp only [lIdeal, lWire, libsignalWireAead, WireAEAD.idealEnc, liftM, monadLift,
      MonadLift.monadLift]
    simp only [liftP_bind ℓ Pt I, liftP_pure ℓ Pt I, map_bind, map_pure, bind_assoc, pure_bind]
  rw [hrhs]
  refine (CoinSimEquiv.refl _).bind fun v => (CoinSimEquiv.refl _).bind fun tag => ?_
  apply CoinSimEquiv.of_eq
  have hct : (v.toList.flatMap blockToBytesLE).length ≤ 32 * (ℓ / 32 + 2) := by
    rw [flatMap_blockToBytesLE_len, v.toList_length, nBlocks]; omega
  dsimp only [List.nil_append, Expr.eval]
  rw [exprWkTop1_eval, lHeaderExpr_eval, saltOfSlotAdExpr_eval]
  dsimp only [Expr.eval, env_get_zero, env_get_succ]
  rw [signalEncodeSerOnlyExpr_eval ℓ Pt C encT _ _ hct]
  rfl

theorem sampleIdealComp_cost {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hc : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).cost ≤ 3) :
    (sampleIdealComp ℓ Pt C encT sampU).cost ≤ 70 * (ℓ / 32) + 1300 := by
  have hb := hc (Γ := [B 32, slotAdT]) .bv128
  have hu := sampleU64Comp_cost ℓ Pt C encT sampU hc (Γ := [B 32, slotAdT])
  have hhdr := lHeaderExpr_cost ℓ Pt C encT (Γ := [U64, B 32, slotAdT]) (.var (.succ (.succ .zero)))
  have hser := signalEncodeSerOnlyExpr_cost ℓ Pt C encT
  have hsalt := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [U64, B 32, slotAdT])
    (.var (.succ (.succ .zero)))
  have hnb : nBlocks ℓ ≤ 2 * (ℓ / 32) + 2 := by unfold nBlocks; omega
  simp only [Expr.cost] at hhdr hsalt
  simp only [sampleIdealComp, Comp.cost, opPure_cost, AtomicPureOp.cost, Expr.cost,
    exprWkTop1_cost, List.length_nil, PNat.val_ofNat]
  nlinarith

theorem sampleIdealComp_queries {ι : Type} {T : OracleSpec.{0, 0} ι} {I : Iface S T}
    (sampU : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), Comp O I Γ (.base b.sort))
    (hq : ∀ {Γ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).queries = 0) :
    (sampleIdealComp ℓ Pt C encT sampU).queries = 0 := by
  funext w ws
  have hq' : ∀ {Δ : List (Ty S)} (b : AtomicBaseUnif), (sampU (Γ := Δ) b).queries w ws = 0 :=
    fun b => congrFun (congrFun (hq b) w) ws
  have hu := congrFun (congrFun (sampleU64Comp_queries ℓ Pt C encT sampU hq (Γ := [B 32, slotAdT])) w) ws
  simp [sampleIdealComp, Comp.queries, hq', hu]

end SamplerMacros

end Computational.Proofs.ReductionDsl.FsAtomicOps
