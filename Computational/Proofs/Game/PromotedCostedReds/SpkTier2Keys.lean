/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSpkModel
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.TablesHonest

/-!
# Tier-2 Key Encoders

Injective `.nat` table-key encoders for curve points (`ptKeyE`) and bounded wire messages
(`wireKeyE`, `spkWireKeyE`) over `ReductionDsl.atomicSessionOps`.
-/

public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift (cost_tier2PtEncOp cost_tier2PureOp
  eval_tier2PtEncOp eval_tier2PureOp tier2PtEncOp tier2PureOp)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.E2E (Bytes)
open ReductionDsl (AtomicPureOp B Env Expr PtT Ty atomicSessionOps atomicSig bits bytesToWordLE)

namespace Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys

/-- Maximum byte length of any honest Double Ratchet + SPQR wire message. -/
@[expose] def spkMaxWireLen (ℓ : ℕ) : ℕ :=
  32 * (ℓ / 32) + 450

@[expose] def spkWireChunks (ℓ : ℕ) : ℕ :=
  4 * (ℓ / 32) + 57

theorem spkMaxWireLen_le_eight_mul_chunks (ℓ : ℕ) :
    spkMaxWireLen ℓ ≤ 8 * spkWireChunks ℓ := by
  unfold spkMaxWireLen spkWireChunks; omega

theorem spkMaxWireLen_lt_two_pow_64 {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) :
    spkMaxWireLen ℓ < 2 ^ 64 := by
  unfold spkMaxWireLen; omega

/-! ## Little-endian 64-bit limb packing -/

@[expose] def chunk64Nat (bs : Bytes) (off : ℕ) : ℕ :=
  (bytesToWordLE 64 ((bs.drop off).take 8)).toNat

theorem chunk64Nat_lt (bs : Bytes) (off : ℕ) : chunk64Nat bs off < 2 ^ 64 :=
  (bytesToWordLE 64 ((bs.drop off).take 8)).isLt

@[expose] def packChunks (bs : Bytes) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, off => chunk64Nat bs off + 2 ^ 64 * packChunks bs k (off + 8)

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

private theorem extractLsb'_bytesToWordLE64 (bs : Bytes) (j : ℕ)
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

private theorem chunk64Nat_eq_at {bs₁ bs₂ : Bytes} :
    ∀ {k off q : ℕ}, q < k → packChunks bs₁ k off = packChunks bs₂ k off →
      chunk64Nat bs₁ (off + 8 * q) = chunk64Nat bs₂ (off + 8 * q)
  | 0, _, _, hq, _ => absurd hq (Nat.not_lt_zero _)
  | k + 1, off, 0, _, hp => by
    simp only [packChunks] at hp
    have h1 := chunk64Nat_lt bs₁ off
    have h2 := chunk64Nat_lt bs₂ off
    have : off + 8 * 0 = off := by omega
    rw [this]; omega
  | k + 1, off, q + 1, hq, hp => by
    simp only [packChunks] at hp
    have h1 := chunk64Nat_lt bs₁ off
    have h2 := chunk64Nat_lt bs₂ off
    have hrest : packChunks bs₁ k (off + 8) = packChunks bs₂ k (off + 8) := by omega
    have ih := chunk64Nat_eq_at (bs₁ := bs₁) (bs₂ := bs₂) (k := k) (off := off + 8) (q := q)
      (by omega) hrest
    have heq : (off + 8) + 8 * q = off + 8 * (q + 1) := by omega
    rwa [heq] at ih

theorem eq_of_length_eq_of_packChunks_eq {bs₁ bs₂ : Bytes} {K : ℕ}
    (hlen : bs₁.length = bs₂.length) (hK : bs₁.length ≤ 8 * K)
    (hp : packChunks bs₁ K 0 = packChunks bs₂ K 0) : bs₁ = bs₂ := by
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have hq : i / 8 < K := by omega
  have hr : i % 8 < 8 := by omega
  have hch := chunk64Nat_eq_at (bs₁ := bs₁) (bs₂ := bs₂) (off := 0) hq hp
  simp only [Nat.zero_add, chunk64Nat] at hch
  have hbv : bytesToWordLE 64 ((bs₁.drop (8 * (i / 8))).take 8) =
      bytesToWordLE 64 ((bs₂.drop (8 * (i / 8))).take 8) := BitVec.eq_of_toNat_eq hch
  have hs1 : i % 8 < ((bs₁.drop (8 * (i / 8))).take 8).length := by simp; omega
  have hs2 : i % 8 < ((bs₂.drop (8 * (i / 8))).take 8).length := by simp; omega
  have e1 := extractLsb'_bytesToWordLE64 ((bs₁.drop (8 * (i / 8))).take 8) (i % 8) hs1 hr
  have e2 := extractLsb'_bytesToWordLE64 ((bs₂.drop (8 * (i / 8))).take 8) (i % 8) hs2 hr
  rw [hbv] at e1
  have hget := e1.symm.trans e2
  simp only [List.getElem_take, List.getElem_drop] at hget
  have hidx : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  simpa [hidx] using hget

/-! ## Pure key encoders -/

/-- Pure `Pt → ℕ` key encoding packing the 33-byte serialized public key in 5 limbs. -/
@[expose] def ptKeyVal {Pt : Type} (encT : Pt → PublicKey) (Q : Pt) : ℕ :=
  packChunks (encT Q).serialize 5 0

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem publicKey_serialize_injective : Function.Injective PublicKey.serialize := by
  intro ⟨a⟩ ⟨b⟩ h
  simp only [PublicKey.serialize, List.cons.injEq, true_and] at h
  exact congrArg PublicKey.mk (List.Vector.eq a b h)

theorem ptKeyVal_injective {Pt : Type} {encT : Pt → PublicKey} (hinj : Function.Injective encT) :
    Function.Injective (ptKeyVal encT) := by
  intro Q₁ Q₂ h
  apply hinj
  apply publicKey_serialize_injective
  exact eq_of_length_eq_of_packChunks_eq (K := 5)
    (by simp [publicKey_serialize_length])
    (by simp [publicKey_serialize_length])
    h

theorem ptKeyVal_injective_of_dec {Pt : Type} {encT : Pt → PublicKey}
    {decT : PublicKey → Option Pt} (hdec : ∀ T, decT (encT T) = some T) :
    Function.Injective (ptKeyVal encT) := by
  refine ptKeyVal_injective fun Q₁ Q₂ h => ?_
  have h1 := hdec Q₁
  rw [h, hdec Q₂] at h1
  exact Option.some.inj h1.symm

/-- Pure bounded-wire key encoding returning `none` when `W < c.length`. -/
@[expose] def wireKeyVal (W n : ℕ) (c : Bytes) : Option ℕ :=
  if c.length ≤ W then some (c.length + 2 ^ 64 * packChunks c n 0) else none

theorem wireKeyVal_eq_some_of_le {W n : ℕ} {c : Bytes} (hc : c.length ≤ W) :
    wireKeyVal W n c = some (c.length + 2 ^ 64 * packChunks c n 0) := by
  simp [wireKeyVal, hc]

theorem wireKeyVal_eq_none_of_gt {W n : ℕ} {c : Bytes} (hc : W < c.length) :
    wireKeyVal W n c = none := by
  have h : ¬ c.length ≤ W := by omega
  simp [wireKeyVal, h]

theorem wireKeyVal_injective {W n : ℕ} (hWn : W ≤ 8 * n) (hW64 : W < 2 ^ 64)
    {c₁ c₂ : Bytes} {k : ℕ}
    (h1 : wireKeyVal W n c₁ = some k) (h2 : wireKeyVal W n c₂ = some k) :
    c₁ = c₂ := by
  unfold wireKeyVal at h1 h2
  split at h1
  case isFalse => simp at h1
  case isTrue hc1 =>
    split at h2
    case isFalse => simp at h2
    case isTrue hc2 =>
      simp only [Option.some.injEq] at h1 h2
      have heq : c₁.length + 2 ^ 64 * packChunks c₁ n 0 =
          c₂.length + 2 ^ 64 * packChunks c₂ n 0 := h1.trans h2.symm
      have hlen : c₁.length = c₂.length := by omega
      have hp : packChunks c₁ n 0 = packChunks c₂ n 0 := by omega
      exact eq_of_length_eq_of_packChunks_eq hlen (by omega) hp

abbrev spkWireKeyVal (ℓ : ℕ) : Bytes → Option ℕ :=
  wireKeyVal (spkMaxWireLen ℓ) (spkWireChunks ℓ)

theorem spkWireKeyVal_injective {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) {c₁ c₂ : Bytes} {k : ℕ}
    (h1 : spkWireKeyVal ℓ c₁ = some k) (h2 : spkWireKeyVal ℓ c₂ = some k) : c₁ = c₂ :=
  wireKeyVal_injective (spkMaxWireLen_le_eight_mul_chunks ℓ) (spkMaxWireLen_lt_two_pow_64 hℓ) h1 h2

/-! ## DSL key-encoder expressions -/

section DslEncoders

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def chunk64NatE {Γ : List (Ty ASig)} (w : ℕ+) (off : ℕ) (bsE : Expr AOps Γ (B w)) :
    Expr AOps Γ .nat :=
  tier2PureOp .u64ToNat
    (tier2PureOp .bytesToU64Le
      (tier2PureOp (.bytesTakeK w 8)
        (tier2PureOp (.bytesDrop w) (.pair (.nat off) bsE))))

@[simp] theorem eval_chunk64NatE {Γ : List (Ty ASig)} (w : ℕ+) (off : ℕ)
    (bsE : Expr AOps Γ (B w)) (ρ : Env Γ) :
    (chunk64NatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) w off bsE).eval ρ = chunk64Nat (bsE.eval ρ) off := rfl

theorem cost_chunk64NatE {Γ : List (Ty ASig)} (w : ℕ+) (off : ℕ)
    (bsE : Expr AOps Γ (B w)) :
    (chunk64NatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) w off bsE).cost =
      bsE.cost + bits off + 2 * (w : ℕ) + 82 := by
  dsimp only [chunk64NatE]
  rw [cost_tier2PureOp, cost_tier2PureOp, cost_tier2PureOp, cost_tier2PureOp]
  simp only [AtomicPureOp.cost, ReductionDsl.Expr.cost, PNat.val_ofNat]
  omega

@[expose] def packChunksVar0E {Γ : List (Ty ASig)} (w : ℕ+) : ℕ → ℕ → Expr AOps (B w :: Γ) .nat
  | 0, _ => .nat 0
  | n + 1, off =>
    .add (chunk64NatE w off .v0) (.mulK (2 ^ 64) (packChunksVar0E w n (off + 8)))

@[simp] theorem eval_packChunksVar0E {Γ : List (Ty ASig)} (w : ℕ+) (bs : Bytes) (ρ : Env Γ) :
    ∀ (n off : ℕ),
      (packChunksVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) w n off).eval (.cons bs ρ) = packChunks bs n off
  | 0, _ => rfl
  | n + 1, off => by
    simp only [packChunksVar0E, ReductionDsl.Expr.eval, eval_chunk64NatE, ReductionDsl.Expr.v0,
      ReductionDsl.Env.get, eval_packChunksVar0E w bs ρ n (off + 8), packChunks]

theorem cost_packChunksVar0E {Γ : List (Ty ASig)} (w : ℕ+) :
    ∀ (n off : ℕ),
      (packChunksVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ) w n off).cost ≤
        n * (bits (off + 8 * n) + 2 * (w : ℕ) + 150) + 1
  | 0, _ => by
    have h0 : bits 0 = 1 := by decide
    simp [packChunksVar0E, ReductionDsl.Expr.cost, h0]
  | n + 1, off => by
    have ih := cost_packChunksVar0E (Γ := Γ) w n (off + 8)
    have hch := cost_chunk64NatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) w off (.v0 : Expr AOps (B w :: Γ) (B w))
    have hbits_mono : bits off ≤ bits (off + 8 * (n + 1)) :=
      ReductionDsl.bits_mono (by omega)
    have h64 : bits (2 ^ 64) ≤ 65 := by decide
    have heq : (off + 8) + 8 * n = off + 8 * (n + 1) := by omega
    rw [heq] at ih
    dsimp only [packChunksVar0E, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0] at hch ⊢
    calc
      (chunk64NatE w off (.var .zero)).cost +
          ((packChunksVar0E w n (off + 8)).cost + bits (2 ^ 64)) + 1
        ≤ (1 + bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 82) +
          ((n * (bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 150) + 1) + 65) + 1 := by omega
      _ ≤ (n + 1) * (bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 150) + 1 := by
        have : (n + 1) * (bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 150) + 1 =
            n * (bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 150) +
              (bits (off + 8 * (n + 1)) + 2 * (w : ℕ) + 150) + 1 := by ring
        omega

/-- DSL expression computing `ptKeyVal encT` over `atomicSessionOps`. -/
@[expose] def ptKeyE {Γ : List (Ty ASig)} (qE : Expr AOps Γ PtT) : Expr AOps Γ .nat :=
  .letE (tier2PureOp .pkSerialize (tier2PtEncOp .ptEncPk qE))
    (packChunksVar0E 33 5 0)

@[simp] theorem eval_ptKeyE {Γ : List (Ty ASig)} (qE : Expr AOps Γ PtT) (ρ : Env Γ) :
    (ptKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qE).eval ρ = ptKeyVal encT (qE.eval ρ) := by
  change (packChunksVar0E 33 5 0).eval (.cons (encT (qE.eval ρ)).serialize ρ) =
    ptKeyVal encT (qE.eval ρ)
  exact eval_packChunksVar0E 33 (encT (qE.eval ρ)).serialize ρ 5 0

theorem cost_ptKeyE {Γ : List (Ty ASig)} (qE : Expr AOps Γ PtT) :
    (ptKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qE).cost ≤ qE.cost + 1160 := by
  have hp := cost_packChunksVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ) 33 5 0
  have hb40 : bits (0 + 8 * 5) ≤ 6 := by decide
  simp only [PNat.val_ofNat] at hp
  change qE.cost + 4 + 33 + (packChunksVar0E 33 5 0).cost + 1 ≤ qE.cost + 1160
  omega

@[expose] def unitListPow2E {Γ : List (Ty ASig)} : ℕ → Expr AOps Γ (.list .unit)
  | 0 => .cons .unit .nil
  | d + 1 => .letE (unitListPow2E d) (.appendL (2 ^ (d + 1)) .v0 .v0)

@[simp] theorem eval_unitListPow2E {Γ : List (Ty ASig)} (ρ : Env Γ) :
    ∀ d : ℕ,
      (unitListPow2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) d).eval ρ = List.replicate (2 ^ d) ()
  | 0 => rfl
  | d + 1 => by
    simp only [unitListPow2E, ReductionDsl.Expr.eval, eval_unitListPow2E ρ d,
      ReductionDsl.Expr.v0, ReductionDsl.Env.get, ← List.replicate_add]
    have hpow : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by ring
    rw [hpow, List.take_of_length_le (by simp)]

theorem cost_unitListPow2E {Γ : List (Ty ASig)} :
    ∀ d : ℕ,
      (unitListPow2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ) d).cost ≤ 2 * 2 ^ d + 4 * d + 3
  | 0 => by simp [unitListPow2E, ReductionDsl.Expr.cost]
  | d + 1 => by
    have ih := cost_unitListPow2E (Γ := Γ) d
    dsimp only [unitListPow2E, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0]
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    omega

theorem size_unitListPow2E {Γ : List (Ty ASig)} :
    ∀ d : ℕ,
      (unitListPow2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ) d).size ≤ d * (bits (2 ^ d) + 6) + 3
  | 0 => by simp [unitListPow2E, ReductionDsl.Expr.size]
  | d + 1 => by
    have ih := size_unitListPow2E (Γ := Γ) d
    have hb_mono : bits (2 ^ d) ≤ bits (2 ^ (d + 1)) :=
      ReductionDsl.bits_mono (Nat.pow_le_pow_right (by decide) (Nat.le_succ d))
    have hmul : d * (bits (2 ^ d) + 6) ≤ d * (bits (2 ^ (d + 1)) + 6) :=
      Nat.mul_le_mul_left d (by omega)
    dsimp only [unitListPow2E, ReductionDsl.Expr.size, ReductionDsl.Expr.v0]
    have hstep : (d + 1) * (bits (2 ^ (d + 1)) + 6) =
        d * (bits (2 ^ (d + 1)) + 6) + bits (2 ^ (d + 1)) + 6 := by ring
    omega

@[expose] def packFoldBodyE {Γ : List (Ty ASig)} :
    Expr AOps (.unit :: .prod .nat .nat :: B 32 :: Γ) (.prod .nat .nat) :=
  .letE (.sub (.snd .v1) (.nat 8))
    (.pair
      (.add
        (tier2PureOp .u64ToNat
          (tier2PureOp .bytesToU64Le
            (tier2PureOp (.bytesTakeK 32 8)
              (tier2PureOp (.bytesDrop 32) (.pair .v0 .v3)))))
        (.mulK (2 ^ 64) (.fst .v2)))
      .v0)

theorem cost_packFoldBodyE {Γ : List (Ty ASig)} :
    (packFoldBodyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ)).cost = 226 := by
  dsimp only [packFoldBodyE, tier2PureOp, ReductionDsl.Expr.cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3,
    ReductionDsl.atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps,
    ReductionDsl.atomicPureOps, ReductionDsl.Ops.sum, Sum.elim, AtomicPureOp.cost]
  decide

theorem size_packFoldBodyE {Γ : List (Ty ASig)} :
    (packFoldBodyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ)).size ≤ 90 := by
  dsimp only [packFoldBodyE, tier2PureOp, ReductionDsl.Expr.size, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3,
    ReductionDsl.atomicSessionOps, ReductionDsl.atomicFig8Ops, ReductionDsl.atomicFsOps,
    ReductionDsl.atomicPureOps, ReductionDsl.Ops.sum, Sum.elim, AtomicPureOp.opSize]
  decide

private theorem foldr_replicate_packStep (bs : Bytes) :
    ∀ (m off : ℕ),
      (List.replicate m ()).foldr
        (fun _ (p : ℕ × ℕ) => (chunk64Nat bs (p.2 - 8) + 2 ^ 64 * p.1, p.2 - 8))
        (0, off + 8 * m) = (packChunks bs m off, off)
  | 0, off => by simp [packChunks]
  | m + 1, off => by
    have heq : off + 8 * (m + 1) = (off + 8) + 8 * m := by omega
    rw [List.replicate_succ, List.foldr_cons, heq, foldr_replicate_packStep bs m (off + 8)]
    have hsub : (off + 8) - 8 = off := by omega
    simp [hsub, packChunks]

@[expose] def packChunksFoldVar0E {Γ : List (Ty ASig)} : ℕ → Expr AOps (B 32 :: Γ) .nat
  | 0 => .nat 0
  | m + 1 =>
    .fst (.foldrB (m + 1)
      (.take (.nat (m + 1)) (unitListPow2E (bits (m + 1))))
      (.pair (.nat 0) (.nat (8 * (m + 1))))
      packFoldBodyE)

@[simp] theorem eval_packChunksFoldVar0E {Γ : List (Ty ASig)} (bs : Bytes) (ρ : Env Γ) :
    ∀ n : ℕ,
      (packChunksFoldVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) n).eval (.cons bs ρ) = packChunks bs n 0
  | 0 => rfl
  | m + 1 => by
    have hpow : m + 1 ≤ 2 ^ bits (m + 1) := by
      unfold bits
      exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) (m + 1))
    simp only [packChunksFoldVar0E, ReductionDsl.Expr.eval, eval_unitListPow2E,
      List.take_replicate, Nat.min_eq_left hpow, Nat.min_self]
    have hbody : ∀ (x : Unit) (acc : ℕ × ℕ),
        (packFoldBodyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam)).eval (.cons x (.cons acc (.cons bs ρ))) =
          (chunk64Nat bs (acc.2 - 8) + 2 ^ 64 * acc.1, acc.2 - 8) := fun _ _ => rfl
    simp only [hbody]
    have hf := foldr_replicate_packStep bs (m + 1) 0
    simp only [Nat.zero_add] at hf
    simp only [hf]

theorem cost_packChunksFoldVar0E {Γ : List (Ty ASig)} :
    ∀ n : ℕ,
      (packChunksFoldVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := Γ) n).cost ≤
        231 * n + 5 * bits n + bits (8 * n) + 8
  | 0 => by
    have h0 : bits 0 = 1 := by decide
    simp [packChunksFoldVar0E, ReductionDsl.Expr.cost, h0]
  | m + 1 => by
    have hul := cost_unitListPow2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := B 32 :: Γ) (bits (m + 1))
    have hpow : 2 ^ bits (m + 1) ≤ 2 * (m + 1) := by
      unfold bits
      rw [Nat.pow_succ]
      have hlog : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
      omega
    have hb := cost_packFoldBodyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ)
    have h0 : bits 0 = 1 := by decide
    dsimp only [packChunksFoldVar0E, ReductionDsl.Expr.cost]
    rw [hb, h0]
    omega

/-- DSL expression computing `wireKeyVal W n` in logarithmic AST size via `foldrB`. -/
@[expose] def wireKeyE {Γ : List (Ty ASig)} (W n : ℕ) (cE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt .nat) :=
  .letE cE
    (.letE (tier2PureOp (.bytesLen 32) .v0)
      (.ite (.lt (.nat W) .v0)
        .none
        (.some (.add .v0 (.mulK (2 ^ 64)
          (.letE (.var (.succ .zero)) (packChunksFoldVar0E n)))))))

@[simp] theorem eval_wireKeyE {Γ : List (Ty ASig)} (W n : ℕ) (cE : Expr AOps Γ (B 32))
    (ρ : Env Γ) :
    (wireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) W n cE).eval ρ = wireKeyVal W n (cE.eval ρ) := by
  let ρ1 : Env (B 32 :: Γ) := .cons (cE.eval ρ) ρ
  let ρ2 : Env (.nat :: B 32 :: Γ) := .cons (cE.eval ρ).length ρ1
  let ρ3 : Env (B 32 :: .nat :: B 32 :: Γ) := .cons (cE.eval ρ) ρ2
  change (if decide (W < (cE.eval ρ).length) = true then none
    else some ((cE.eval ρ).length + 2 ^ 64 * (packChunksFoldVar0E n).eval ρ3)) =
    wireKeyVal W n (cE.eval ρ)
  unfold wireKeyVal
  by_cases hgt : W < (cE.eval ρ).length
  · have hnle : ¬ (cE.eval ρ).length ≤ W := by omega
    simp [hgt, hnle]
  · have hle : (cE.eval ρ).length ≤ W := by omega
    simp [hgt, hle, ρ3, eval_packChunksFoldVar0E]

theorem cost_wireKeyE {Γ : List (Ty ASig)} (W n : ℕ) (cE : Expr AOps Γ (B 32)) :
    (wireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) W n cE).cost ≤
      cE.cost + bits W + 231 * n + 5 * bits n + bits (8 * n) + 95 := by
  have hp := cost_packChunksFoldVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .nat :: B 32 :: Γ) n
  have hb32 : bits (32 : ℕ) ≤ 6 := by decide
  have hb64 : bits (2 ^ 64) ≤ 65 := by decide
  change cE.cost +
      ((1 + (bits (32 : ℕ) + 1)) +
        ((bits W + 1 + 1) +
          max 1 (1 + ((1 + (packChunksFoldVar0E n).cost + 1) + bits (2 ^ 64)) + 1 + 1) + 1) + 1) +
      1 ≤ cE.cost + bits W + 231 * n + 5 * bits n + bits (8 * n) + 95
  omega

@[expose] def spkWireKeyE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  wireKeyE (spkMaxWireLen ℓ) (spkWireChunks ℓ) cE

@[simp] theorem eval_spkWireKeyE {Γ : List (Ty ASig)} (cE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ = spkWireKeyVal ℓ (cE.eval ρ) :=
  eval_wireKeyE _ _ cE ρ

theorem cost_spkWireKeyE_of_lt {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (cE : Expr AOps Γ (B 32)) :
    (spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + 30 * ℓ + 14000 := by
  have hc := cost_wireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (spkMaxWireLen ℓ) (spkWireChunks ℓ) cE
  have hbW : bits (spkMaxWireLen ℓ) ≤ 21 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 20) ?_) (by decide)
    unfold spkMaxWireLen; omega
  have hbn : bits (spkWireChunks ℓ) ≤ 21 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 20) ?_) (by decide)
    unfold spkWireChunks; omega
  have hb8n : bits (8 * spkWireChunks ℓ) ≤ 21 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 20) ?_) (by decide)
    unfold spkWireChunks; omega
  dsimp only [spkWireKeyE]
  have h231 : 231 * spkWireChunks ℓ = 924 * (ℓ / 32) + 13167 := by
    unfold spkWireChunks; ring
  omega

theorem size_spkWireKeyE_of_lt {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (cE : Expr AOps Γ (B 32)) :
    (spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).size ≤ cE.size + 800 := by
  have hbW : bits (spkMaxWireLen ℓ) ≤ 21 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 20) ?_) (by decide)
    unfold spkMaxWireLen; omega
  have hbn : bits (spkWireChunks ℓ) ≤ 18 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 17 - 1) ?_) (by decide)
    unfold spkWireChunks; omega
  have hb8n : bits (8 * spkWireChunks ℓ) ≤ 21 := by
    refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 20) ?_) (by decide)
    unfold spkWireChunks; omega
  have hb64 : bits (2 ^ 64) ≤ 65 := by decide
  have hb0 : bits 0 = 1 := by decide
  dsimp only [spkWireKeyE, wireKeyE]
  cases hn : spkWireChunks ℓ with
  | zero =>
    unfold spkWireChunks at hn; omega
  | succ m =>
    rw [← hn]
    have hul := size_unitListPow2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := B 32 :: .nat :: B 32 :: Γ) (bits (spkWireChunks ℓ))
    have hb_pow : bits (2 ^ bits (spkWireChunks ℓ)) ≤ 19 := by
      refine le_trans (ReductionDsl.bits_mono (b := 2 ^ 18) ?_) (by decide)
      exact Nat.pow_le_pow_right (by decide) hbn
    have hmul : bits (spkWireChunks ℓ) * (bits (2 ^ bits (spkWireChunks ℓ)) + 6) ≤ 18 * 25 :=
      Nat.mul_le_mul hbn (by omega)
    have hbody := size_packFoldBodyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := .nat :: B 32 :: Γ)
    have hlen_sz : (tier2PureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.bytesLen 32)
        (.v0 : Expr AOps (B 32 :: Γ) (B 32))).size = 2 := rfl
    have hp_sz : (packChunksFoldVar0E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (Γ := .nat :: B 32 :: Γ) (spkWireChunks ℓ)).size ≤ 620 := by
      rw [hn]
      dsimp only [packChunksFoldVar0E, ReductionDsl.Expr.size]
      rw [← hn]
      omega
    dsimp only [ReductionDsl.Expr.size, ReductionDsl.Expr.v0] at hlen_sz ⊢
    omega

end DslEncoders

end Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
