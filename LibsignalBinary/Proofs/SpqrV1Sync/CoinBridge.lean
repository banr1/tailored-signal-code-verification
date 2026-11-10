/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncParty
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.FinEnum
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec

/-!
# Uniform Coin Bijections for `spqrV1SessionUniformCoins`

`spqrV1SessionUniformCoins F K` samples `r : BitVec 512` and passes the 64-byte little-endian tape
`coinBytes r = toLEBytes 64 r` to `send`:
* In `.keysUnsampled`, `nextCoins` consumes all 64 bytes as the ML-KEM keygen seed via the
  bijection `coinEquiv : BitVec 512 ≃ Seed`.
* In `.headerReceived`, `nextCoins` consumes the first 32 bytes as encapsulation randomness
  `encRandOf r = encRandEquiv (splitCoins r).2`, where `splitCoins : BitVec 512 ≃ BitVec 256 × BitVec 256`
  splits `r` into its high and low 256-bit halves and `encRandEquiv : BitVec 256 ≃ EncRand`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Braid

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoGames.LibsignalSession (ShaCompress)
/-- `toLEBytes n` is injective on `BitVec (8 * n)`: bit `i` of `x` is bit `i % 8` of byte `i / 8`. -/
theorem toLEBytes_injective (n : ℕ) :
    Function.Injective (fun x : BitVec (8 * n) => LibsignalAesCbc.toLEBytes n x) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hb : i % 8 < 8 := by omega
  have hget := congrArg (fun l : List (BitVec 8) => l[i / 8]?) h
  simp only [LibsignalAesCbc.toLEBytes, List.getElem?_ofFn, hj, ↓reduceDIte, Option.some.injEq] at hget
  have hbit := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hget
  simpa [BitVec.getLsbD_extractLsb', hb, Nat.div_add_mod i 8] using hbit

theorem toLEBytes_length (n : ℕ) {w : ℕ} (x : BitVec w) :
    (LibsignalAesCbc.toLEBytes n x).length = n := by
  simp [LibsignalAesCbc.toLEBytes]

theorem card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  have e : BitVec n ≃ Fin (2 ^ n) :=
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
  rw [Fintype.card_congr e, Fintype.card_fin]

private def fromLEList : (bs : List (BitVec 8)) → BitVec (8 * bs.length)
  | [] => 0#0
  | b :: bs => ((fromLEList bs ++ b).cast (by simp; omega))

private theorem getLsbD_fromLEList (bs : List (BitVec 8)) (i : ℕ) (hi : i < 8 * bs.length) :
    (fromLEList bs).getLsbD i =
      (bs[i / 8]'(by omega)).getLsbD (i % 8) := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    simp only [fromLEList, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · have hdiv : i / 8 = 0 := by omega
      have hmod : i % 8 = i := Nat.mod_eq_of_lt h8
      simp [h8, hdiv, hmod]
    · have hk : i - 8 < 8 * bs.length := by simp at hi; omega
      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
      have hmod : i % 8 = (i - 8) % 8 := by omega
      simp [h8, ih (i - 8) hk, hdiv, hmod]

private theorem toLEBytes_fromLEList (bs : List (BitVec 8)) :
    LibsignalAesCbc.toLEBytes bs.length (fromLEList bs) = bs := by
  apply List.ext_getElem
  · simp [LibsignalAesCbc.toLEBytes]
  · intro j hj1 hj2
    simp only [LibsignalAesCbc.toLEBytes, List.getElem_ofFn]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hlt : 8 * j + i < 8 * bs.length := by omega
    have hdiv : (8 * j + i) / 8 = j := by omega
    have hmod : (8 * j + i) % 8 = i := by omega
    rw [BitVec.getLsbD_extractLsb', getLsbD_fromLEList bs (8 * j + i) hlt]
    simp [hi, hdiv, hmod]

private theorem toLEVec_surjective (n : ℕ) :
    Function.Surjective
      (fun x : BitVec (8 * n) =>
        (⟨LibsignalAesCbc.toLEBytes n x, toLEBytes_length n x⟩ : List.Vector (BitVec 8) n)) := by
  intro ⟨bs, hbs⟩
  refine ⟨(fromLEList bs).cast (by omega), List.Vector.eq _ _ ?_⟩
  change LibsignalAesCbc.toLEBytes n ((fromLEList bs).cast _) = bs
  have hcast : ∀ {w₁ w₂ : ℕ} (hw : w₁ = w₂) (z : BitVec w₁),
      LibsignalAesCbc.toLEBytes n (z.cast hw) = LibsignalAesCbc.toLEBytes n z := by
    intro w₁ w₂ hw z; subst hw; rfl
  rw [hcast, ← hbs]
  exact toLEBytes_fromLEList bs

private noncomputable def toLEVecEquiv (n : ℕ) : BitVec (8 * n) ≃ List.Vector (BitVec 8) n :=
  Equiv.ofBijective
    (fun x => ⟨LibsignalAesCbc.toLEBytes n x, toLEBytes_length n x⟩)
    ⟨fun _ _ h => toLEBytes_injective n (congrArg List.Vector.toList h), toLEVec_surjective n⟩

theorem card_byteVector (n : ℕ) : Fintype.card (List.Vector (BitVec 8) n) = 2 ^ (8 * n) := by
  rw [← Fintype.card_congr (toLEVecEquiv n), card_bitVec]

def coinVec (r : BitVec 512) : Seed := ⟨coinBytes r, coinBytes_length r⟩

theorem coinVec_injective : Function.Injective coinVec := by
  intro x y h
  exact toLEBytes_injective 64 (congrArg List.Vector.toList h)

theorem coinVec_bijective : Function.Bijective coinVec :=
  ⟨coinVec_injective, fun v => by
    obtain ⟨x, hx⟩ := toLEVec_surjective 64 v
    exact ⟨x, List.Vector.eq _ _ (congrArg List.Vector.toList hx)⟩⟩

/-- Bijection `BitVec 512 ≃ Seed` via 64 little-endian bytes (`coinBytes`). -/
noncomputable def coinEquiv : BitVec 512 ≃ Seed := Equiv.ofBijective coinVec coinVec_bijective

theorem coinEquiv_apply (r : BitVec 512) : (coinEquiv r).toList = coinBytes r := by
  simp [coinEquiv, coinVec]

def key32Vec (k : BitVec 256) : EncRand :=
  ⟨LibsignalAesCbc.toLEBytes 32 k, toLEBytes_length 32 k⟩

theorem key32Vec_injective : Function.Injective key32Vec := by
  intro x y h
  exact toLEBytes_injective 32 (congrArg List.Vector.toList h)

theorem key32Vec_bijective : Function.Bijective key32Vec :=
  ⟨key32Vec_injective, toLEVec_surjective 32⟩

/-- Bijection `BitVec 256 ≃ EncRand` via 32 little-endian bytes. -/
noncomputable def encRandEquiv : BitVec 256 ≃ EncRand :=
  Equiv.ofBijective key32Vec key32Vec_bijective

theorem encRandEquiv_apply (k : BitVec 256) :
    (encRandEquiv k).toList = CryptoGames.HMAC.keyToBytes32 k := by
  simp [encRandEquiv, key32Vec, LibsignalAesCbc.toLEBytes, CryptoGames.HMAC.keyToBytes32]

/-- Taking the first 32 bytes of `coinBytes r` extracts the low 256 bits in little-endian order. -/
theorem coinBytes_take32 (r : BitVec 512) :
    (coinBytes r).take 32 = LibsignalAesCbc.toLEBytes 32 (r.setWidth 256) := by
  apply List.ext_getElem
  · simp [coinBytes, LibsignalAesCbc.toLEBytes]
  · intro j hj1 hj2
    have hj32 : j < 32 := by simpa [LibsignalAesCbc.toLEBytes] using hj2
    simp only [coinBytes, LibsignalAesCbc.toLEBytes, List.getElem_take, List.getElem_ofFn]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    simp [hi, show 8 * j + i < 256 by omega]

/-- Encapsulation randomness drawn from the first 32 bytes of `coinBytes r`. -/
def encRandOf (r : BitVec 512) : EncRand :=
  ⟨(coinBytes r).take 32, by simp [coinBytes_length]⟩

/-- Splits a 512-bit coin vector into its high and low 256-bit halves. -/
def splitCoins : BitVec 512 ≃ BitVec 256 × BitVec 256 where
  toFun r := (r.extractLsb' 256 256, r.extractLsb' 0 256)
  invFun p := p.1 ++ p.2
  left_inv r := BitVec.extractLsb'_append_extractLsb' (w := 256) (len := 256)
  right_inv p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hi, show ¬ 256 + i < 256 by omega]
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hi]

/-- `encRandOf r` factors through the low 256-bit half `(splitCoins r).2` via `encRandEquiv`. -/
theorem encRandOf_eq_split (r : BitVec 512) : encRandOf r = encRandEquiv (splitCoins r).2 := by
  apply List.Vector.eq
  have heq : (splitCoins r).2 = r.setWidth 256 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (r.extractLsb' 0 256).getLsbD i = (r.setWidth 256).getLsbD i
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    simp [hi]
  change (coinBytes r).take 32 = (encRandEquiv (splitCoins r).2).toList
  rw [encRandEquiv_apply, heq, coinBytes_take32]
  rfl

theorem coinBytes_take64 (r : BitVec 512) : (coinBytes r).take 64 = coinBytes r :=
  List.take_of_length_le (by rw [coinBytes_length])

/-- Sending from `.keysUnsampled` on `coinBytes r` draws the keygen seed `coinEquiv r`. -/
theorem nextCoins_init_coin (F : ShaCompress) (r : BitVec 512) (st : St F)
    (hst : ∃ ku, st = .keysUnsampled ku) :
    nextCoins F .init st (coinBytes r) = .seed (coinEquiv r) := by
  rcases hst with ⟨ku, rfl⟩
  have hlen : ((coinBytes r).take 64).length = 64 := by
    rw [coinBytes_take64, coinBytes_length]
  simp only [nextCoins, hlen, ↓reduceDIte]
  apply congrArg Coins.seed
  apply List.Vector.eq
  change (coinBytes r).take 64 = (coinEquiv r).toList
  rw [coinBytes_take64, coinEquiv_apply]

/-- Sending from `.headerReceived` on `coinBytes r` draws the encapsulation coins `encRandOf r`. -/
theorem nextCoins_seed_coin (F : ShaCompress) (s : Seed) (r : BitVec 512) (st : St F)
    (hst : ∃ hr, st = .headerReceived hr) :
    nextCoins F (.seed s) st (coinBytes r) = .both s (encRandOf r) := by
  rcases hst with ⟨hr, rfl⟩
  have hlen : ((coinBytes r).take 32).length = 32 := by
    simp [coinBytes_length]
  simp only [nextCoins, hlen, ↓reduceDIte]
  congr 1

theorem coinBytes_tape_ok (r : BitVec 512) : 64 ≤ (coinBytes r).length := by
  simp [coinBytes_length]

theorem encRand_toList_eq_iff (r : BitVec 512) (r' : EncRand) :
    r'.toList = (coinBytes r).take 32 ↔ r' = encRandOf r :=
  ⟨fun h => List.Vector.eq r' (encRandOf r) h, fun h => by subst h; rfl⟩

end CryptoVerification.SpqrV1Sync.Braid
