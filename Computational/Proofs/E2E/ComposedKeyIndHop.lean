/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.StatementComposed
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import LibsignalBinary.Proofs.E2E.PqxdhSpecTestsPure
import VCVio.EvalDist.Monad.Basic

/-!
# `DRKey` bijection and uniform sampling equivalence

**Checked by Lean.**

Establishes the bijection between 32-byte little-endian words (`word256ToBytes`, `keyToBytes32`,
`bytesToKey32`) and proves that `keySOf` of `sampleDRKey96` and uniform coins has the uniform
`SampledSessionKey` distribution.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.PqxdhSpecTests

private theorem uint8_ofNat_shift_toBitVec_eq_extractLsb' (w : BitVec 256) (j : ℕ) :
    (UInt8.ofNat ((w.toNat >>> (8 * j)) % 256)).toBitVec = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [UInt8.ofNat, BitVec.extractLsb'_toNat]

@[simp]
theorem ofU8_word256ToBytes (w : BitVec 256) :
    ofU8 (SignalPqxdh.word256ToBytes w) = HMAC.keyToBytes32 w := by
  refine List.ext_getElem (by simp [ofU8, SignalPqxdh.word256ToBytes, HMAC.keyToBytes32])
    fun j h1 h2 => ?_
  simp only [ofU8, SignalPqxdh.word256ToBytes, HMAC.keyToBytes32, List.getElem_map,
    List.getElem_ofFn]
  exact uint8_ofNat_shift_toBitVec_eq_extractLsb' w j

theorem word256ToBytes_eq_toU8_keyToBytes32 (w : BitVec 256) :
    SignalPqxdh.word256ToBytes w = toU8 (HMAC.keyToBytes32 w) := by
  rw [← toU8_ofU8 (SignalPqxdh.word256ToBytes w), ofU8_word256ToBytes]

@[simp]
theorem length_word256ToBytes (w : BitVec 256) :
    (SignalPqxdh.word256ToBytes w).length = 32 := by
  simp [SignalPqxdh.word256ToBytes]

@[simp]
theorem length_keyToBytes32 (k : BitVec 256) :
    (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [HKDF.bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : HKDF.bytesToKey32 (b :: rest) =
          (HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

@[simp]
theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    HKDF.bytesToKey32 (HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (HMAC.keyToBytes32 k) (i / 8) (by simp [HMAC.keyToBytes32, hj]) hj)
  simp only [HMAC.keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    HMAC.keyToBytes32 (HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [HMAC.keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

@[simp]
theorem bytesToKey32_ofU8_word256ToBytes (w : BitVec 256) :
    HKDF.bytesToKey32 (ofU8 (SignalPqxdh.word256ToBytes w)) = w := by
  rw [ofU8_word256ToBytes, bytesToKey32_keyToBytes32]

@[simp]
theorem bytesWord_word256ToBytes (w : BitVec 256) :
    bytesWord (SignalPqxdh.word256ToBytes w) = w :=
  bytesToKey32_ofU8_word256ToBytes w

@[simp]
theorem keySOf_wordsToDRKey (rk ck pqr aliceCoins : BitVec 256) :
    keySOf (SignalPqxdh.wordsToDRKey (rk, ck, pqr)) aliceCoins =
      ((rk, ck), aliceCoins, pqr) := by
  simp [keySOf, SignalPqxdh.wordsToDRKey]

theorem sample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    (($ᵗ (α × β) : ProbComp (α × β)) >>= f) =
      (($ᵗ α : ProbComp α) >>= fun a => ($ᵗ β : ProbComp β) >>= fun b => f (a, b)) := by
  have hsel : ($ᵗ (α × β) : ProbComp (α × β)) =
      (Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β)) := rfl
  rw [hsel]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

theorem sampleBytes32_bind {α : Type} (f : List UInt8 → ProbComp α) :
    (SignalPqxdh.sampleBytes32 >>= f) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun w => f (SignalPqxdh.word256ToBytes w)) := by
  unfold SignalPqxdh.sampleBytes32
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem length_of_mem_support_sampleBytes32 {bs : List UInt8}
    (h : bs ∈ support SignalPqxdh.sampleBytes32) : bs.length = 32 := by
  unfold SignalPqxdh.sampleBytes32 at h
  simp only [support_map, Set.mem_image] at h
  rcases h with ⟨w, _, rfl⟩
  exact length_word256ToBytes w

theorem lengths_of_mem_support_sampleDRKey96 {dk : SignalPqxdh.DRKey}
    (h : dk ∈ support SignalPqxdh.sampleDRKey96) :
    dk.rootKey.length = 32 ∧ dk.chainKey.length = 32 ∧ dk.pqrKey.length = 32 := by
  unfold SignalPqxdh.sampleDRKey96 at h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  rcases h with ⟨rk, hrk, ck, hck, pqr, hpqr, rfl⟩
  exact ⟨length_of_mem_support_sampleBytes32 hrk,
    length_of_mem_support_sampleBytes32 hck,
    length_of_mem_support_sampleBytes32 hpqr⟩

theorem sampleDRKey96_eq_wordsToDRKey :
    SignalPqxdh.sampleDRKey96 =
      (do
        let rk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        return SignalPqxdh.wordsToDRKey (rk, ck, pqr)) := by
  unfold SignalPqxdh.sampleDRKey96 SignalPqxdh.wordsToDRKey
  simp only [sampleBytes32_bind]

theorem sampleDRKey96_bind {α : Type} (f : SignalPqxdh.DRKey → ProbComp α) :
    (SignalPqxdh.sampleDRKey96 >>= f) =
      (do
        let rk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        f (SignalPqxdh.wordsToDRKey (rk, ck, pqr))) := by
  rw [sampleDRKey96_eq_wordsToDRKey]
  simp only [bind_assoc, pure_bind]

theorem sampleDRKey96_bind_keySOf {α : Type} (f : SampledSessionKey → ProbComp α) :
    (do
      let dk ← SignalPqxdh.sampleDRKey96
      let aliceCoins ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      f (keySOf dk aliceCoins)) =
    (do
      let rk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let aliceCoins ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      f ((rk, ck), aliceCoins, pqr)) := by
  rw [sampleDRKey96_bind]
  simp only [keySOf_wordsToDRKey]

theorem select_keyS_bind {α : Type} (f : SampledSessionKey → ProbComp α) :
    (($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= f) =
      (do
        let rk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let ck ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let aliceCoins ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        f ((rk, ck), aliceCoins, pqr)) := by
  rw [sample_prod_bind, sample_prod_bind]
  refine bind_congr fun rk => bind_congr fun ck => ?_
  exact sample_prod_bind (fun rest => f ((rk, ck), rest))

/-- Mapping `sampleDRKey96` and uniform `BitVec 256` coins through `keySOf` yields a uniform
`SampledSessionKey`. -/
theorem evalDist_sampleDRKey96_keySOf_eq_select_keyS {α : Type} [MeasurableSpace α]
    (f : SampledSessionKey → ProbComp α) :
    𝒟[do
      let dk ← SignalPqxdh.sampleDRKey96
      let aliceCoins ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      f (keySOf dk aliceCoins)] =
    𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= f] := by
  rw [sampleDRKey96_bind_keySOf, select_keyS_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun rk => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun ck => ?_
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)
    (fun pqr aliceCoins => f ((rk, ck), aliceCoins, pqr))

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem liftM_unif_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    (liftM (pure a : ProbComp α) : OracleComp (unifSpec + spec) α) = pure a := rfl

@[simp]
private theorem liftM_unif_query_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (q : unifSpec.Domain) (k : unifSpec.Range q → ProbComp α) :
    (liftM (liftM (OracleSpec.query q) >>= k) : OracleComp (unifSpec + spec) α) =
      (liftM (OracleSpec.query (spec := unifSpec + spec) (Sum.inl q)) >>=
        fun u => (liftM (k u) : OracleComp (unifSpec + spec) α)) := rfl

abbrev kioKind (S : SignalPqxdh.Setup) :
    (q : SignalPqxdh.KeyIndQuery S) →
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) SignalPqxdh.KeyIndResponse :=
  fun q => query (spec := unifSpec + SignalPqxdh.keyIndSpec S) (.inr q)

end CryptoVerification.E2E
