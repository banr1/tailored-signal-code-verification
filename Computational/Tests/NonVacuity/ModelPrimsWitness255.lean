/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SignalPqxdh.CwfPrimitives
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import VCVio.EvalDist.Monad.Basic

/-!
# Concrete `BitVec 255` Primitive Witness

Constructs a concrete primitive witness `(Pt := BitVec 255, dh255, c255, K255, Q255, W255, X255)`
backed by the masked XOR action `SpecTests.SignalPqxdh.cwfX`, and proves `dh255.Commutes`,
`DhKerUniform dh255`, `X25519RealizesDh c255 dh255 encPt255 encT255`, and
`ModelPrimsCryptoAssumptions X255 W255`.

Points in `BitVec 255` embed into 32-byte keys with top bit clear (`encPt255`). The witness is
intentionally insecure (`X255_pre.kemKeyGen` exposes its 32-byte seed in the public key and
`K255`/`Q255` return constant shared secrets) and is used only to witness joint consistency of the
primitive hypotheses.
-/

@[expose] public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession CKA
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
  CryptoGames.LibsignalSM.Proofs.Correctness
open SignalPqxdh SpecTests.SignalPqxdh

/-- 32-byte little-endian encoding of `Q : BitVec 255` with top bit clear. -/
def encPt255 (Q : BitVec 255) : List (BitVec 8) :=
  HMAC.keyToBytes32 (Q.zeroExtend 256)

def encT255 (Q : BitVec 255) : PublicKey := ⟨vec32 (encPt255 Q)⟩

/-- Left inverse of `encT255` that truncates a 32-byte little-endian key to 255 bits. -/
def decT255 (pk : PublicKey) : Option (BitVec 255) :=
  some ((HKDF.bytesToKey32 pk.1.toList).truncate 255)

/-- `DHFun` instance on `BitVec 255` backed by `cwfX`. -/
def dh255 : DHFun (BitVec 256) (BitVec 255) where
  base := 9#255
  dh k Q := (HKDF.bytesToKey32 (ofU8 (cwfX (word256ToBytes k) (toU8 (encPt255 Q))))).truncate 255

/-- `Crypto` instance with identity block primitives and `cwfX` X25519 hooks. -/
def c255 : Crypto where
  F := fun st _ => st
  E := fun _ b => b
  D := fun _ b => b
  X := fun s u => u8Vec 32 (cwfX (vecU8 s) (vecU8 u))
  pubKey := fun s => u8Vec 32 (cwfX (vecU8 s) (toU8 x25519Base))

/-- Constant `MlKem` witness with total `encaps1`. -/
def K255 : MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
    List.Vector.replicate 32 0#8)
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 0#8
  validPk := fun _ _ => true

/-- `PqxdhPrims` witness with `cwfCanon` point decoding and `K255`. -/
def Q255 : PqxdhPrims where
  F512 := fun st _ => st
  montToEd := fun u s =>
    if s == 0#8 && cwfCanon (vecU8 u) then some (List.Vector.replicate 160 0#8) else none
  compress := fun _ => List.Vector.replicate 32 0#8
  edNeg := fun p => p
  isTorsionFree := fun _ => true
  dsmb := fun _ a _ => a
  scalarMod := fun b => b
  scalarWide := fun _ => List.Vector.replicate 32 0#8
  encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps := fun _ _ => List.Vector.replicate 32 0#8
  K := K255

def W255 : PEParams := ⟨c255, Q255⟩

/-- Base `UnreachedPqxdhPrimitives` witness with `pow8 = cwfP8` whose `kemKeyGen` places the first
32 seed bytes in the public key (sufficient for `cwfPrimitives_kem_coll_bound`). -/
def X255_pre : UnreachedPqxdhPrimitives where
  sigPkGen := fun a => vecU8 (c255.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
  sigSign := fun _ _ _ => List.replicate 64 0
  scalarMul := fun _ _ => List.replicate 32 0
  scalarAdd := fun _ _ => List.replicate 32 0
  kemKeyGen := fun seed => (fitBytes 1568 (seed.take 32), fitBytes 3168 seed)
  pow8 := cwfP8
  isValidDhTriple := fun _ _ _ => false

/-- `X255_pre` with `isValidDhTriple` set to the classical decision procedure for `isValidDhTripleRef`. -/
noncomputable def X255 : UnreachedPqxdhPrimitives :=
  { X255_pre with
    isValidDhTriple := fun A B Z =>
      @decide (isValidDhTripleRef (modelPrims X255_pre W255) A B Z) (Classical.propDecidable _) }

private theorem uint8_xor_left_comm (a b c : UInt8) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  apply UInt8.toBitVec_inj.1
  show a.toBitVec ^^^ (b.toBitVec ^^^ c.toBitVec) = b.toBitVec ^^^ (a.toBitVec ^^^ c.toBitVec)
  rw [← BitVec.xor_assoc, BitVec.xor_comm a.toBitVec b.toBitVec, BitVec.xor_assoc]

private theorem cwfByte_xor_left_comm (i : Nat) (x y z : UInt8) :
    cwfByte i (x ^^^ cwfByte i (y ^^^ z)) = cwfByte i (y ^^^ cwfByte i (x ^^^ z)) := by
  rw [cwfByte_eq_iff, uint8_and_xor, cwfByte_mask, uint8_and_xor,
      uint8_and_xor, cwfByte_mask, uint8_and_xor, uint8_xor_left_comm]

private theorem cwfX25519_getD (x y : List UInt8) (i : Nat) (hi : i < 32) :
    (cwfX25519 x y).getD i 0 = cwfByte i ((cwfC x).getD i 0 ^^^ (cwfC y).getD i 0) := by
  unfold cwfX25519
  have hl : (xorBytes (cwfC x) (cwfC y)).length = 32 := by simp [cwfC_length]
  rw [cwfC_getD _ i hi, fitBytes_of_length_eq hl,
      xorBytes_getD _ _ i (by rw [cwfC_length]; exact hi) (by rw [cwfC_length]; exact hi)]

private theorem cwfX25519_length (x y : List UInt8) : (cwfX25519 x y).length = 32 :=
  cwfC_length _

private theorem cwfX25519_left_comm (a b c : List UInt8) :
    cwfX25519 a (cwfX25519 b c) = cwfX25519 b (cwfX25519 a c) := by
  apply bytes32_ext (cwfX25519_length _ _) (cwfX25519_length _ _)
  intro i hi
  have hbc : cwfC (cwfX25519 b c) = cwfX25519 b c := cwfC_idem _
  have hac : cwfC (cwfX25519 a c) = cwfX25519 a c := cwfC_idem _
  rw [cwfX25519_getD _ _ i hi, cwfX25519_getD _ _ i hi, hbc, hac,
      cwfX25519_getD _ _ i hi, cwfX25519_getD _ _ i hi, cwfByte_xor_left_comm]

private theorem zeroExtend_truncate_255 (Q : BitVec 255) :
    (Q.zeroExtend 256).truncate 255 = Q := by
  ext i hi; simp

private theorem zeroExtend_255_toNat_lt (Q : BitVec 255) :
    (Q.zeroExtend 256).toNat < 2 ^ 255 := by
  have := Q.isLt
  simp only [BitVec.toNat_setWidth]
  omega

private theorem truncate_zeroExtend_255_of_testBit_false (w : BitVec 256)
    (h : w.toNat.testBit 255 = false) :
    (w.truncate 255).zeroExtend 256 = w := by
  have hdiv : (w.toNat / 2 ^ 255).testBit 0 = false := by
    rw [Nat.testBit_div_two_pow]; exact h
  have hlt : w.toNat < 2 ^ 255 := by
    have hw := w.isLt
    by_contra hge
    have h1 : w.toNat / 2 ^ 255 = 1 := by omega
    rw [h1] at hdiv; revert hdiv; decide
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [BitVec.toNat_setWidth]
  omega

private theorem word256ToBytes_bytesToKey32_ofU8 (bs : List UInt8) (h : bs.length = 32) :
    word256ToBytes (HKDF.bytesToKey32 (ofU8 bs)) = bs := by
  rw [word256ToBytes_eq_toU8_keyToBytes32, keyToBytes32_bytesToKey32 _ (by simp [h]), toU8_ofU8]

private theorem uint8_testBit_7_of_and_80 (b : UInt8) (h : (b &&& 0x80) = 0) :
    b.toNat.testBit 7 = false := by
  have h1 := congrArg (fun x : UInt8 => x.toNat.testBit 7) h
  simp only [UInt8.toNat_and, Nat.testBit_and] at h1
  exact Bool.eq_false_iff.mpr fun hb => by rw [hb] at h1; exact Bool.noConfusion h1

private theorem cwfX_testBit_255 (sk pk : List UInt8) :
    (HKDF.bytesToKey32 (ofU8 (cwfX sk pk))).toNat.testBit 255 = false := by
  have hw := word256ToBytes_bytesToKey32_ofU8 (cwfX sk pk) (cwfX_length sk pk)
  have hbit := word_byte_testBit (HKDF.bytesToKey32 (ofU8 (cwfX sk pk))).toNat 31 7 (by decide)
  rw [← word256ToBytes_getD _ 31 (by decide), hw] at hbit
  rw [← hbit]
  unfold cwfX cwfX25519
  split
  · exact uint8_testBit_7_of_and_80 _ (cwfC_and_80 _)
  · rfl

private theorem encPt255_truncate_cwfX (sk pk : List UInt8) :
    encPt255 ((HKDF.bytesToKey32 (ofU8 (cwfX sk pk))).truncate 255) = ofU8 (cwfX sk pk) := by
  unfold encPt255
  rw [truncate_zeroExtend_255_of_testBit_false _ (cwfX_testBit_255 sk pk),
      keyToBytes32_bytesToKey32 _ (by simp [cwfX_length])]

private theorem encPt255_dh255 (k : BitVec 256) (Q : BitVec 255) :
    encPt255 (dh255.dh k Q) = ofU8 (cwfX (word256ToBytes k) (toU8 (encPt255 Q))) :=
  encPt255_truncate_cwfX (word256ToBytes k) (toU8 (encPt255 Q))

private theorem toU8_encPt255_dh255 (k : BitVec 256) (Q : BitVec 255) :
    toU8 (encPt255 (dh255.dh k Q)) = cwfX (word256ToBytes k) (toU8 (encPt255 Q)) := by
  rw [encPt255_dh255, toU8_ofU8]

private theorem encPt255_inj : Function.Injective encPt255 := by
  intro a b h
  have h1 := congrArg HKDF.bytesToKey32 h
  simp only [encPt255, bytesToKey32_keyToBytes32] at h1
  rw [← zeroExtend_truncate_255 a, ← zeroExtend_truncate_255 b, h1]

private theorem encPt255_length (Q : BitVec 255) : (encPt255 Q).length = 32 :=
  length_keyToBytes32 _

private theorem encPt255_zero : encPt255 0 = List.replicate 32 0#8 := by decide

private theorem encPt255_base : encPt255 dh255.base = x25519Base := by decide

private theorem encT255_toList (Q : BitVec 255) : (encT255 Q).1.toList = encPt255 Q := by
  simp [encT255, vec32, encPt255_length]

theorem decT255_encT255 (Q : BitVec 255) : decT255 (encT255 Q) = some Q := by
  unfold decT255
  rw [encT255_toList, encPt255, bytesToKey32_keyToBytes32, zeroExtend_truncate_255]

theorem encT255_inj : Function.Injective encT255 := by
  intro a b h
  exact Option.some.inj ((decT255_encT255 a).symm.trans (by rw [h, decT255_encT255]))

theorem encT255_ne_dummyKey (Q : BitVec 255) : encT255 Q ≠ dummyKey := by
  intro h
  have h1 := congrArg
    (fun pk : PublicKey => decide ((HKDF.bytesToKey32 pk.1.toList).toNat < 2 ^ 255)) h
  rw [encT255_toList, encPt255, bytesToKey32_keyToBytes32,
      decide_eq_true (zeroExtend_255_toNat_lt Q)] at h1
  have h2 : decide ((HKDF.bytesToKey32 dummyKey.1.toList).toNat < 2 ^ 255) = false := by decide
  rw [h2] at h1; exact Bool.noConfusion h1

private theorem cwfX_clamp (sk pk : List UInt8) :
    cwfX (clampScalar25519 sk) pk = cwfX sk pk := by
  unfold cwfX cwfX25519; rw [cwfC_clamp]

private theorem vecU8_clampScalar_u8Vec (a : List UInt8) :
    vecU8 (Ratchet.clampScalar (u8Vec 32 a)) = clampScalar25519 a := by
  rw [← u8Vec_clampScalar25519, vecU8_u8Vec_of_length _ (clampScalar25519_length a)]

private theorem cwfGood_base : cwfGood (toU8 x25519Base) = true := by decide

private theorem cwfX_of_good {sk pk : List UInt8} (h : cwfGood pk = true) :
    cwfX sk pk = cwfX25519 sk pk := by
  simp [cwfX, h]

private theorem vecU8_vec32_of_length (bs : List (BitVec 8)) (h : bs.length = 32) :
    vecU8 (vec32 bs) = toU8 bs := by
  simp [vecU8, vec32, h]

private theorem vecU8_vec32_keyToBytes32 (k : BitVec 256) :
    vecU8 (vec32 (HMAC.keyToBytes32 k)) = word256ToBytes k := by
  rw [vecU8_vec32_of_length _ (length_keyToBytes32 k), ← word256ToBytes_eq_toU8_keyToBytes32]

private theorem word256ToBytes_clamp256 (k : BitVec 256) :
    word256ToBytes (clamp256 k) = clampScalar25519 (word256ToBytes k) := by
  have h1 : u8Vec 32 (word256ToBytes (clamp256 k)) =
      u8Vec 32 (clampScalar25519 (word256ToBytes k)) := by
    rw [u8Vec_word256ToBytes, ← clampScalar_keyVec,
        ← u8Vec_word256ToBytes, u8Vec_clampScalar25519]
  have h2 := congrArg vecU8 h1
  rwa [vecU8_u8Vec_of_length _ (length_word256ToBytes _),
       vecU8_u8Vec_of_length _ (clampScalar25519_length _)] at h2

theorem dh255_zero (x : BitVec 256) : dh255.dh x 0 = 0 := by
  apply encPt255_inj
  rw [encPt255_dh255, encPt255_zero]
  have hz : toU8 (List.replicate 32 0#8) = cwfZero := rfl
  rw [hz, show cwfX (word256ToBytes x) cwfZero = cwfZero by simp [cwfX, cwfGood_zero]]
  rfl

private theorem dh255_ne_zero (k : BitVec 256) (Q : BitVec 255) (hQ : Q ≠ 0) :
    dh255.dh k Q ≠ 0 := by
  intro h0
  have heq := congrArg (fun x => toU8 (encPt255 x)) h0
  rw [toU8_encPt255_dh255, encPt255_zero] at heq
  have hz : toU8 (List.replicate 32 0#8) = List.replicate 32 0 := rfl
  rw [hz, cwfX_zero_iff] at heq
  have hlen : (toU8 (encPt255 Q)).length = 32 := by simp [encPt255_length]
  have hzero : toU8 (encPt255 Q) = cwfZero := by
    unfold cwfGood at heq
    rw [hlen] at heq
    simpa using heq
  have henc : encPt255 Q = encPt255 0 := by
    rw [← ofU8_toU8 (encPt255 Q), hzero, encPt255_zero]; rfl
  exact hQ (encPt255_inj henc)

theorem dh255_commutes : dh255.Commutes := by
  intro a b
  have h : toU8 (encPt255 (dh255.dh a (dh255.dh b dh255.base))) =
      toU8 (encPt255 (dh255.dh b (dh255.dh a dh255.base))) := by
    rw [toU8_encPt255_dh255, toU8_encPt255_dh255, toU8_encPt255_dh255, toU8_encPt255_dh255,
        encPt255_base,
        cwfX_of_good cwfGood_base,
        cwfX_of_good (by unfold cwfX25519; exact cwfGood_cwfC _),
        cwfX_of_good cwfGood_base,
        cwfX_of_good (by unfold cwfX25519; exact cwfGood_cwfC _)]
    exact cwfX25519_left_comm (word256ToBytes a) (word256ToBytes b) (toU8 x25519Base)
  apply encPt255_inj
  have h1 := congrArg ofU8 h
  rwa [ofU8_toU8, ofU8_toU8] at h1

theorem dh255_kerUniform : DhKerUniform dh255 := by
  intro s x Q Q'
  have hiff (a : BitVec 256) :
      dh255.dh a Q = dh255.dh a Q' ↔
        cwfP8 (toU8 (encPt255 Q)) = cwfP8 (toU8 (encPt255 Q')) := by
    constructor
    · intro h
      have h1 := congrArg (fun P => toU8 (encPt255 P)) h
      rw [toU8_encPt255_dh255, toU8_encPt255_dh255] at h1
      exact cwfX_inj _ _ _ h1
    · intro h
      apply encPt255_inj
      rw [encPt255_dh255, encPt255_dh255, cwfX_pow8_congr _ _ _ h]
  rw [hiff x, hiff s]

theorem libX25519Rel_c255 : X25519RealizesDh c255 dh255 encPt255 encT255 := by
  refine ⟨?_, fun _ => rfl⟩
  refine
    { enc_injective := encPt255_inj
      enc_length := encPt255_length
      enc_zero := encPt255_zero
      enc_base := encPt255_base
      base_ne_zero := by decide
      hook := fun k Q => ?_
      pubKey_hook := fun k => ?_
      dh_clamp := fun k Q => ?_
      dh_ne_zero := dh255_ne_zero }
  · dsimp only [c255]
    rw [vecU8_vec32_keyToBytes32, vecU8_vec32_of_length _ (encPt255_length Q),
        ← ofU8_fitBytesRef_eq_u8Vec_toList, fitBytesRef_of_length_eq (cwfX_length _ _),
        encPt255_dh255]
  · dsimp only [c255]
    rw [vecU8_vec32_keyToBytes32, ← ofU8_fitBytesRef_eq_u8Vec_toList,
        fitBytesRef_of_length_eq (cwfX_length _ _), encPt255_dh255, encPt255_base]
  · dsimp only [dh255]
    rw [word256ToBytes_clamp256, cwfX_clamp]

private theorem modelPrims_X255_x25519Base (a : List UInt8) :
    (modelPrims X255 W255).x25519Base a = cwfX25519 a (toU8 x25519Base) := by
  dsimp only [modelPrims, blockLevelPrims, W255, c255]
  rw [vecU8_u8Vec_of_length _ (cwfX_length _ _), vecU8_clampScalar_u8Vec, cwfX_clamp,
      cwfX, cwfGood_base]
  rfl

private theorem modelPrims_X255_x25519 (a pk : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X255 W255).x25519 a pk = cwfX a pk := by
  dsimp only [modelPrims, blockLevelPrims, W255, c255]
  rw [vecU8_u8Vec_of_length _ (cwfX_length _ _), vecU8_clampScalar_u8Vec,
      vecU8_u8Vec_of_length pk hpk, cwfX_clamp]

private theorem modelPrims_X255_isCanonical (pk : List UInt8) :
    (modelPrims X255 W255).isCanonical pk = cwfCanon pk := by
  dsimp only [modelPrims, blockLevelPrims, W255, Q255, isCanonicalRef]
  by_cases hc : cwfCanon pk = true
  · obtain ⟨hlen, hfix⟩ := cwfCanon_spec hc
    have h80 : (pk.getD 31 0 &&& 0x80) = 0 := by rw [← hfix]; exact cwfC_and_80 pk
    have hr : scalarIsInRange pk = true := by rw [← hfix]; exact cwfC_scalarIsInRange pk
    rw [hc, hlen, h80, hr, vecU8_u8Vec_of_length pk hlen, hc]
    rfl
  · have hfalse : cwfCanon pk = false := Bool.eq_false_iff.mpr hc
    by_cases hlen : pk.length = 32
    · rw [hfalse, vecU8_u8Vec_of_length pk hlen, hfalse]
      split <;> rfl
    · have hlenB : (pk.length == 32) = false := beq_eq_false_iff_ne.mpr hlen
      simp [hfalse, hlenB]

theorem modelPrims_X255_sig_corr (sk msg r : List UInt8) :
    (modelPrims X255 W255).sigVerify (X255.sigPkGen sk) msg (X255.sigSign sk msg r) = true := by
  have hpk : X255.sigPkGen sk = cwfX25519 sk (toU8 x25519Base) := modelPrims_X255_x25519Base sk
  have hcan : cwfCanon (X255.sigPkGen sk) = true := by
    rw [hpk]; unfold cwfX25519; exact cwfCanon_cwfC _
  have hlen : (X255.sigPkGen sk).length = 32 := (cwfCanon_spec hcan).1
  rw [modelPrims_sigVerify_eq_ref]
  have hsig : X255.sigSign sk msg r = List.replicate 64 0 := rfl
  rw [hsig]
  unfold xeddsaVerifyRef
  have hcond : ((X255.sigPkGen sk).length == 32 &&
      (List.replicate 64 (0 : UInt8)).length == 64 &&
      (((List.replicate 64 (0 : UInt8)).getD 63 0 &&& 0x60) == 0)) = true := by
    rw [hlen]; decide
  rw [hcond]
  dsimp only [modelPrims, blockLevelPrims, W255, Q255]
  have hs0 : (((List.replicate 64 (0 : UInt8)).getD 63 0 &&& 0x80) >>> 7).toBitVec == 0#8 := by
    decide
  rw [vecU8_u8Vec_of_length _ hlen, hcan, hs0]
  decide

private theorem cwfX25519_base_fiber_card (c : List UInt8) :
    (Finset.univ.filter (fun w : BitVec 256 =>
      cwfX25519 (word256ToBytes w) (toU8 x25519Base) = c)).card ≤ 32 := by
  calc (Finset.univ.filter (fun w : BitVec 256 =>
          cwfX25519 (word256ToBytes w) (toU8 x25519Base) = c)).card
      ≤ (Finset.range 8 ×ˢ Finset.range 4).card := by
        apply Finset.card_le_card_of_injOn (fun w => (w.toNat % 8, w.toNat / 2 ^ 254))
        · intro w _
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact ⟨Nat.mod_lt _ (by decide), by
            have := w.isLt
            exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by omega)⟩
        · intro w hw w' hw' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
          simp only [Prod.mk.injEq] at heq
          have hcomm : cwfX25519 (toU8 x25519Base) (word256ToBytes w) =
              cwfX25519 (toU8 x25519Base) (word256ToBytes w') := by
            rw [cwfX25519_comm, hw, cwfX25519_comm _ (word256ToBytes w'), hw']
          exact cwfC_word_eq w w' (cwfX25519_inj _ _ _ hcomm) heq.1 heq.2
    _ = 32 := by simp

private theorem modelPrims_X255_ec_coll_bound (targetPk : List UInt8) :
    (𝒟[do
        let sk ← sampleScalar32
        pure (X255.pow8 ((modelPrims X255 W255).x25519Base sk) ==
          X255.pow8 targetPk)] {true}).toReal
        ≤ 1 / (2 : ℝ) ^ 250 := by
  have hc : ∀ sk, X255.pow8 ((modelPrims X255 W255).x25519Base sk) =
      cwfX25519 sk (toU8 x25519Base) := fun sk => by
    rw [modelPrims_X255_x25519Base]; exact cwfP8_cwfC _
  simp only [hc, sampleScalar32, sampleBytes32, bind_pure_comp, Functor.map_map]
  refine le_trans (uniform256_map_bool_le _ 32 ?_) (by norm_num)
  refine le_trans (Finset.card_le_card ?_) (cwfX25519_base_fiber_card (X255.pow8 targetPk))
  intro w hw
  simpa using hw

theorem modelPrims_X255_cryptoAssumptions : ModelPrimsCryptoAssumptions X255 W255 where
  x25519_zero_iff := fun a1 a2 pk _ _ hpk => by
    rw [modelPrims_X255_x25519 a1 pk hpk, modelPrims_X255_x25519 a2 pk hpk,
        cwfX_zero_iff, cwfX_zero_iff]
  canon_base := fun e _ => by
    rw [modelPrims_X255_isCanonical, modelPrims_X255_x25519Base]
    exact cwfCanon_cwfC _
  canon_x25519 := fun a pk _ hcan => by
    rw [modelPrims_X255_isCanonical] at hcan ⊢
    obtain ⟨hpk, hfix⟩ := cwfCanon_spec hcan
    rw [modelPrims_X255_x25519 a pk hpk, ← hfix, cwfX_cwfC]
    exact cwfCanon_cwfC _
  pow8_idemp := cwfP8_idem
  isValidDhTriple_eq_ref := fun A B Z => by
    dsimp only [X255]
    exact @decide_eq_true_iff _ (Classical.propDecidable _)
  x25519_pow8_congr := fun a pk1 pk2 _ h1 h2 hpow => by
    rw [modelPrims_X255_x25519 a pk1 h1, modelPrims_X255_x25519 a pk2 h2]
    exact cwfX_pow8_congr a pk1 pk2 hpow
  x25519_congr_of_base_eq := fun a1 a2 pk _ _ hcan hbase => by
    rw [modelPrims_X255_isCanonical] at hcan
    have hpk := (cwfCanon_spec hcan).1
    rw [modelPrims_X255_x25519Base, modelPrims_X255_x25519Base] at hbase
    have hcomm : cwfX25519 (toU8 x25519Base) a1 = cwfX25519 (toU8 x25519Base) a2 := by
      rw [cwfX25519_comm, hbase, cwfX25519_comm]
    have hc := cwfX25519_inj _ _ _ hcomm
    rw [modelPrims_X255_x25519 a1 pk hpk, modelPrims_X255_x25519 a2 pk hpk]
    unfold cwfX cwfX25519; rw [hc]
  canon_pow8_inj := fun pk1 pk2 h1 h2 hpow => by
    rw [modelPrims_X255_isCanonical] at h1 h2
    exact cwfPrimitives_wellFormed.canon_pow8_inj pk1 pk2 h1 h2 hpow
  pow8_len := cwfP8_length
  ec_coll_bound := modelPrims_X255_ec_coll_bound
  x25519_inj_pow8 := fun a pk1 pk2 _ h1 h2 hx => by
    rw [modelPrims_X255_x25519 a pk1 h1, modelPrims_X255_x25519 a pk2 h2] at hx
    exact cwfX_inj a pk1 pk2 hx
  pow8_base_len := fun p e _ hpow => by
    rw [modelPrims_X255_x25519Base] at hpow
    have hg := cwfGood_of_P8_eq hpow
    unfold cwfX25519 at hg
    rw [cwfGood_cwfC] at hg
    exact cwfGood_len hg
  sigPkGen_eq_x25519Base := rfl
  scalarMul_len := fun _ _ => by simp [X255, X255_pre]
  scalarAdd_len := fun _ _ => by simp [X255, X255_pre]
  kemKeyGen_len := fun seed => ⟨fitBytes_length 1568 (seed.take 32), fitBytes_length 3168 seed⟩
  sig_corr := modelPrims_X255_sig_corr
  kem_coll_bound := cwfPrimitives_kem_coll_bound

#print axioms modelPrims_X255_cryptoAssumptions
#print axioms dh255_commutes
#print axioms libX25519Rel_c255
#print axioms dh255_kerUniform

end CryptoVerification.E2E
