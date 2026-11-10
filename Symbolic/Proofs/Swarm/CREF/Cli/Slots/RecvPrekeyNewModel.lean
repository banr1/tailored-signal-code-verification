/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# PQXDH Primitive Bridges and Store Event Layout

Proves byte-offset projections for `preKeyStoreEventsBytes`, X25519 scalar clamping and `< p25519`
canonicality extraction under `ModelAgree`, and byte-level X25519 and ML-KEM-1024 equations for
`modelPrims`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionFree toEdwardsSymbol torsionFreeSymbol
  kyberDecapsSymbol)
open DY.Libsignal.TripleRatchet.Refinement (clamp clampByte)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF PreKeyFields pubBytes secretBytes ecKey kyberDecapsBytes vec32)
open DY.Libsignal.Composed.Refinement.Cli (ModelAgree)
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.TR (dhAgreeBytes secretBytes_eq setupRandomsAt_eq)

/-! ## Store Event Byte Offsets -/

@[simp] theorem toLEBytes_4_length (v : BitVec 32) :
    (toLEBytes 4 v).length = 4 := rfl

theorem eventsBytes_append_getElem?_zero (m : PreKeyMessageFields) (pt : HwBytes) :
    ((preKeyStoreEventsBytes m ++ pt)[0]?).any (· != 0#8) = true := by
  cases m.opkId <;> rfl

theorem eventsBytes_append_slice_9_33 (m : PreKeyMessageFields) (pt : HwBytes) :
    ((preKeyStoreEventsBytes m ++ pt).drop 9).take 33 = djbKey m.baseKey := by
  have hd : (1#8 :: (toLEBytes 4 m.kpkId ++ toLEBytes 4 m.spkId)).length = 9 := rfl
  have hcat :
      preKeyStoreEventsBytes m ++ pt =
        (1#8 :: (toLEBytes 4 m.kpkId ++ toLEBytes 4 m.spkId)) ++
          (djbKey m.baseKey ++
            ((match m.opkId with
              | some i => 1#8 :: toLEBytes 4 i
              | none => 0#8 :: toLEBytes 4 (0#32)) ++ pt)) := by
    simp only [preKeyStoreEventsBytes, List.cons_append, List.append_assoc]; rfl
  rw [hcat, List.drop_left' hd,
      List.take_append_of_le_length (by simp [djbKey]),
      List.take_of_length_le (by simp [djbKey])]

theorem eventsBytes_append_getElem?_42 (m : PreKeyMessageFields) (pt : HwBytes) :
    ((preKeyStoreEventsBytes m ++ pt)[42]?).any (· != 0#8) = m.opkId.isSome := by
  let pre := 1#8 :: (toLEBytes 4 m.kpkId ++ (toLEBytes 4 m.spkId ++ djbKey m.baseKey))
  have hpre : pre.length = 42 := by simp [pre, djbKey]
  have hle : pre.length ≤ 42 := Nat.le_of_eq hpre
  have hcat :
      preKeyStoreEventsBytes m ++ pt =
        pre ++
          ((match m.opkId with
            | some i => 1#8 :: toLEBytes 4 i
            | none => 0#8 :: toLEBytes 4 (0#32)) ++ pt) := by
    simp only [pre, preKeyStoreEventsBytes, List.cons_append, List.append_assoc]; rfl
  rw [hcat, List.getElem?_append_right hle, hpre, Nat.sub_self]
  cases m.opkId <;> rfl

/-! ## Scalar Clamping and Byte-Vector Conversions -/

private theorem toU8_length_rpnmba1 (bs : HwBytes) : (toU8 bs).length = bs.length := by
  simp [toU8]

theorem ofU8_toU8_id (bs : HwBytes) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    unfold toU8 ofU8 at *
    simp only [List.map_cons, ih]

theorem toU8_ofU8_id (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    unfold toU8 ofU8 at *
    simp only [List.map_cons, ih]

theorem u8Vec_toU8_of_length {n : Nat} {bs : HwBytes} (hb : bs.length = n) :
    u8Vec n (toU8 bs) = ⟨bs, hb⟩ := by
  apply List.Vector.eq
  change (fitVec n (ofU8 (toU8 bs))).toList = bs
  rw [ofU8_toU8_id]
  unfold fitVec
  simp [hb]

@[simp] private theorem u8Vec_vecU8_rpnmba1 {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (vecU8 v) = v := by
  unfold vecU8
  rw [u8Vec_toU8_of_length v.toList_length]
  exact List.Vector.eq _ _ rfl

@[simp] private theorem ofU8_vecU8_rpnmba1 {n : Nat} (v : List.Vector (BitVec 8) n) :
    ofU8 (vecU8 v) = v.toList :=
  ofU8_toU8_id v.toList

private theorem bytesToVec_toList_local {n : Nat} {b : HwBytes} (hb : b.length = n) :
    (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec n b).toList = b := by
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec
  change (b ++ List.replicate n 0#8).take n = b
  rw [List.take_append_of_le_length (Nat.le_of_eq hb.symm),
      List.take_of_length_le (Nat.le_of_eq hb)]

theorem clampScalar_toList_eq_clamp_toList (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList = clamp v.toList := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  change [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
    (b31 &&& 0x7f#8) ||| 0x40#8] = _
  simp [clamp, clampByte]

theorem clampScalar_idem_pure (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.eq
  rw [clampScalar_toList_eq_clamp_toList, clampScalar_toList_eq_clamp_toList,
      DY.Libsignal.TripleRatchet.Refinement.clamp_clamp]

theorem secretBytes_length_bob {r : ProtocolSetup} (hwf : ProtocolSetupWF r) :
    (secretBytes r 0).length = 32 ∧
      (secretBytes r 1).length = 32 ∧
      (secretBytes r 2).length = 32 ∧
      (r.withOpk = true → (secretBytes r 6).length = 32) := by
  have hs := secretBytes_eq r hwf.1
  have hr := setupRandomsAt_eq r hwf.1
  refine ⟨?_, ?_, ?_, fun hopk => ?_⟩
  · rw [hs.1]; exact hwf.2.1 (0, 32) (by rw [hr]; cases r.withOpk <;> simp)
  · rw [hs.2.1]; exact hwf.2.1 (5, 32) (by rw [hr]; cases r.withOpk <;> simp)
  · rw [hs.2.2.1]; exact hwf.2.1 (10, 32) (by rw [hr]; cases r.withOpk <;> simp)
  · rw [hs.2.2.2.2 hopk]; exact hwf.2.1 (22, 32) (by rw [hr, hopk]; simp)

/-! ## Scalar Range and Canonicality -/

private theorem leValue_append : ∀ (xs ys : List Nat),
    DY.X25519.leValue (xs ++ ys) =
      DY.X25519.leValue xs + 256 ^ xs.length * DY.X25519.leValue ys
  | [], ys => by simp [DY.X25519.leValue]
  | x :: xs, ys => by
    simp only [List.cons_append, DY.X25519.leValue, leValue_append xs ys,
      List.length_cons, Nat.pow_succ']
    rw [Nat.mul_assoc]
    omega

private theorem leValue_lt_or_eq_replicate : ∀ (xs : HwBytes),
    DY.X25519.leValue (xs.map BitVec.toNat) < 256 ^ xs.length - 1 ∨
    (DY.X25519.leValue (xs.map BitVec.toNat) = 256 ^ xs.length - 1 ∧
      toU8 xs = List.replicate xs.length 0xFF)
  | [] => Or.inr ⟨rfl, rfl⟩
  | x :: xs => by
    have hx : x.toNat < 256 := x.isLt
    have hpow : 1 ≤ 256 ^ xs.length := Nat.one_le_pow _ _ (by decide)
    rcases leValue_lt_or_eq_replicate xs with hlt | ⟨heq, hrep⟩
    · left
      simp only [List.map_cons, DY.X25519.leValue, List.length_cons, Nat.pow_succ']
      omega
    · by_cases hx255 : x.toNat = 255
      · right
        have hu8 : UInt8.ofBitVec x = 0xFF :=
          UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hx255)
        simp only [List.map_cons, DY.X25519.leValue, List.length_cons, Nat.pow_succ',
          toU8, heq, hx255, hu8, List.replicate_succ]
        exact ⟨by omega, congrArg (0xFF :: ·) hrep⟩
      · left
        simp only [List.map_cons, DY.X25519.leValue, List.length_cons, Nat.pow_succ', heq]
        omega

private theorem nibble_high_bit_zero : ∀ (hi lo : Fin 16),
    ((hi.val * 16 + lo.val) &&& 128 == 0) = true →
    hi.val * 16 + lo.val ≤ 127 ∧
      (((hi.val * 16 + lo.val) &&& 127 == 127) = true ↔ hi.val * 16 + lo.val = 127) := by
  decide

private theorem bv8_high_bit_zero (b31 : BitVec 8)
    (h : ((UInt8.ofBitVec b31 &&& 0x80) == 0) = true) :
    b31.toNat ≤ 127 ∧
      (((UInt8.ofBitVec b31 &&& 0x7F) == 0x7F) = true ↔ b31.toNat = 127) := by
  have hb : b31 &&& 0x80#8 = 0#8 := congrArg UInt8.toBitVec (beq_iff_eq.mp h)
  have hlt : b31.toNat < 256 := b31.isLt
  have hdiv : (b31.toNat / 16) * 16 + b31.toNat % 16 = b31.toNat := by omega
  have h128 : (((b31.toNat / 16) * 16 + b31.toNat % 16) &&& 128 == 0) = true := by
    rw [hdiv]
    apply beq_iff_eq.mpr
    simpa [BitVec.toNat_and] using congrArg BitVec.toNat hb
  obtain ⟨hle, hiff⟩ :=
    nibble_high_bit_zero ⟨b31.toNat / 16, by omega⟩ ⟨b31.toNat % 16, by omega⟩ h128
  rw [hdiv] at hle hiff
  refine ⟨hle, ⟨fun h7f => ?_, fun h127 => ?_⟩⟩
  · have h1 : b31 &&& 0x7F#8 = 0x7F#8 := congrArg UInt8.toBitVec (beq_iff_eq.mp h7f)
    have h1_nat : (b31.toNat &&& 127 == 127) = true := by
      apply beq_iff_eq.mpr
      simpa [BitVec.toNat_and] using congrArg BitVec.toNat h1
    exact hiff.mp h1_nat
  · have hbv : b31 = 0x7F#8 := BitVec.eq_of_toNat_eq h127
    subst hbv; rfl

private theorem bv8_ge_0xed_iff (b0 : BitVec 8) :
    decide (UInt8.ofBitVec b0 ≥ 0xED) = true ↔ 237 ≤ b0.toNat :=
  decide_eq_true_iff

theorem leValue_lt_p25519_of_scalarIsInRange (b : HwBytes)
    (hb : b.length = 32) (hrange : SignalPqxdh.scalarIsInRange (toU8 b) = true) :
    DY.X25519.leValue (b.map BitVec.toNat) < DY.X25519.p25519 := by
  cases b with
  | nil => cases hb
  | cons b0 bs =>
    have hbs_len : bs.length = 31 := Nat.succ.inj hb
    let mid := bs.take 30
    let tl := bs.drop 30
    have hmid_len : mid.length = 30 := by simp [mid, hbs_len]
    have htl_len : tl.length = 1 := by simp [tl, hbs_len]
    cases htl : tl with
    | nil => rw [htl] at htl_len; cases htl_len
    | cons b31 tl' =>
      cases tl' with
      | cons _ _ => rw [htl] at htl_len; cases htl_len
      | nil =>
        have hbs_eq : bs = mid ++ [b31] := by
          have h := (List.take_append_drop 30 bs).symm
          rwa [show bs.take 30 = mid from rfl, show bs.drop 30 = tl from rfl, htl] at h
        rw [hbs_eq] at hrange ⊢
        have htoU8 : toU8 (b0 :: (mid ++ [b31])) =
            UInt8.ofBitVec b0 :: (toU8 mid ++ [UInt8.ofBitVec b31]) := by
          simp [toU8]
        have hmid_u8_len : (toU8 mid).length = 30 := by rw [toU8_length_rpnmba1, hmid_len]
        have hget0 : (toU8 (b0 :: (mid ++ [b31]))).getD 0 0 = UInt8.ofBitVec b0 := rfl
        have hdrop1 : ((toU8 (b0 :: (mid ++ [b31]))).drop 1).take 30 = toU8 mid := by
          rw [htoU8, List.drop_succ_cons, List.drop_zero,
            List.take_append_of_le_length (Nat.le_of_eq hmid_u8_len.symm),
            List.take_of_length_le (Nat.le_of_eq hmid_u8_len)]
        have hget31 : (toU8 (b0 :: (mid ++ [b31]))).getD 31 0 = UInt8.ofBitVec b31 := by
          rw [htoU8, ← List.cons_append]
          have hlen31 : (UInt8.ofBitVec b0 :: toU8 mid).length = 31 := by simp [hmid_u8_len]
          rw [← hlen31]
          simp [List.getD]
        unfold SignalPqxdh.scalarIsInRange at hrange
        rw [hget0, hdrop1, hget31, Bool.and_eq_true, Bool.not_eq_true'] at hrange
        obtain ⟨hb31_hi, hnot_ge⟩ := hrange
        obtain ⟨hb31_le, hb31_7f_iff⟩ := bv8_high_bit_zero b31 hb31_hi
        have hb0_lt : b0.toNat < 256 := b0.isLt
        have hle_val : DY.X25519.leValue ((b0 :: (mid ++ [b31])).map BitVec.toNat) =
            b0.toNat + 256 * (DY.X25519.leValue (mid.map BitVec.toNat) + 256 ^ 30 * b31.toNat) := by
          simp only [List.map_cons, List.map_append, List.map_nil, DY.X25519.leValue,
            leValue_append, List.length_map, hmid_len, Nat.mul_zero, Nat.add_zero]
        rw [hle_val]
        unfold DY.X25519.p25519
        rcases leValue_lt_or_eq_replicate mid with hmid_lt | ⟨hmid_eq, hmid_rep⟩
        · rw [hmid_len] at hmid_lt; omega
        · rw [hmid_len] at hmid_eq hmid_rep
          by_cases hb31_127 : b31.toNat = 127
          · have h7f : ((UInt8.ofBitVec b31 &&& 0x7F) == 0x7F) = true := hb31_7f_iff.mpr hb31_127
            have hrep_beq : (toU8 mid == List.replicate 30 0xFF) = true := beq_iff_eq.mpr hmid_rep
            rw [hrep_beq, h7f, Bool.and_true, Bool.and_true] at hnot_ge
            have hb0_not_ge : ¬ (237 ≤ b0.toNat) := fun hge => by
              rw [(bv8_ge_0xed_iff b0).mpr hge] at hnot_ge; cases hnot_ge
            omega
          · omega

/-- Extracts `< p25519` range and `X25519TorsionFree` from `(modelPrims X P).isCanonical`. -/
theorem isCanonical_modelPrims_inv {interp : ExternInterpretation} {P : PEParams}
    (hAgree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives) (v : List.Vector (BitVec 8) 32)
    (hcanon : (modelPrims X P).isCanonical (vecU8 v) = true) :
    DY.X25519.leValue (v.toList.map BitVec.toNat) < DY.X25519.p25519 ∧
      X25519TorsionFree interp v.toList := by
  change SignalPqxdh.isCanonicalRef _ (vecU8 v) = true at hcanon
  unfold SignalPqxdh.isCanonicalRef at hcanon
  split at hcanon
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    have hlt : DY.X25519.leValue (v.toList.map BitVec.toNat) < DY.X25519.p25519 :=
      leValue_lt_p25519_of_scalarIsInRange v.toList v.toList_length hcond.2
    refine ⟨hlt, ?_⟩
    change (match ((P.Q.montToEd (u8Vec 32 (vecU8 v)) (0 : UInt8).toBitVec).map vecU8) with
      | some edPt => P.Q.isTorsionFree (u8Vec 160 edPt)
      | none => false) = true at hcanon
    rw [u8Vec_vecU8_rpnmba1] at hcanon
    have hz : (0 : UInt8).toBitVec = 0#8 := rfl
    rw [hz] at hcanon
    cases hm : P.Q.montToEd v 0#8 with
    | none => rw [hm] at hcanon; cases hcanon
    | some pt =>
      rw [hm] at hcanon
      dsimp only [Option.map] at hcanon
      rw [u8Vec_vecU8_rpnmba1] at hcanon
      have hmont : interp toEdwardsSymbol [v.toList, [0#8]] =
          (P.Q.montToEd v 0#8).map List.Vector.toList :=
        hAgree.2.2.2.2.2.2.2.1 v 0#8
      rw [hm, Option.map_some] at hmont
      have htf : P.Q.isTorsionFree pt = decide (interp torsionFreeSymbol [pt.toList] = some [1#8]) :=
        hAgree.2.2.2.2.2.2.2.2 pt
      rw [hcanon] at htf
      exact ⟨pt.toList, pt.toList_length, hmont, decide_eq_true_eq.mp htf.symm⟩
  · cases hcanon

/-! ## Model Primitive Bridges -/

theorem clampScalar_bytesToVec_toList {b : HwBytes} (hb : b.length = 32) :
    (Ratchet.clampScalar (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 b)).toList = clamp b := by
  rw [clampScalar_toList_eq_clamp_toList, bytesToVec_toList_local hb]

theorem x25519_modelPrims_keyPairOf_bytesToVec {interp : ExternInterpretation} {P : PEParams}
    (hAgree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives)
    {skBytes : HwBytes} (hsk : skBytes.length = 32)
    (pk : List.Vector (BitVec 8) 32) :
    ofU8 ((modelPrims X P).x25519
      (vecU8 (keyPairOf P.C (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 skBytes)).privateKey.bytes)
      (vecU8 pk)) =
      dhAgreeBytes interp skBytes pk.toList := by
  change ofU8 (vecU8 (P.C.X
    (Ratchet.clampScalar (u8Vec 32 (vecU8 (Ratchet.clampScalar
      (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 skBytes)))))
    (u8Vec 32 (vecU8 pk)))) = _
  rw [u8Vec_vecU8_rpnmba1, u8Vec_vecU8_rpnmba1, clampScalar_idem_pure, ofU8_vecU8_rpnmba1]
  have hx := hAgree.2.2.2.1
    (Ratchet.clampScalar (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 skBytes)) pk
  rw [clampScalar_bytesToVec_toList hsk] at hx
  unfold dhAgreeBytes
  rw [hx]; rfl

theorem kemDecaps_modelPrims_bob_bytesToVec {interp : ExternInterpretation} {P : PEParams}
    (hAgree : ModelAgree interp P) {r : ProtocolSetup} (hr : ProtocolSetupWF r) (X : UnreachedPqxdhPrimitives)
    (ct : List.Vector (BitVec 8) 1568) :
    ((modelPrims X P).kemDecaps
      (vecU8 (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 3168 (r.kyberSecB.drop 1)))
      (vecU8 ct)).map ofU8 =
      some ((kyberDecapsBytes interp r ct.toList).getD []) := by
  let kpkSec := Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 3168 (r.kyberSecB.drop 1)
  have hctLen : ((vecU8 ct).length == SignalPqxdh.kyberCtLen) = true := by
    simp [vecU8, toU8, SignalPqxdh.kyberCtLen]
  change (if (vecU8 ct).length == SignalPqxdh.kyberCtLen then
    some (vecU8 (P.Q.decaps (u8Vec 3168 (vecU8 kpkSec)) (u8Vec SignalPqxdh.kyberCtLen (vecU8 ct))))
    else none).map ofU8 = _
  simp only [hctLen, ↓reduceIte]
  change (some (vecU8 (P.Q.decaps (u8Vec 3168 (vecU8 kpkSec)) (u8Vec 1568 (vecU8 ct))))).map ofU8 = _
  rw [u8Vec_vecU8_rpnmba1, u8Vec_vecU8_rpnmba1, Option.map_some, ofU8_vecU8_rpnmba1]
  have hkdrop_len : (r.kyberSecB.drop 1).length = 3168 := by simp [hr.2.2.2.2.2.2.1]
  have hdrop : r.kyberSecB.drop 1 = kpkSec.toList :=
    (bytesToVec_toList_local hkdrop_len).symm
  have hk : interp kyberDecapsSymbol [kpkSec.toList, ct.toList] =
      some (P.Q.decaps kpkSec ct).toList :=
    hAgree.2.2.2.2.2.2.1 kpkSec ct
  unfold kyberDecapsBytes
  rw [hdrop, hk]
  rfl

end Symbolic.Swarm.CREF.Cli.Slots
