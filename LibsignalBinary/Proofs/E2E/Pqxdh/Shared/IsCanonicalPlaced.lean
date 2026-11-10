/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable Per-Block Proof for `<PublicKey>::is_canonical` (Block `202`)

Proves relocatable contracts for mutated Block `202`
(`<libsignal_core::curve::PublicKey>::is_canonical`) under `[LibsignalFullPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open SignalPqxdh

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Mangled Curve25519-Dalek Hook Symbols -/

abbrev lsDalekMontToEdSym : String :=
  "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"

abbrev lsDalekTorsionFreeSym : String :=
  "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free"

/-! ## Image-Free Dalek and SHA-512 Hook Specifications -/

def compressInPlaceStubSpecPlaced (fn : Bytes → Bytes → Bytes) (stateLen blockLen : Nat) :
    Spec CryptoCompressGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      s.readReg64 .x1 = g.blocksPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.nBlocks ∧
      g.nBlocks < 2 ^ 64 ∧
      g.stateBytes.length = stateLen ∧
      g.blockBytes.length = blockLen * g.nBlocks⌝ ∗
      (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.statePtr ↦ₛ fitBv8 stateLen (fn g.stateBytes g.blockBytes)) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s0.sp pqxdhHookStack

def dalekMontToEdStubSpecPlaced (P : Primitives) :
    Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr 168 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗
      stackAt s0.sp pqxdhHookStack

def dalekDoubleMulStubSpecPlaced (P : Primitives) :
    Spec DalekDoubleMulGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.hPtr ∧
      s.readReg64 .x1 = g.negAPtr ∧
      s.readReg64 .x2 = g.sPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.hBytes.length = 32 ∧
      g.negABytes.length = 160 ∧
      g.sBytes.length = 32⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      memRegion g.outPtr 160 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      (g.outPtr ↦ₛ fitBv8 160 (P.doubleScalarMulBasepoint g.hBytes g.negABytes g.sBytes)) ∗
      stackAt s0.sp pqxdhHookStack

/-! ## Memory, Scalar-Range, and `SepWP` Normalization Helpers -/

private theorem memRegion168_of_cell_and_memRegion160 (a : BitVec 64) (v : BitVec 64)
    (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (a + 8#64) bs
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h2)) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion160_of_bytes160 (a : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦ₛ bs) ∗ R_tail ⊢ memRegion a 160 ∗ R_tail := by
  have h1 : (a ↦ₛ bs) ⊢ memRegion a 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion a bs
  exact sepConj_mono_left h1

private theorem exists_unpack64_of_length_160 {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a R_tail,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1 ∗ ((a + 16#64) ↦₆₄ w2 ∗ ((a + 24#64) ↦₆₄ w3 ∗
        ((a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5 ∗ ((a + 48#64) ↦₆₄ w6 ∗ ((a + 56#64) ↦₆₄ w7 ∗
        ((a + 64#64) ↦₆₄ w8 ∗ ((a + 72#64) ↦₆₄ w9 ∗ ((a + 80#64) ↦₆₄ w10 ∗ ((a + 88#64) ↦₆₄ w11 ∗
        ((a + 96#64) ↦₆₄ w12 ∗ ((a + 104#64) ↦₆₄ w13 ∗ ((a + 112#64) ↦₆₄ w14 ∗
        ((a + 120#64) ↦₆₄ w15 ∗ ((a + 128#64) ↦₆₄ w16 ∗ ((a + 136#64) ↦₆₄ w17 ∗
        ((a + 144#64) ↦₆₄ w18 ∗ ((a + 152#64) ↦₆₄ w19 ∗
         R_tail))))))))))))))))))) =
        (a ↦ₛ bs) ∗ R_tail := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, fun a R_tail => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++
      ((bs.drop 64).take 32 ++ ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3
    rw [s3] at s2
    rw [s2] at s1
    exact s1
  symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0,
    pointsToBytes_append, h1, hp1,
    pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sepWP_memRegion160_head {prog : Program} {ret : BitVec 64} {s : State}
    (a : BitVec 64) {P_pre F_rest : SepProp}
    (heq : P_pre = memRegion a 160 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 : BitVec 64,
      SepWP prog ret s
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1 ∗ ((a + 16#64) ↦₆₄ u2 ∗ ((a + 24#64) ↦₆₄ u3 ∗
        ((a + 32#64) ↦₆₄ u4 ∗ ((a + 40#64) ↦₆₄ u5 ∗ ((a + 48#64) ↦₆₄ u6 ∗ ((a + 56#64) ↦₆₄ u7 ∗
        ((a + 64#64) ↦₆₄ u8 ∗ ((a + 72#64) ↦₆₄ u9 ∗ ((a + 80#64) ↦₆₄ u10 ∗ ((a + 88#64) ↦₆₄ u11 ∗
        ((a + 96#64) ↦₆₄ u12 ∗ ((a + 104#64) ↦₆₄ u13 ∗ ((a + 112#64) ↦₆₄ u14 ∗
        ((a + 120#64) ↦₆₄ u15 ∗ ((a + 128#64) ↦₆₄ u16 ∗ ((a + 136#64) ↦₆₄ u17 ∗
        ((a + 144#64) ↦₆₄ u18 ∗ ((a + 152#64) ↦₆₄ u19 ∗
         F_rest)))))))))))))))))))) Q) :
    SepWP prog ret s P_pre Q := by
  rw [heq, memRegion_eq_exists_bytes a 160 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen => ?_
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15,
    u16, u17, u18, u19, hbs⟩ :=
    exists_unpack64_of_length_160 hlen
  rw [← hbs a F_rest]
  exact h u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19

private theorem bytesToBv8_getD (bs : Bytes) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = (bs.getD i 0).toBitVec := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero => rcases b with ⟨⟨val, isLt⟩⟩; simp [bytesToBv8]
    | succ j => exact ih j

private theorem uint8_getLsbD7_eq_true_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = true ↔ ((b &&& 0x80) == 0) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_getLsbD7_eq_false_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = false ↔ ((b &&& 0x80) == 0) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_true_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = true ↔ decide (b ≥ 0xED) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_false_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = false ↔ decide (b ≥ 0xED) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_b31_7f_eq (b : UInt8) (h7 : ((b &&& 0x80) == 0) = true) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b.toBitVec) == 127#32) = ((b &&& 0x7F) == 0x7F) := by
  rcases b with ⟨bv⟩
  revert bv h7; decide

private theorem uint8_toBitVec_eq_ff_iff (b : UInt8) :
    (b.toBitVec = 0xff#8) ↔ (b = 0xFF) := by
  rcases b with ⟨bv⟩
  constructor
  · intro h; subst h; rfl
  · intro h; exact congrArg UInt8.toBitVec h

private theorem bv64_add1_eq_zero_iff (x : BitVec 64) :
    (x + 1#64 == 0#64) = (x == 0xffffffffffffffff#64) := by
  bv_bits

private theorem bv64_allOnes_getElem (i : Nat) (hi : i < 64) :
    (0xffffffffffffffff#64 : BitVec 64)[i] = true := by
  revert i hi; decide

private theorem bv64_and_eq_allOnes_iff (a b : BitVec 64) :
    (a &&& b = 0xffffffffffffffff#64) ↔
      (a = 0xffffffffffffffff#64 ∧ b = 0xffffffffffffffff#64) := by
  constructor
  · intro h
    constructor
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.1
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.2
  · rintro ⟨rfl, rfl⟩; rfl

private theorem pack64_eq_allOnes_iff (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 = 0xffffffffffffffff#64) ↔
      (b0 = 0xff#8 ∧ b1 = 0xff#8 ∧ b2 = 0xff#8 ∧ b3 = 0xff#8 ∧
       b4 = 0xff#8 ∧ b5 = 0xff#8 ∧ b6 = 0xff#8 ∧ b7 = 0xff#8) := by
  unfold pack64
  bv_bits

private theorem list_take_drop_succ (xs : List UInt8) (i n : Nat) (hi : i < xs.length) :
    (xs.drop i).take (n + 1) = xs.getD i 0 :: (xs.drop (i + 1)).take n := by
  have hget : xs.getD i 0 = xs[i] := by simp [List.getD, hi]
  rw [List.drop_eq_getElem_cons hi, ← hget]
  rfl

private theorem list32_drop1_take30_eq (xs : List UInt8) (h : xs.length = 32) :
    (xs.drop 1).take 30 =
      [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] := by
  repeat (rw [list_take_drop_succ _ _ _ (by omega)])
  rfl

private theorem list32_drop1_take30_eq_replicate_iff (xs : List UInt8) (h : xs.length = 32) :
    ((xs.drop 1).take 30 == List.replicate 30 0xFF) = true ↔
      (xs.getD 1 0 = 0xFF ∧ xs.getD 2 0 = 0xFF ∧ xs.getD 3 0 = 0xFF ∧ xs.getD 4 0 = 0xFF ∧
       xs.getD 5 0 = 0xFF ∧ xs.getD 6 0 = 0xFF ∧ xs.getD 7 0 = 0xFF ∧ xs.getD 8 0 = 0xFF ∧
       xs.getD 9 0 = 0xFF ∧ xs.getD 10 0 = 0xFF ∧ xs.getD 11 0 = 0xFF ∧ xs.getD 12 0 = 0xFF ∧
       xs.getD 13 0 = 0xFF ∧ xs.getD 14 0 = 0xFF ∧ xs.getD 15 0 = 0xFF ∧ xs.getD 16 0 = 0xFF ∧
       xs.getD 17 0 = 0xFF ∧ xs.getD 18 0 = 0xFF ∧ xs.getD 19 0 = 0xFF ∧ xs.getD 20 0 = 0xFF ∧
       xs.getD 21 0 = 0xFF ∧ xs.getD 22 0 = 0xFF ∧ xs.getD 23 0 = 0xFF ∧ xs.getD 24 0 = 0xFF ∧
       xs.getD 25 0 = 0xFF ∧ xs.getD 26 0 = 0xFF ∧ xs.getD 27 0 = 0xFF ∧ xs.getD 28 0 = 0xFF ∧
       xs.getD 29 0 = 0xFF ∧ xs.getD 30 0 = 0xFF) := by
  rw [beq_iff_eq, list32_drop1_take30_eq xs h]
  change [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] =
      [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ↔ _
  simp only [List.cons.injEq, and_true]

private theorem pack64_4_allOnes_eq_drop1_take30 (keyBytes : Bytes) (h : keyBytes.length = 32) :
    ((pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
              ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
              ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
              ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
              ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
              ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
              ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
          (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
              ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
              ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
              ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
              ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
              ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
              ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
        1#64 == 0#64) =
      ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) := by
  rw [bv64_add1_eq_zero_iff]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff,
    pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff,
    list32_drop1_take30_eq_replicate_iff keyBytes h]
  simp only [bytesToBv8_getD, uint8_toBitVec_eq_ff_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
            ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨_, _, h25, h26, h27, h28, h29, h30⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
           h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
            h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
    exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
           ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨h23, h24, h25, h26, h27, h28, h29, h30⟩⟩

private theorem ecPubKeyIsCanonical_tail_eq (P : Primitives) (keyBytes edPt : Bytes)
    (h : keyBytes.length = 32)
    (hmont : P.montToEd keyBytes 0 = some edPt)
    (htors : P.isTorsionFree edPt = true)
    (hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true) :
    (if isCanonicalRef P keyBytes = true then (1#8 : BitVec 8) else 0#8) =
      BitVec.setWidth 8
        (if
          (if (BitVec.truncate 32
              (BitVec.signExtend 64 ((bytesToBv8 keyBytes).getD 31 0#8)) == 127#32) = true then
            (pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
                      ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
                      ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
                      ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
                      ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
                      ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
                      ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
                  (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
                      ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
                      ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
                      ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
                      ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
                      ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
                      ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
                1#64 ==
              0#64
          else false) =
            true then
          (0#64 : BitVec 64)
        else 1#64) := by
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
  rw [pack64_4_allOnes_eq_drop1_take30 keyBytes h, bytesToBv8_getD keyBytes 31,
    uint8_b31_7f_eq (keyBytes.getD 31 0) hb31_u8]
  simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
  cases ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) <;>
    cases ((keyBytes.getD 31 0 &&& 0x7F) == 0x7F) <;> rfl

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) :
    @_root_.ite State c inst ((s.setPState ps1).setPC pc) ((s.setPState ps2).setPC pc) =
      (s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC_setMem (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) (m : Memory) :
    @_root_.ite State c inst (((s.setPState ps1).setPC pc).setMem m)
      (((s.setPState ps2).setPC pc).setMem m) =
      ((s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc).setMem m := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem ConditionHolds_ite (cond : CondCode) (c : Prop) [inst : Decidable c]
    (ps1 ps2 : PState) :
    ConditionHolds cond (@_root_.ite PState c inst ps1 ps2) =
      @_root_.ite Bool c inst (ConditionHolds cond ps1) (ConditionHolds cond ps2) := by
  by_cases hc : c <;> simp [hc]

/-! ## Block `202`: `<libsignal_core::curve::PublicKey>::is_canonical` -/

set_option maxHeartbeats 1200000 in
/-- Image-free relocatable `<libsignal_core::curve::PublicKey>::is_canonical` (Block `202`, mutated)
meets `ecPubKeyIsCanonicalCallSpec P` under `[LibsignalFullPlacement]`. -/
theorem isCanonical_placed_ok'_placed [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpec P) := by
  unfold ecPubKeyIsCanonicalCallSpec
  simp only [stackAt_ecPubKeyIsCanonical_call]
  cells_unfold
  have hmont_call : subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (lsρ lsDalekMontToEdSym) (dalekMontToEdStubSpecPlaced P) :=
    ls_hook_ok_any hmontHook
  have htors_call : subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (lsρ lsDalekTorsionFreeSym) (cryptoBoolRegStubSpec P.isTorsionFree 160) :=
    ls_hook_ok_any htorsHook
  clear hmontHook htorsHook
  wp_init g s0
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hcanon_eq : P.isCanonicalEC keyBytes = isCanonicalRef P keyBytes :=
    hisCanon keyBytes
  rw [hcanon_eq]
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 hlen_bv
  have hpk_sp_tail (R_tail : SepProp) :
      (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗
      ((s0.sp - 384#64) ↦₆₄ w2 ∗ ((s0.sp - 376#64) ↦₆₄ w3 ∗ R_tail))) =
      (s0.sp - 400#64) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    have hpk_sp := hpk_cells (s0.sp - 400#64)
    have ha1 : s0.sp - 400#64 + 8#64 = s0.sp - 392#64 := by bv_arith
    have ha2 : s0.sp - 400#64 + 16#64 = s0.sp - 384#64 := by bv_arith
    have ha3 : s0.sp - 400#64 + 24#64 = s0.sp - 376#64 := by bv_arith
    rw [ha1, ha2, ha3] at hpk_sp
    rw [hpk_sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  have hpk_reg0_tail (R_tail : SepProp) :
      s0.readReg64 (Reg.gpr 0#5) ↦₆₄ w0 ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3 ∗ R_tail))) =
      s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5)), sepConj_assoc, sepConj_assoc, sepConj_assoc]
  wp_conv_pre => rw [← hpk_reg0_tail]
  wp_steps
  wp_conv_pre => rw [hpk_reg0_tail, hpk_sp_tail]
  wp_call hmont_call ⟨keyBytes, 0, s0.sp - 400#64, s0.sp - 360#64⟩
  wp_conv_pre => rw [show (0 : UInt8) &&& 1 = 0 from rfl, ← hpk_sp_tail]
  cases hmont : P.montToEd keyBytes 0 with
  | none =>
    have hcanon_none : isCanonicalRef P keyBytes = false := by
      simp [isCanonicalRef, hmont]
    rw [hcanon_none]
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_none P keyBytes 0 hmont (s0.sp - 360#64), sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (memRegion168_of_cell_and_memRegion160 (s0.sp - 360#64) 0#64 _))))) ?_
    wp_done
  | some edPt =>
    have hed_len : edPt.length = 160 := hmontLen keyBytes 0 edPt hmont
    have hed_bv_len : (bytesToBv8 edPt).length = 160 := by simp [bytesToBv8, hed_len]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
      e16, e17, e18, e19, hed_cells⟩ :=
      exists_unpack64_of_length_160 hed_bv_len
    refine sepWP_memRegion160_head (s0.sp - 192#64)
      (F_rest := (s0.sp - 400#64) ↦₆₄ w0 ∗
        ((s0.sp - 392#64) ↦₆₄ w1 ∗
          ((s0.sp - 384#64) ↦₆₄ w2 ∗
            ((s0.sp - 376#64) ↦₆₄ w3 ∗
              (dalekMontToEdOutAt P (s0.sp - 360#64) keyBytes 0 ∗
                (stackAt (s0.sp - 400#64) pqxdhHookStack ∗
                  (s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗
                    (memRegion (s0.sp - 368#64) 8 ∗
                        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                              (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))))))
      (by ac_rfl)
      fun u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 => ?_
    wp_conv_pre =>
      rw [dalekMontToEdOutAt_some P keyBytes edPt 0 hmont hed_len (s0.sp - 360#64),
        sepConj_assoc ((s0.sp - 360#64) ↦₆₄ 1#64),
        ← hed_cells (s0.sp - 360#64 + 8#64)]
    wp_steps
    wp_conv_pre =>
      rw [hed_cells (s0.sp - 192#64), hed_cells (s0.sp - 360#64 + 8#64)]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (memRegion168_of_cell_and_bytes160
          (s0.sp - 360#64) 1#64 hed_bv_len _)))))) ?_
    wp_call htors_call ⟨s0.sp - 192#64, edPt⟩
    refine SepWP.weaken_pre (memRegion160_of_bytes160 (s0.sp - 192#64) hed_bv_len _) ?_
    cases htors : P.isTorsionFree edPt with
    | false =>
      have hcanon_false : isCanonicalRef P keyBytes = false := by
        simp [isCanonicalRef, hmont, htors]
      rw [hcanon_false]
      simp only [htors, Bool.false_eq_true, ite_false] at hpost_1
      have hx0_8 : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#8 := by
        revert hpost_1; bv_bits
      wp_steps
      wp_done
    | true =>
      simp only [htors, ite_true] at hpost_1
      have hfocus8 (off : Nat) (hoff : off < 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₈
              (bytesToBv8 keyBytes).getD off 0#8) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 1)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 1) ∗ R_tail)) := by
        rw [pointsToBytes_focus8 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      have hfocus64 (off : Nat) (hoff : off + 8 ≤ 32) (R_tail : SepProp) :
          s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
            ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₆₄
              pack64 ((bytesToBv8 keyBytes).getD off 0#8) ((bytesToBv8 keyBytes).getD (off + 1) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 2) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 3) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 4) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 5) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 6) 0#8)
                ((bytesToBv8 keyBytes).getD (off + 7) 0#8)) ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 8)) ↦ₛ
              (bytesToBv8 keyBytes).drop (off + 8) ∗ R_tail)) := by
        rw [pointsToBytes_focus64 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
            (by rw [hlen_bv]; exact hoff),
          sepConj_assoc, sepConj_assoc]
      wp_conv_pre => rw [hfocus8 31 (by decide)]
      wp_steps
      wp_conv_pre => rw [← hfocus8 31 (by decide)]
      cases hb31 : ((bytesToBv8 keyBytes).getD 31 0#8).getLsbD 7 with
      | true =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_true_iff _).mp hb31
        have hcanon_b31 : isCanonicalRef P keyBytes = false := by
          unfold isCanonicalRef; rw [hb31_u8]; simp
        rw [hcanon_b31]
        simp only [beq_self_eq_true, ite_true]
        wp_steps
        wp_done
      | false =>
        have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true := by
          rw [bytesToBv8_getD] at hb31
          exact (uint8_getLsbD7_eq_false_iff _).mp hb31
        simp only [beq_iff_eq, Bool.false_eq_true, ite_false]
        wp_conv_pre => rw [hfocus8 0 (by decide)]
        wp_steps
        wp_conv_pre => rw [← hfocus8 0 (by decide)]
        cases hb0 : (BitVec.zeroExtend 64 ((bytesToBv8 keyBytes).getD 0 0#8)).ult 237#64 with
        | true =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = false := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_true_iff _).mp hb0
          have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
          have hcanon_b0 : isCanonicalRef P keyBytes = true := by
            simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
            rfl
          rw [hcanon_b0]
          simp only [ite_true]
          wp_steps
          wp_done
        | false =>
          have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true := by
            rw [bytesToBv8_getD] at hb0
            exact (uint8_ult237_eq_false_iff _).mp hb0
          simp only [Bool.false_eq_true, ite_false]
          wp_conv_pre => rw [hfocus64 1 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 1 (by decide), hfocus64 9 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 9 (by decide), hfocus64 17 (by decide)]
          wp_step
          wp_conv_pre => rw [← hfocus64 17 (by decide), hfocus64 23 (by decide)]
          wp_steps
          wp_conv_pre => rw [← hfocus64 23 (by decide)]
          rw [ecPubKeyIsCanonical_tail_eq P keyBytes edPt h hmont htors hb31_u8 hb0_u8]
          wp_done

theorem isCanonical_placed_ok_placed [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpec P) :=
  isCanonical_placed_ok'_placed hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len hmontHook htorsHook

theorem isCanonical_placed_ok'_cl_placed [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_placed_ok'_placed hisCanon hmontLen hmontHook htorsHook)

theorem isCanonical_placed_ok_cl_placed [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpecPlaced P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  full_ls_subroutine_ok_of_plain (j := 202) (isCanonical_placed_ok_placed hWF hmontHook htorsHook)

/-- Relocatable `<libsignal_core::curve::PublicKey>::is_canonical` (Block `202`, mutated)
meets `ecPubKeyIsCanonicalCallSpec P` under `[LibsignalFullPlacement]`. -/
theorem isCanonical_placed_ok' [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpec P) :=
  isCanonical_placed_ok'_placed hisCanon hmontLen hmontHook htorsHook

theorem isCanonical_placed_ok [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H)
      (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpec P) :=
  isCanonical_placed_ok_placed hWF hmontHook htorsHook

theorem isCanonical_placed_ok'_cl [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  isCanonical_placed_ok'_cl_placed hisCanon hmontLen hmontHook htorsHook

theorem isCanonical_placed_ok_cl [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  isCanonical_placed_ok_cl_placed hWF hmontHook htorsHook

abbrev ecPubKeyIsCanonical_placed_ok' [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hisCanon : ∀ k, P.isCanonicalEC k = isCanonicalRef P k)
    (hmontLen : ∀ u s ed, P.montToEd u s = some ed → ed.length = 160)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :=
  isCanonical_placed_ok' hisCanon hmontLen hmontHook htorsHook

abbrev ecPubKeyIsCanonical_placed_ok [LibsignalFullPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :=
  isCanonical_placed_ok hWF hmontHook htorsHook

end CryptoVerification.E2E.Pqxdh.Shared
