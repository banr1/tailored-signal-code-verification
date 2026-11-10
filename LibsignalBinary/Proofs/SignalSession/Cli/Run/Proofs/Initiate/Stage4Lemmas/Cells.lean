/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit

/-!
# Stage 4 Precondition Monotonicity and Byte/Cell Packing Helpers

Precondition rewriting (`sepWPp_mono_pre`, `sepWP_mono_pre`) and 64-bit word / byte-slice
split-and-pack lemmas for `hkSlotBytes` (`100` B), `32`-byte keys, `36`-byte `ChainKey`s,
`40`-byte SPQR `Params`, `72`-byte `create_chain` `Err` srets, and `344`-byte `SessionState`
copies.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

structure Hide (P : Prop) : Prop where
  val : P

@[simp, arm64_norm, wp_norm]
theorem s4_extract_lo64_zero : (0#128).extractLsb' 0 64 = 0#64 := rfl

@[simp, arm64_norm, wp_norm]
theorem s4_extract_hi64_zero : (0#128).extractLsb' 64 64 = 0#64 := rfl

@[simp, arm64_norm, wp_norm]
theorem s4_extract_lo64_append (b a : BitVec 64) :
    (b ++ a).extractLsb' 0 64 = a := by
  ext i hi
  simp [hi]

@[simp, arm64_norm, wp_norm]
theorem s4_extract_hi64_append (b a : BitVec 64) :
    (b ++ a).extractLsb' 64 64 = b := by
  ext i hi
  have hlt : ¬ (64 + i < 64) := by omega
  simp [hi, hlt]

theorem sepWPp_mono_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {Qo : State → SepProp}
    (hent : P ⊢ P')
    (hwp : SepWPp prog target s P' Q Qp Qo) :
    SepWPp prog target s P Q Qp Qo := by
  intro R hm hL
  exact hwp R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWP_mono_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P ⊢ P')
    (hwp : SepWP prog target s P' post oom) :
    SepWP prog target s P post oom :=
  SepWP.weaken_pre hent hwp

@[simp, arm64_norm, wp_norm]
theorem cond_eq_adds_33_1 :
    ConditionHolds CondCode.EQ (addsPState64 33#64 1#64) = false := by
  simp only [ConditionHolds, addsPState64, AddWithCarry64]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_ne_subs_0_1 :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64, AddWithCarry64]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_lo_subs_0_3 :
    ConditionHolds CondCode.CC (subsPState64 0#64 3#64) = true := by
  simp only [ConditionHolds, subsPState64, AddWithCarry64]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_ne_subs32_0_1 :
    ConditionHolds CondCode.NE (subsPState32 0#32 1#32) = true := by
  simp only [ConditionHolds, subsPState32, AddWithCarry32]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_ne_subs32_1_1 :
    ConditionHolds CondCode.NE (subsPState32 1#32 1#32) = false := by
  simp only [ConditionHolds, subsPState32, AddWithCarry32]
  decide

theorem cells4_eq_memRegion32 (base : BitVec 64) :
    memRegion base 32 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) := by
  rw [(ProofLib.memRegion_cells base 4 (by decide) : memRegion base 32 = cells base 4)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem cells4_entails_memRegion32' (base w0 w1 w2 w3 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
    ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ⊢
      memRegion base 32 := by
  rw [cells4_eq_memRegion32 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

theorem cells3_eq_memRegion24 (base : BitVec 64) :
    memRegion base 24 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) := by
  rw [(ProofLib.memRegion_cells base 3 (by decide) : memRegion base 24 = cells base 3)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem cells3_entails_memRegion24 (base w0 w1 w2 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ⊢
      memRegion base 24 := by
  rw [cells3_eq_memRegion24 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.refl _)))

theorem cells7_eq_memRegion56 (base : BitVec 64) :
    memRegion base 56 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗
        ((base + 24#64) ↦₆₄ w3) ∗ ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ∗
        ((base + 48#64) ↦₆₄ w6) := by
  rw [(ProofLib.memRegion_cells base 7 (by decide) : memRegion base 56 = cells base 7)]
  simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem cells4_4_eq_memRegion36 (base : BitVec 64) :
    memRegion base 36 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ d4 : BitVec 32,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
        ((base + 32#64) ↦₃₂ d4) := by
  rw [ProofLib.memRegion_split' (b := base) (n := 32) (k := 4)
        (b' := base + 32#64) rfl (by bv_omega) (by decide),
      cells4_eq_memRegion32 base,
      ProofLib.memRegion_four (base + 32#64)]
  s4_exists_eq

theorem pointsTo64_4294967296_eq_pair32 (base : BitVec 64) :
    (base ↦₆₄ 4294967296#64) =
      (base ↦₃₂ 0#32) ∗ ((base + 4#64) ↦₃₂ 1#32) := by
  have hunpack : unpack64 4294967296#64 = unpack32 0#32 ++ unpack32 1#32 := by decide
  rw [pointsTo64_eq_pointsToBytes, hunpack, pointsToBytes_append]
  simp only [unpack32_length, ← pointsTo32_eq_pointsToBytes]

theorem createChainErr_5632_entails_memRegion72 (fsp e0 e1 e2 e3 e4 e5 : BitVec 64) :
    ((fsp + 5632#64) ↦₃₂ 1#32) ∗
    memRegion (fsp + 5636#64) 4 ∗
    ((fsp + 5640#64) ↦₆₄ e0) ∗
    ((fsp + 5648#64) ↦₆₄ e1) ∗
    ((fsp + 5656#64) ↦₆₄ e2) ∗
    ((fsp + 5664#64) ↦₆₄ e3) ∗
    ((fsp + 5672#64) ↦₆₄ e4) ∗
    ((fsp + 5680#64) ↦₆₄ e5) ∗
    memRegion (fsp + 5688#64) 16 ⊢
      memRegion (fsp + 5632#64) 72 := by
  have h4 : ((fsp + 5632#64) ↦₃₂ 1#32) ⊢ memRegion (fsp + 5632#64) 4 :=
    pointsTo32_entails_memRegion (fsp + 5632#64) 1#32
  have h48 := cells6_entails_memRegion48 (fsp + 5640#64) e0 e1 e2 e3 e4 e5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
  rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 4) (k := 68)
        (b' := fsp + 5636#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5636#64) (n := 4) (k := 64)
        (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 48) (k := 16)
        (b' := fsp + 5688#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono h4 (sepConj_mono_right (sepConj_mono_left h48)))

theorem pointsToBytes_split_56_288 (base : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 344) :
    (base ↦ₛ bs) =
      (base ↦ₛ bs.take 56) ∗ ((base + 56#64) ↦ₛ bs.drop 56) := by
  have heq : bs = bs.take 56 ++ bs.drop 56 := (List.take_append_drop 56 bs).symm
  have ht : (bs.take 56).length = 56 := by simp [hlen]
  conv => lhs; rw [heq]
  rw [pointsToBytes_append, ht]

theorem pointsToBytes_pack_56_288 (base : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 344) :
    (base ↦ₛ bs.take 56) ∗ ((base + 56#64) ↦ₛ bs.drop 56) =
      (base ↦ₛ bs) :=
  (pointsToBytes_split_56_288 base hlen).symm

theorem memRegion344_split_56_288 (base : BitVec 64) :
    memRegion base 344 =
      memRegion base 56 ∗ memRegion (base + 56#64) 288 :=
  ProofLib.memRegion_split' (b := base) (n := 56) (k := 288)
    (b' := base + 56#64) rfl (by bv_omega) (by decide)

theorem memRegion40_eq_cells5' (base : BitVec 64) :
    memRegion base 40 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗
        ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
        ((base + 32#64) ↦₆₄ w4) :=
  cells5_eq_memRegion40 base

theorem hkSlot100_unpack (base : BitVec 64) (rk pq ck : List (BitVec 8))
    {rk0 rk1 rk2 rk3 pq0 pq1 pq2 pq3 ck0 ck1 ck2 ck3 : BitVec 64}
    (hrk_cells : ∀ a, (a ↦ₛ rk) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hpq_cells : ∀ a, (a ↦ₛ pq) =
      (a ↦₆₄ pq0) ∗ ((a + 8#64) ↦₆₄ pq1) ∗ ((a + 16#64) ↦₆₄ pq2) ∗ ((a + 24#64) ↦₆₄ pq3))
    (hck_cells : ∀ a, (a ↦ₛ ck) =
      (a ↦₆₄ ck0) ∗ ((a + 8#64) ↦₆₄ ck1) ∗ ((a + 16#64) ↦₆₄ ck2) ∗ ((a + 24#64) ↦₆₄ ck3))
    (hrk : rk.length = 32) (hpq : pq.length = 32) (hck : ck.length = 32) :
    (base ↦ₛ (rk ++ pq ++ ck ++ unpack32 0#32)) =
      (base ↦₆₄ rk0) ∗ ((base + 8#64) ↦₆₄ rk1) ∗ ((base + 16#64) ↦₆₄ rk2) ∗
      ((base + 24#64) ↦₆₄ rk3) ∗
      ((base + 32#64) ↦₆₄ pq0) ∗ ((base + 40#64) ↦₆₄ pq1) ∗ ((base + 48#64) ↦₆₄ pq2) ∗
      ((base + 56#64) ↦₆₄ pq3) ∗
      ((base + 64#64) ↦₆₄ ck0) ∗ ((base + 72#64) ↦₆₄ ck1) ∗ ((base + 80#64) ↦₆₄ ck2) ∗
      ((base + 88#64) ↦₆₄ ck3) ∗
      ((base + 96#64) ↦₃₂ 0#32) := by
  simp only [List.append_assoc, pointsToBytes_append, hrk, hpq, hck,
    hrk_cells, hpq_cells, hck_cells, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem hkSlot100_cells_entails_memRegion100 (base : BitVec 64)
    (rk0 rk1 rk2 rk3 pq0 pq1 pq2 pq3 ck0 ck1 ck2 ck3 : BitVec 64) :
    (base ↦₆₄ rk0) ∗ ((base + 8#64) ↦₆₄ rk1) ∗ ((base + 16#64) ↦₆₄ rk2) ∗
    ((base + 24#64) ↦₆₄ rk3) ∗
    ((base + 32#64) ↦₆₄ pq0) ∗ ((base + 40#64) ↦₆₄ pq1) ∗ ((base + 48#64) ↦₆₄ pq2) ∗
    ((base + 56#64) ↦₆₄ pq3) ∗
    ((base + 64#64) ↦₆₄ ck0) ∗ ((base + 72#64) ↦₆₄ ck1) ∗ ((base + 80#64) ↦₆₄ ck2) ∗
    ((base + 88#64) ↦₆₄ ck3) ∗
    ((base + 96#64) ↦₃₂ 0#32) ⊢
      memRegion base 100 := by
  rw [ProofLib.memRegion_split' (b := base) (n := 8) (k := 92) (b' := base + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 8#64) (n := 8) (k := 84) (b' := base + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 16#64) (n := 8) (k := 76) (b' := base + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 24#64) (n := 8) (k := 68) (b' := base + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 32#64) (n := 8) (k := 60) (b' := base + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 40#64) (n := 8) (k := 52) (b' := base + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 48#64) (n := 8) (k := 44) (b' := base + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 56#64) (n := 8) (k := 36) (b' := base + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 64#64) (n := 8) (k := 28) (b' := base + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 72#64) (n := 8) (k := 20) (b' := base + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 80#64) (n := 8) (k := 12) (b' := base + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := base + 88#64) (n := 8) (k := 4) (b' := base + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))))))))))))

theorem spqrParams_5632_merge_72 (fsp w0 w1 : BitVec 64) (d2 d3 d4 d5 d6 : BitVec 32) :
    ((fsp + 5632#64) ↦₆₄ w0) ∗ ((fsp + 5640#64) ↦₆₄ w1) ∗
    ((fsp + 5648#64) ↦₃₂ d2) ∗ ((fsp + 5652#64) ↦₃₂ d3) ∗
    ((fsp + 5656#64) ↦₃₂ d4) ∗ ((fsp + 5660#64) ↦₃₂ d5) ∗
    ((fsp + 5664#64) ↦₃₂ d6) ∗ memRegion (fsp + 5668#64) 36 ⊢
      memRegion (fsp + 5632#64) 72 := by
  rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 8) (k := 64) (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 8) (k := 56) (b' := fsp + 5648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 4) (k := 52) (b' := fsp + 5652#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5652#64) (n := 4) (k := 48) (b' := fsp + 5656#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5656#64) (n := 4) (k := 44) (b' := fsp + 5660#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5660#64) (n := 4) (k := 40) (b' := fsp + 5664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5664#64) (n := 4) (k := 36) (b' := fsp + 5668#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (Entails.refl _)))))))

theorem spqrOut_4064_to_memRegion344 (fsp w0 w1 w2 w3 : BitVec 64) :
    ((fsp + 4064#64) ↦₆₄ w0) ∗ ((fsp + 4072#64) ↦₆₄ w1) ∗
    ((fsp + 4080#64) ↦₆₄ w2) ∗ ((fsp + 4088#64) ↦₆₄ w3) ∗
    memRegion (fsp + 4096#64) 312 ⊢
      memRegion (fsp + 4064#64) 344 := by
  rw [ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 32) (k := 312)
        (b' := fsp + 4096#64) rfl (by bv_omega) (by decide)]
  have h32 := cells4_entails_memRegion32' (fsp + 4064#64) w0 w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h32 (Entails.refl _))

theorem ccOk72_5632_to_spqrParams (fsp : BitVec 64)
    (rk0 rk1 rk2 rk3 ck0 ck1 ck2 ck3 : BitVec 64) :
    ((fsp + 5632#64) ↦₃₂ 0#32) ∗
    ((fsp + 5636#64) ↦₆₄ rk0) ∗ ((fsp + 5644#64) ↦₆₄ rk1) ∗
    ((fsp + 5652#64) ↦₆₄ rk2) ∗ ((fsp + 5660#64) ↦₆₄ rk3) ∗
    ((fsp + 5668#64) ↦₆₄ ck0) ∗ ((fsp + 5676#64) ↦₆₄ ck1) ∗
    ((fsp + 5684#64) ↦₆₄ ck2) ∗ ((fsp + 5692#64) ↦₆₄ ck3) ∗
    ((fsp + 5700#64) ↦₃₂ 0#32) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ d2 : BitVec 32,
      ∃∗ d3 : BitVec 32, ∃∗ w4 : BitVec 64, ∃∗ d6 : BitVec 32,
        ((fsp + 5632#64) ↦₆₄ w0) ∗ ((fsp + 5640#64) ↦₆₄ w1) ∗
        ((fsp + 5648#64) ↦₃₂ d2) ∗ ((fsp + 5652#64) ↦₃₂ d3) ∗
        ((fsp + 5656#64) ↦₆₄ w4) ∗ ((fsp + 5664#64) ↦₃₂ d6) ∗
        memRegion (fsp + 5668#64) 36 := by
  have hm72 :
      ((fsp + 5632#64) ↦₃₂ 0#32) ∗
      ((fsp + 5636#64) ↦₆₄ rk0) ∗ ((fsp + 5644#64) ↦₆₄ rk1) ∗
      ((fsp + 5652#64) ↦₆₄ rk2) ∗ ((fsp + 5660#64) ↦₆₄ rk3) ∗
      ((fsp + 5668#64) ↦₆₄ ck0) ∗ ((fsp + 5676#64) ↦₆₄ ck1) ∗
      ((fsp + 5684#64) ↦₆₄ ck2) ∗ ((fsp + 5692#64) ↦₆₄ ck3) ∗
      ((fsp + 5700#64) ↦₃₂ 0#32) ⊢
        memRegion (fsp + 5632#64) 72 := by
    rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 4) (k := 68) (b' := fsp + 5636#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5636#64) (n := 8) (k := 60) (b' := fsp + 5644#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5644#64) (n := 8) (k := 52) (b' := fsp + 5652#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5652#64) (n := 8) (k := 44) (b' := fsp + 5660#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5660#64) (n := 8) (k := 36) (b' := fsp + 5668#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5668#64) (n := 8) (k := 28) (b' := fsp + 5676#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5676#64) (n := 8) (k := 20) (b' := fsp + 5684#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5684#64) (n := 8) (k := 12) (b' := fsp + 5692#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5692#64) (n := 8) (k := 4) (b' := fsp + 5700#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo32_entails_memRegion _ _)))))))))
  refine Entails.trans hm72 ?_
  rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 8) (k := 64) (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 8) (k := 56) (b' := fsp + 5648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 4) (k := 52) (b' := fsp + 5652#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5652#64) (n := 4) (k := 48) (b' := fsp + 5656#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5656#64) (n := 8) (k := 40) (b' := fsp + 5664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5664#64) (n := 4) (k := 36) (b' := fsp + 5668#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 5632#64),
      ProofLib.memRegion_eight (fsp + 5640#64),
      ProofLib.memRegion_four (fsp + 5648#64),
      ProofLib.memRegion_four (fsp + 5652#64),
      ProofLib.memRegion_eight (fsp + 5656#64),
      ProofLib.memRegion_four (fsp + 5664#64)]
  s4_exists_eq
  exact Entails.refl _

theorem memRegion344_4064_split68 (fsp : BitVec 64) :
    memRegion (fsp + 4064#64) 344 =
      memRegion (fsp + 4064#64) 68 ∗ memRegion (fsp + 4132#64) 276 :=
  ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 68) (k := 276)
    (b' := fsp + 4132#64) rfl (by bv_omega) (by decide)

theorem memRegion68_4064_split (fsp : BitVec 64) :
    memRegion (fsp + 4064#64) 68 =
      cells (fsp + 4064#64) 8 ∗ (∃∗ v : BitVec 32, (fsp + 4128#64) ↦₃₂ v) := by
  rw [ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 64) (k := 4)
        (b' := fsp + 4128#64) rfl (by bv_omega) (by decide),
      (ProofLib.memRegion_cells (fsp + 4064#64) 8 (by decide) :
        memRegion (fsp + 4064#64) 64 = cells (fsp + 4064#64) 8),
      ProofLib.memRegion_four (fsp + 4128#64)]

def pack32Pair (lo hi : BitVec 32) : BitVec 64 :=
  (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_low (lo hi : BitVec 32) :
    (pack32Pair lo hi).setWidth 32 = lo := by
  unfold pack32Pair; bv_kernel

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_high (lo hi : BitVec 32) :
    ((pack32Pair lo hi) >>> 32).setWidth 32 = hi := by
  unfold pack32Pair; bv_kernel

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_high_bv (lo hi : BitVec 32) :
    ((pack32Pair lo hi) >>> 32#64).setWidth 32 = hi := by
  change ((pack32Pair lo hi) >>> (32#64).toNat).setWidth 32 = hi
  exact pack32Pair_high lo hi

theorem bv64_eq_pack32Pair (w : BitVec 64) :
    w = pack32Pair (w.setWidth 32) ((w >>> 32).setWidth 32) := by
  unfold pack32Pair; bv_kernel

theorem unpack64_pack32Pair (lo hi : BitVec 32) :
    unpack64 (pack32Pair lo hi) = unpack32 lo ++ unpack32 hi := by
  dsimp only [pack32Pair, unpack64, unpack32]
  exact congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel) rfl)))))))

@[simp, arm64_norm, wp_norm]
theorem s4_bv_add_add (x : BitVec 64) (a b : Nat) (_hab : a + b < 2 ^ 64 := by decide) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

@[simp, arm64_norm, wp_norm]
theorem s4_bv_add_sub_gt (x : BitVec 64) (a b : Nat) (_h : b < a := by decide)
    (_ha : a < 2 ^ 64 := by decide) :
    x + BitVec.ofNat 64 a - BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[simp, arm64_norm, wp_norm]
theorem s4_bv_add_sub_lt (x : BitVec 64) (a b : Nat) (_h : a < b := by decide)
    (_hb : b < 2 ^ 64 := by decide) :
    x + BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (b - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[simp, arm64_norm, wp_norm]
theorem s4_bv_add_sub_cancel (x : BitVec 64) (a : Nat) :
    x + BitVec.ofNat 64 a - BitVec.ofNat 64 a = x := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem s4_bv_sub_add_cancel (x : BitVec 64) (a : Nat) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 a = x := by
  bv_omega

theorem pointsTo64_pack32Pair (base : BitVec 64) (lo hi : BitVec 32) :
    (base ↦₆₄ pack32Pair lo hi) =
      (base ↦₃₂ lo) ∗ ((base + 4#64) ↦₃₂ hi) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack32Pair, pointsToBytes_append]
  simp only [unpack32_length, ← pointsTo32_eq_pointsToBytes]

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_truncate_low (lo hi : BitVec 32) :
    BitVec.truncate 32 (pack32Pair lo hi) = lo := by
  unfold pack32Pair; bv_kernel

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_truncate_high (lo hi : BitVec 32) :
    BitVec.truncate 32 ((pack32Pair lo hi) >>> 32) = hi := by
  unfold pack32Pair; bv_kernel

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_truncate_high_bv (lo hi : BitVec 32) :
    BitVec.truncate 32 ((pack32Pair lo hi) >>> 32#64) = hi := by
  change BitVec.truncate 32 ((pack32Pair lo hi) >>> (32#64).toNat) = hi
  exact pack32Pair_truncate_high lo hi

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_extract0 (lo hi : BitVec 32) :
    (pack32Pair lo hi).extractLsb' 0 32 = lo := by
  unfold pack32Pair; bv_kernel

@[simp, arm64_norm, wp_norm]
theorem pack32Pair_extract32 (lo hi : BitVec 32) :
    (pack32Pair lo hi).extractLsb' 32 32 = hi := by
  unfold pack32Pair; bv_kernel

theorem pointsTo64_pair_eq_pointsTo128 (a : BitVec 64) (w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) = pointsTo128 a (w1 ++ w0) := by
  unfold pointsTo128
  exact congrArg₂ sepConj (congrArg (pointsTo64 a) (by bv_kernel))
    (congrArg (pointsTo64 (a + 8#64)) (by bv_kernel))

theorem pointsTo128_zero (a : BitVec 64) :
    pointsTo128 a 0#128 = (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64) := by
  rw [show (0#128 : BitVec 128) = (0#64 : BitVec 64) ++ 0#64 from rfl,
      ← pointsTo64_pair_eq_pointsTo128 a 0#64 0#64]

theorem fsp_pair128 (fsp : BitVec 64) (off off8 : Nat) (w0 w1 : BitVec 64)
    (h : BitVec.ofNat 64 off + 8#64 = BitVec.ofNat 64 off8 := by decide) :
    ((fsp + BitVec.ofNat 64 off) ↦₆₄ w0) ∗ ((fsp + BitVec.ofNat 64 off8) ↦₆₄ w1) =
      pointsTo128 (fsp + BitVec.ofNat 64 off) (w1 ++ w0) := by
  rw [← h, ← BitVec.add_assoc]
  exact pointsTo64_pair_eq_pointsTo128 (fsp + BitVec.ofNat 64 off) w0 w1

theorem fsp_zero128 (fsp : BitVec 64) (off off8 : Nat)
    (h : BitVec.ofNat 64 off + 8#64 = BitVec.ofNat 64 off8 := by decide) :
    pointsTo128 (fsp + BitVec.ofNat 64 off) 0#128 =
      ((fsp + BitVec.ofNat 64 off) ↦₆₄ 0#64) ∗ ((fsp + BitVec.ofNat 64 off8) ↦₆₄ 0#64) := by
  rw [← h, ← BitVec.add_assoc]
  exact pointsTo128_zero (fsp + BitVec.ofNat 64 off)

theorem exists_unpack32_8_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 32,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₃₂ d0) ∗ ((a + 4#64) ↦₃₂ d1) ∗ ((a + 8#64) ↦₃₂ d2) ∗ ((a + 12#64) ↦₃₂ d3) ∗
          ((a + 16#64) ↦₃₂ d4) ∗ ((a + 20#64) ↦₃₂ d5) ∗ ((a + 24#64) ↦₃₂ d6) ∗
          ((a + 28#64) ↦₃₂ d7) := by
  obtain ⟨w0, w1, w2, w3, _, hw⟩ := exists_unpack64_of_length_32 h
  refine ⟨w0.setWidth 32, (w0 >>> 32).setWidth 32,
          w1.setWidth 32, (w1 >>> 32).setWidth 32,
          w2.setWidth 32, (w2 >>> 32).setWidth 32,
          w3.setWidth 32, (w3 >>> 32).setWidth 32, fun a => ?_⟩
  conv => lhs; rw [hw a, bv64_eq_pack32Pair w0, bv64_eq_pack32Pair w1,
    bv64_eq_pack32Pair w2, bv64_eq_pack32Pair w3]
  simp only [pointsTo64_pack32Pair, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion32_7232_unaligned_split (fsp : BitVec 64) :
    memRegion (fsp + 7232#64) 32 =
      ∃∗ d0 : BitVec 32, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ d4 : BitVec 32,
        ((fsp + 7232#64) ↦₃₂ d0) ∗ ((fsp + 7236#64) ↦₆₄ w1) ∗
        ((fsp + 7244#64) ↦₆₄ w2) ∗ ((fsp + 7252#64) ↦₆₄ w3) ∗
        ((fsp + 7260#64) ↦₃₂ d4) := by
  rw [ProofLib.memRegion_split' (b := fsp + 7232#64) (n := 4) (k := 28) (b' := fsp + 7236#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 7236#64) (n := 8) (k := 20) (b' := fsp + 7244#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 7244#64) (n := 8) (k := 12) (b' := fsp + 7252#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 7252#64) (n := 8) (k := 4) (b' := fsp + 7260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (fsp + 7232#64),
      ProofLib.memRegion_eight (fsp + 7236#64),
      ProofLib.memRegion_eight (fsp + 7244#64),
      ProofLib.memRegion_eight (fsp + 7252#64),
      ProofLib.memRegion_four (fsp + 7260#64)]
  s4_exists_eq

theorem memRegion36_2336_unaligned_split (fsp : BitVec 64) :
    memRegion (fsp + 2336#64) 36 =
      ∃∗ d0 : BitVec 32, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ((fsp + 2336#64) ↦₃₂ d0) ∗ ((fsp + 2340#64) ↦₆₄ w1) ∗
        ((fsp + 2348#64) ↦₆₄ w2) ∗ ((fsp + 2356#64) ↦₆₄ w3) ∗
        ((fsp + 2364#64) ↦₆₄ w4) := by
  rw [ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 4) (k := 32) (b' := fsp + 2340#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2340#64) (n := 8) (k := 24) (b' := fsp + 2348#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2348#64) (n := 8) (k := 16) (b' := fsp + 2356#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2356#64) (n := 8) (k := 8) (b' := fsp + 2364#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (fsp + 2336#64),
      ProofLib.memRegion_eight (fsp + 2340#64),
      ProofLib.memRegion_eight (fsp + 2348#64),
      ProofLib.memRegion_eight (fsp + 2356#64),
      ProofLib.memRegion_eight (fsp + 2364#64)]
  s4_exists_eq

theorem ccOk72_5632_to_spqrParams_unaligned (fsp : BitVec 64)
    (r0 : BitVec 32) (p1 p2 p3 p4 p5 p6 p7 p8 : BitVec 64) :
    ((fsp + 5632#64) ↦₃₂ 0#32) ∗
    ((fsp + 5636#64) ↦₃₂ r0) ∗
    ((fsp + 5640#64) ↦₆₄ p1) ∗ ((fsp + 5648#64) ↦₆₄ p2) ∗
    ((fsp + 5656#64) ↦₆₄ p3) ∗ ((fsp + 5664#64) ↦₆₄ p4) ∗
    ((fsp + 5672#64) ↦₆₄ p5) ∗ ((fsp + 5680#64) ↦₆₄ p6) ∗
    ((fsp + 5688#64) ↦₆₄ p7) ∗ ((fsp + 5696#64) ↦₆₄ p8) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ d2 : BitVec 32,
      ∃∗ d3 : BitVec 32, ∃∗ w4 : BitVec 64, ∃∗ d6 : BitVec 32,
        ((fsp + 5632#64) ↦₆₄ w0) ∗ ((fsp + 5640#64) ↦₆₄ w1) ∗
        ((fsp + 5648#64) ↦₃₂ d2) ∗ ((fsp + 5652#64) ↦₃₂ d3) ∗
        ((fsp + 5656#64) ↦₆₄ w4) ∗ ((fsp + 5664#64) ↦₃₂ d6) ∗
        memRegion (fsp + 5668#64) 36 := by
  have hm72 :
      ((fsp + 5632#64) ↦₃₂ 0#32) ∗
      ((fsp + 5636#64) ↦₃₂ r0) ∗
      ((fsp + 5640#64) ↦₆₄ p1) ∗ ((fsp + 5648#64) ↦₆₄ p2) ∗
      ((fsp + 5656#64) ↦₆₄ p3) ∗ ((fsp + 5664#64) ↦₆₄ p4) ∗
      ((fsp + 5672#64) ↦₆₄ p5) ∗ ((fsp + 5680#64) ↦₆₄ p6) ∗
      ((fsp + 5688#64) ↦₆₄ p7) ∗ ((fsp + 5696#64) ↦₆₄ p8) ⊢
        memRegion (fsp + 5632#64) 72 := by
    rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 4) (k := 68) (b' := fsp + 5636#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5636#64) (n := 4) (k := 64) (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 8) (k := 56) (b' := fsp + 5648#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 8) (k := 48) (b' := fsp + 5656#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5656#64) (n := 8) (k := 40) (b' := fsp + 5664#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5664#64) (n := 8) (k := 32) (b' := fsp + 5672#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5672#64) (n := 8) (k := 24) (b' := fsp + 5680#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5680#64) (n := 8) (k := 16) (b' := fsp + 5688#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 5688#64) (n := 8) (k := 8) (b' := fsp + 5696#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))))))))
  refine Entails.trans hm72 ?_
  rw [ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 8) (k := 64) (b' := fsp + 5640#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5640#64) (n := 8) (k := 56) (b' := fsp + 5648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 4) (k := 52) (b' := fsp + 5652#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5652#64) (n := 4) (k := 48) (b' := fsp + 5656#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5656#64) (n := 8) (k := 40) (b' := fsp + 5664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5664#64) (n := 4) (k := 36) (b' := fsp + 5668#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 5632#64),
      ProofLib.memRegion_eight (fsp + 5640#64),
      ProofLib.memRegion_four (fsp + 5648#64),
      ProofLib.memRegion_four (fsp + 5652#64),
      ProofLib.memRegion_eight (fsp + 5656#64),
      ProofLib.memRegion_four (fsp + 5664#64)]
  s4_exists_eq
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
