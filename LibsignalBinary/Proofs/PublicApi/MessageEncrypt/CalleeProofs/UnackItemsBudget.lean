/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItems
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# VM-Preserving `unacknowledged_pre_key_message_items`

Proves `subroutine_ok (lsProg_36 H) (blkPl_36).base (withLsCodeLoaded lsmpl (unackItemsPlacedSpec A))`
under `HookSat H lsTimeAddSym timeAddBudgetSpec` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved timeAddBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SystemTime PendingPreKey PendingKyberPreKey Session)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_201 blkPl_201 lsLogFilterAddr ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain
   lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At vecAt)
open CryptoVerification.LibsignalSessionRepr (VecGhost leBytes vecGhostAt chainAt)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (DeserGhost deserializePlacedSpec publicKey_deserialize_ok_inversion pointsToBytes_deserialize_split)
open CryptoVerification.LibsignalTripleRatchetRepr
  (noneCap TailVecGhost optTailVecAt SessionGhost optSenderChainAt sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr
  (OptU32Rel PendingRel KyberRel optU32At sessionStateReprAt)
open CryptoVerification.LibsignalPublicApi (timeAddSpec)
open CryptoVerification.LibsignalPublicApi.Placed
  (lsProg_36 blkPC_36 blkPl_36 blkLib_eq_36 blkPC_36_pairStep_0x84)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (unackItemsStack unackKyberSliceAt unackOutAt UnackCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems
  (lsTimeAddSym subroutine_ok_merge_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (withLsRet hookSat_withLsRet lsRetAddr624_of_lr_eq_blockPlacement_base_add)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.AddrOffsetArith
  (le_of_eq32 extractLsb'_append_lo extractLsb'_append_hi sub_add_ofNat_eq_sub
   add_add_ofNat_eq_add add_ofNat_eq_add sub_add_eq_sub add_add_eq_add)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem vmPreserved_trans_eq {s0 s1 s1' s2 : State}
    (h1 : VmPreserved s0 s1) (h2 : VmPreserved s1' s2)
    (heq : s1 = s1' := by simp only [wp_norm, arm64_norm]) :
    VmPreserved s0 s2 := by cases heq; exact h1.trans h2

private theorem vmPreserved_prepend {s1 s2 s3 : State}
    (h23 : VmPreserved s2 s3) (h12 : VmPreserved s1 s2 := by assumption) :
    VmPreserved s1 s3 := h12.trans h23

private def deserializePlacedVmSpec [LibsignalPlacement] : Spec DeserGhost where
  pre := deserializePlacedSpec.pre
  post := fun (ptr, bs, pk, sret, _, _) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)

private theorem deserialize_placed_ok_vm [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base deserializePlacedVmSpec := by
  simp only [deserializePlacedVmSpec, deserializePlacedSpec]
  wp_init g s0
  obtain ⟨ptr, bs, pk, sret, tag0, out32⟩ := g
  dsimp only at *
  subst h_1 h_3
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h_5
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ :=
    exists_unpack64_of_length_32 (bs := out32) h
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) h_5,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
    hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_201).rebase (blkPl_201).base (hooksException H))
    CryptoVerification.blkLib_eq_201 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  wp_steps
  wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      h_2, decide_eq_true_eq] at hcs
    omega
  · wp_step
    wp_if hcbz9
    · wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [wp_norm, arm64_norm] at hvm
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done
    · wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [wp_norm, arm64_norm] at hvm
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done

/-! ## Separation-Logic and `SepWPp` Helpers -/

private theorem leBytes_4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

private theorem pointsToBytes_leBytes4_eq_pointsTo32 (a : BitVec 64) (w : BitVec 32) :
    (a ↦ₛ leBytes 4 w.toNat) = (a ↦₃₂ w) := by
  rw [leBytes_4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

private theorem leBytes_8_eq_unpack64 (w : BitVec 64) :
    leBytes 8 w.toNat = unpack64 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216),
          BitVec.ofNat 8 (w.toNat / 4294967296), BitVec.ofNat 8 (w.toNat / 1099511627776),
          BitVec.ofNat 8 (w.toNat / 281474976710656), BitVec.ofNat 8 (w.toNat / 72057594037927936)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w,
     BitVec.extractLsb' 32 8 w, BitVec.extractLsb' 40 8 w,
     BitVec.extractLsb' 48 8 w, BitVec.extractLsb' 56 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
        · congr 1
          · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
          · congr 1
            · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
            · congr 1
              · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
              · congr 1
                · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

private theorem pointsToBytes_leBytes8_eq_pointsTo64 (a : BitVec 64) (w : BitVec 64) :
    (a ↦ₛ leBytes 8 w.toNat) = (a ↦₆₄ w) := by
  rw [leBytes_8_eq_unpack64, ← pointsTo64_eq_pointsToBytes]

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

private theorem sevenLo_eq_sevenHi (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenLo_eq_sevenHi a b0 b1 b2 b3 b4 b5 b6)

private theorem pointsTo32_32_eq_pointsTo64 (a : BitVec 64) (w0 w1 : BitVec 32) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1)) = (a ↦₆₄ (w1 ++ w0)) := by
  simp only [pointsTo32, pointsTo64,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have e0 : w0.extractLsb' 0 8 = (w1 ++ w0).extractLsb' 0 8 :=
    (extractLsb'_append_lo w1 w0 0 8 (by decide)).symm
  have e1 : w0.extractLsb' 8 8 = (w1 ++ w0).extractLsb' 8 8 :=
    (extractLsb'_append_lo w1 w0 8 8 (by decide)).symm
  have e2 : w0.extractLsb' 16 8 = (w1 ++ w0).extractLsb' 16 8 :=
    (extractLsb'_append_lo w1 w0 16 8 (by decide)).symm
  have e3 : w0.extractLsb' 24 8 = (w1 ++ w0).extractLsb' 24 8 :=
    (extractLsb'_append_lo w1 w0 24 8 (by decide)).symm
  have e4 : w1.extractLsb' 0 8 = (w1 ++ w0).extractLsb' 32 8 :=
    (extractLsb'_append_hi w1 w0 32 8 (by decide)).symm
  have e5 : w1.extractLsb' 8 8 = (w1 ++ w0).extractLsb' 40 8 :=
    (extractLsb'_append_hi w1 w0 40 8 (by decide)).symm
  have e6 : w1.extractLsb' 16 8 = (w1 ++ w0).extractLsb' 48 8 :=
    (extractLsb'_append_hi w1 w0 48 8 (by decide)).symm
  have e7 : w1.extractLsb' 24 8 = (w1 ++ w0).extractLsb' 56 8 :=
    (extractLsb'_append_hi w1 w0 56 8 (by decide)).symm
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

private theorem pointsTo32_32_eq_pointsTo64' (a a4 : BitVec 64)
    (h4 : a + 4#64 = a4) (w0 w1 : BitVec 32) (rest : SepProp) :
    ((a ↦₃₂ w0) ∗ (a4 ↦₃₂ w1) ∗ rest) = ((a ↦₆₄ (w1 ++ w0)) ∗ rest) := by
  subst h4
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (pointsTo32_32_eq_pointsTo64 a w0 w1)

private def baseKeyChunks (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₆₄ v7) ∗ ((a + 15#64) ↦₆₄ v15) ∗
  ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem exists_baseKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = baseKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack64 (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8)
      (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 7 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (le_of_eq32 h (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 7 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (le_of_eq32 h (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  rw [h8, h1, h4]
  simp only [baseKeyChunks, pack32, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem baseKeyChunks_sp_127 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8) :
    baseKeyChunks (sp - 127#64) b0 b1 b2 b3 b4 b5 b6 v7 v15 v23 v31 =
      ((sp - 127#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 123#64) ↦₈ b4) ∗ ((sp - 122#64) ↦₈ b5) ∗ ((sp - 121#64) ↦₈ b6) ∗
      ((sp - 120#64) ↦₆₄ v7) ∗ ((sp - 112#64) ↦₆₄ v15) ∗
      ((sp - 104#64) ↦₆₄ v23) ∗ ((sp - 96#64) ↦₈ v31) := by
  dsimp only [baseKeyChunks]
  rw [ProofLib.sub_add_eq_sub sp 127#64 4#64 123#64 rfl, ProofLib.sub_add_eq_sub sp 127#64 5#64 122#64 rfl,
      ProofLib.sub_add_eq_sub sp 127#64 6#64 121#64 rfl, ProofLib.sub_add_eq_sub sp 127#64 7#64 120#64 rfl,
      ProofLib.sub_add_eq_sub sp 127#64 15#64 112#64 rfl, ProofLib.sub_add_eq_sub sp 127#64 23#64 104#64 rfl,
      ProofLib.sub_add_eq_sub sp 127#64 31#64 96#64 rfl]

private theorem baseKeyChunks_out_32 (out : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8) :
    baseKeyChunks (out + 32#64) b0 b1 b2 b3 b4 b5 b6 v7 v15 v23 v31 =
      ((out + 32#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((out + 36#64) ↦₈ b4) ∗ ((out + 37#64) ↦₈ b5) ∗ ((out + 38#64) ↦₈ b6) ∗
      ((out + 39#64) ↦₆₄ v7) ∗ ((out + 47#64) ↦₆₄ v15) ∗
      ((out + 55#64) ↦₆₄ v23) ∗ ((out + 63#64) ↦₈ v31) := by
  dsimp only [baseKeyChunks]
  rw [add_add_eq_add out 32#64 36#64 4#64 rfl, add_add_eq_add out 32#64 37#64 5#64 rfl,
      add_add_eq_add out 32#64 38#64 6#64 rfl, add_add_eq_add out 32#64 39#64 7#64 rfl,
      add_add_eq_add out 32#64 47#64 15#64 rfl, add_add_eq_add out 32#64 55#64 23#64 rfl,
      add_add_eq_add out 32#64 63#64 31#64 rfl]

private theorem sevenLo_sp_127 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 127#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 123#64) ↦₈ b4) ∗ ((sp - 122#64) ↦₈ b5) ∗ ((sp - 121#64) ↦₈ b6) ∗ rest) =
      (((sp - 127#64) ↦₈ b0) ∗ ((sp - 126#64) ↦₈ b1) ∗ ((sp - 125#64) ↦₈ b2) ∗
       ((sp - 124#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 127#64) (sp - 126#64) (sp - 125#64) (sp - 124#64)
    (sp - 123#64) (sp - 122#64) (sp - 121#64)
    (sub_add_eq_sub sp 127#64 126#64 1#64 rfl) (sub_add_eq_sub sp 127#64 125#64 2#64 rfl)
    (sub_add_eq_sub sp 127#64 124#64 3#64 rfl) (sub_add_eq_sub sp 127#64 123#64 4#64 rfl)
    (sub_add_eq_sub sp 127#64 122#64 5#64 rfl) (sub_add_eq_sub sp 127#64 121#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_88 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 84#64) ↦₈ b4) ∗ ((sp - 83#64) ↦₈ b5) ∗ ((sp - 82#64) ↦₈ b6) ∗ rest) =
      (((sp - 88#64) ↦₈ b0) ∗ ((sp - 87#64) ↦₈ b1) ∗ ((sp - 86#64) ↦₈ b2) ∗
       ((sp - 85#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 88#64) (sp - 87#64) (sp - 86#64) (sp - 85#64)
    (sp - 84#64) (sp - 83#64) (sp - 82#64)
    (sub_add_eq_sub sp 88#64 87#64 1#64 rfl) (sub_add_eq_sub sp 88#64 86#64 2#64 rfl)
    (sub_add_eq_sub sp 88#64 85#64 3#64 rfl) (sub_add_eq_sub sp 88#64 84#64 4#64 rfl)
    (sub_add_eq_sub sp 88#64 83#64 5#64 rfl) (sub_add_eq_sub sp 88#64 82#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_168 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 168#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 164#64) ↦₈ b4) ∗ ((sp - 163#64) ↦₈ b5) ∗ ((sp - 162#64) ↦₈ b6) ∗ rest) =
      (((sp - 168#64) ↦₈ b0) ∗ ((sp - 167#64) ↦₈ b1) ∗ ((sp - 166#64) ↦₈ b2) ∗
       ((sp - 165#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 168#64) (sp - 167#64) (sp - 166#64) (sp - 165#64)
    (sp - 164#64) (sp - 163#64) (sp - 162#64)
    (sub_add_eq_sub sp 168#64 167#64 1#64 rfl) (sub_add_eq_sub sp 168#64 166#64 2#64 rfl)
    (sub_add_eq_sub sp 168#64 165#64 3#64 rfl) (sub_add_eq_sub sp 168#64 164#64 4#64 rfl)
    (sub_add_eq_sub sp 168#64 163#64 5#64 rfl) (sub_add_eq_sub sp 168#64 162#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_out_32 (out : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((out + 32#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((out + 36#64) ↦₈ b4) ∗ ((out + 37#64) ↦₈ b5) ∗ ((out + 38#64) ↦₈ b6) ∗ rest) =
      (((out + 32#64) ↦₈ b0) ∗ ((out + 33#64) ↦₈ b1) ∗ ((out + 34#64) ↦₈ b2) ∗
       ((out + 35#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (out + 32#64) (out + 33#64) (out + 34#64) (out + 35#64)
    (out + 36#64) (out + 37#64) (out + 38#64)
    (add_add_eq_add out 32#64 33#64 1#64 rfl) (add_add_eq_add out 32#64 34#64 2#64 rfl)
    (add_add_eq_add out 32#64 35#64 3#64 rfl) (add_add_eq_add out 32#64 36#64 4#64 rfl)
    (add_add_eq_add out 32#64 37#64 5#64 rfl) (add_add_eq_add out 32#64 38#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem pointsTo32_32_sp_172 (sp : BitVec 64)
    (w0 w1 : BitVec 32) (rest : SepProp) :
    (((sp - 172#64) ↦₃₂ w0) ∗ ((sp - 168#64) ↦₃₂ w1) ∗ rest) =
      (((sp - 172#64) ↦₆₄ (w1 ++ w0)) ∗ rest) :=
  pointsTo32_32_eq_pointsTo64' (sp - 172#64) (sp - 168#64)
    (sub_add_eq_sub sp 172#64 168#64 4#64 rfl) w0 w1 rest

private theorem pointsTo32_32_out_28 (out : BitVec 64)
    (w0 w1 : BitVec 32) (rest : SepProp) :
    (((out + 28#64) ↦₃₂ w0) ∗ ((out + 32#64) ↦₃₂ w1) ∗ rest) =
      (((out + 28#64) ↦₆₄ (w1 ++ w0)) ∗ rest) :=
  pointsTo32_32_eq_pointsTo64' (out + 28#64) (out + 32#64)
    (add_add_eq_add out 28#64 32#64 4#64 rfl) w0 w1 rest

private theorem optU32Rel_pointsToBytes (a : BitVec 64) (bs : List (BitVec 8))
    (opt : Option (BitVec 32)) (hrel : OptU32Rel bs opt) (hlen : 8 ≤ bs.length) :
    ∃ (pkTag pkVal : BitVec 32),
      (a ↦ₛ bs.take 8) = (a ↦₃₂ pkTag) ∗ ((a + 4#64) ↦₃₂ pkVal) ∧
      (∀ out : BitVec 64, (out ↦₃₂ pkTag) ∗ ((out + 4#64) ↦₃₂ pkVal) ⊢ optU32At out opt) := by
  have hsplit : bs.take 8 = bs.take 4 ++ (bs.drop 4).take 4 := by
    simpa using List.take_add (i := 4) (j := 4) (l := bs)
  have hlen4 : (bs.take 4).length = 4 := by simp [List.length_take]; omega
  cases opt with
  | none =>
    dsimp only [OptU32Rel] at hrel
    have h0_eq : (a ↦ₛ [0#8, 0#8, 0#8, 0#8]) = (a ↦₃₂ 0#32) := pointsToBytes_leBytes4_eq_pointsTo32 a 0#32
    refine ⟨0#32, pack32 (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8), ?_, ?_⟩
    · rw [hsplit, pointsToBytes_append, hlen4, hrel, h0_eq,
          pointsToBytes_take4_eq_pointsTo32 (a + BitVec.ofNat 64 4) bs 4 hlen]
    · intro out; dsimp only [optU32At]
      exact sepConj_mono_right (pointsTo32_entails_memRegion (out + 4#64) _)
  | some v =>
    rcases hrel with ⟨h0, h1⟩
    have h1_eq : (a ↦ₛ [1#8, 0#8, 0#8, 0#8]) = (a ↦₃₂ 1#32) := pointsToBytes_leBytes4_eq_pointsTo32 a 1#32
    refine ⟨1#32, v, ?_, ?_⟩
    · rw [hsplit, pointsToBytes_append, hlen4, h0, h1, h1_eq, pointsToBytes_leBytes4_eq_pointsTo32]
    · intro out; dsimp only [optU32At]; exact Entails.refl _

private theorem pendingTail_pointsToBytes (ss : BitVec 64) (tail : List (BitVec 8))
    (items : PendingPreKey) (hlen : tail.length = 24)
    (hpk : OptU32Rel tail items.preKeyId)
    (hts : (tail.drop 8).take 8 = leBytes 8 items.timestamp.toNat)
    (hspk : (tail.drop 16).take 4 = leBytes 4 items.signedPreKeyId.toNat) :
    ∃ (pkTag pkVal : BitVec 32),
      ((ss + 272#64) ↦ₛ tail) =
        ((ss + 272#64) ↦₃₂ pkTag) ∗ ((ss + 276#64) ↦₃₂ pkVal) ∗
        ((ss + 280#64) ↦₆₄ items.timestamp) ∗ ((ss + 288#64) ↦₃₂ items.signedPreKeyId) ∗
        ((ss + 292#64) ↦ₛ tail.drop 20) ∧
      (∀ out : BitVec 64, (out ↦₃₂ pkTag) ∗ ((out + 4#64) ↦₃₂ pkVal) ⊢ optU32At out items.preKeyId) := by
  obtain ⟨pkTag, pkVal, htake8, hent⟩ := optU32Rel_pointsToBytes (ss + 272#64) tail items.preKeyId hpk (by omega)
  refine ⟨pkTag, pkVal, ?_, hent⟩
  change ((ss + 272#64) ↦ₛ tail.drop 0) = _
  rw [pointsToBytes_drop_split (ss + 272#64) tail 0 8 (by omega),
      pointsToBytes_drop_split _ tail 8 8 (by omega),
      pointsToBytes_drop_split _ tail 16 4 (by omega)]
  simp only [List.drop_zero]
  rw [htake8, hts, pointsToBytes_leBytes8_eq_pointsTo64, hspk, pointsToBytes_leBytes4_eq_pointsTo32]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  rw [h8, h4]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem kyberTail_pointsToBytes (ss : BitVec 64) (tail : List (BitVec 8))
    (ky : PendingKyberPreKey) (hlen : tail.length = 8)
    (htake : tail.take 4 = leBytes 4 ky.preKeyId.toNat) :
    ((ss + 320#64) ↦ₛ tail) =
      ((ss + 320#64) ↦₃₂ ky.preKeyId) ∗ ((ss + 324#64) ↦ₛ tail.drop 4) := by
  change ((ss + 320#64) ↦ₛ tail.drop 0) = _
  rw [pointsToBytes_drop_split (ss + 320#64) tail 0 4 (by omega)]
  simp only [List.drop_zero]
  rw [htake, pointsToBytes_leBytes4_eq_pointsTo32]
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  rw [h4]; simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_unackItems_outer (sp : BitVec 64) :
    stackAt sp unackItemsStack =
      memRegion (sp - 16896#64) 336 ∗ stackAt (sp - 176#64) extHookStack ∗
      memRegion (sp - 176#64) 176 := by
  simp only [stackAt, unackItemsStack, extHookStack]
  have hsub : sp - 176#64 - BitVec.ofNat 64 (2 ^ 14) = sp - 16560#64 := by
    change sp - 176#64 - 16384#64 = sp - 16560#64; bv_omega
  rw [hsub]
  change memRegion (sp - 16896#64) 16896 =
    memRegion (sp - 16896#64) 336 ∗ memRegion (sp - 16560#64) 16384 ∗ memRegion (sp - 176#64) 176
  rw [@ProofLib.memRegion_split' (sp - 16896#64) (sp - 16560#64) 336 16560 16896 rfl (sub_add_ofNat_eq_sub sp 16896#64 16560#64 336 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 16560#64) (n := 16384) (k := 176) (b' := sp - 176#64) rfl (sub_add_ofNat_eq_sub sp 16560#64 176#64 16384 rfl) (by decide)]

private theorem memRegion_176_none_split (sp : BitVec 64) :
    memRegion (sp - 176#64) 176 =
      memRegion (sp - 176#64) 96 ∗ cells (sp - 80#64) 10 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 96) (k := 80) (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 176#64 80#64 96 rfl) (by decide),
      (ProofLib.memRegion_cells (sp - 80#64) 10 (by decide) : memRegion (sp - 80#64) 80 = cells (sp - 80#64) 10)]

private theorem memRegion_32_eq_exists_bytes (a : BitVec 64) :
    memRegion a 32 = ∃∗ bs : List (BitVec 8), ⌜bs.length = 32⌝ ∗ (a ↦ₛ bs) :=
  ProofLib.memRegion_eq_exists_bytes a 32 (by decide)

private theorem memRegion_176_some_split (sp : BitVec 64) :
    memRegion (sp - 176#64) 176 =
      memRegion (sp - 176#64) 4 ∗ (∃∗ s172 : BitVec 32, (sp - 172#64) ↦₃₂ s172) ∗
      (∃∗ s168 : BitVec 32, (sp - 168#64) ↦₃₂ s168) ∗ (∃∗ s164 : BitVec 8, (sp - 164#64) ↦₈ s164) ∗
      (∃∗ s163 : BitVec 8, (sp - 163#64) ↦₈ s163) ∗ (∃∗ s162 : BitVec 8, (sp - 162#64) ↦₈ s162) ∗
      memRegion (sp - 161#64) 1 ∗ (∃∗ s160 : BitVec 64, (sp - 160#64) ↦₆₄ s160) ∗
      (∃∗ s152 : BitVec 8, (sp - 152#64) ↦₈ s152) ∗ memRegion (sp - 151#64) 23 ∗
      (∃∗ tag0 : BitVec 8, (sp - 128#64) ↦₈ tag0) ∗ memRegion (sp - 127#64) 32 ∗
      memRegion (sp - 95#64) 7 ∗ (∃∗ s88 : BitVec 32, (sp - 88#64) ↦₃₂ s88) ∗
      (∃∗ s84 : BitVec 8, (sp - 84#64) ↦₈ s84) ∗ (∃∗ s83 : BitVec 8, (sp - 83#64) ↦₈ s83) ∗
      (∃∗ s82 : BitVec 8, (sp - 82#64) ↦₈ s82) ∗ memRegion (sp - 81#64) 1 ∗
      cells (sp - 80#64) 10 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 4) (k := 172) (b' := sp - 172#64) rfl (sub_add_ofNat_eq_sub sp 176#64 172#64 4 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 172#64) (n := 4) (k := 168) (b' := sp - 168#64) rfl (sub_add_ofNat_eq_sub sp 172#64 168#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 4) (k := 164) (b' := sp - 164#64) rfl (sub_add_ofNat_eq_sub sp 168#64 164#64 4 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 164#64) (n := 1) (k := 163) (b' := sp - 163#64) rfl (sub_add_ofNat_eq_sub sp 164#64 163#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 163#64) (n := 1) (k := 162) (b' := sp - 162#64) rfl (sub_add_ofNat_eq_sub sp 163#64 162#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 162#64) (n := 1) (k := 161) (b' := sp - 161#64) rfl (sub_add_ofNat_eq_sub sp 162#64 161#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 161#64) (n := 1) (k := 160) (b' := sp - 160#64) rfl (sub_add_ofNat_eq_sub sp 161#64 160#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 152) (b' := sp - 152#64) rfl (sub_add_ofNat_eq_sub sp 160#64 152#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 151) (b' := sp - 151#64) rfl (sub_add_ofNat_eq_sub sp 152#64 151#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 151#64) (n := 23) (k := 128) (b' := sp - 128#64) rfl (sub_add_ofNat_eq_sub sp 151#64 128#64 23 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 1) (k := 127) (b' := sp - 127#64) rfl (sub_add_ofNat_eq_sub sp 128#64 127#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 127#64) (n := 32) (k := 95) (b' := sp - 95#64) rfl (sub_add_ofNat_eq_sub sp 127#64 95#64 32 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 95#64) (n := 7) (k := 88) (b' := sp - 88#64) rfl (sub_add_ofNat_eq_sub sp 95#64 88#64 7 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 84) (b' := sp - 84#64) rfl (sub_add_ofNat_eq_sub sp 88#64 84#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 1) (k := 83) (b' := sp - 83#64) rfl (sub_add_ofNat_eq_sub sp 84#64 83#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 83#64) (n := 1) (k := 82) (b' := sp - 82#64) rfl (sub_add_ofNat_eq_sub sp 83#64 82#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 1) (k := 81) (b' := sp - 81#64) rfl (sub_add_ofNat_eq_sub sp 82#64 81#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := sp - 81#64) (n := 1) (k := 80) (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 81#64 80#64 1 rfl) (by decide),
      memRegion_four (sp - 172#64), memRegion_four (sp - 168#64),
      memRegion_one (sp - 164#64), memRegion_one (sp - 163#64), memRegion_one (sp - 162#64),
      ProofLib.memRegion_eight (sp - 160#64), memRegion_one (sp - 152#64),
      memRegion_one (sp - 128#64), memRegion_four (sp - 88#64),
      memRegion_one (sp - 84#64), memRegion_one (sp - 83#64), memRegion_one (sp - 82#64),
      (ProofLib.memRegion_cells (sp - 80#64) 10 (by decide) : memRegion (sp - 80#64) 80 = cells (sp - 80#64) 10)]

private theorem memRegion_88_none_split (out : BitVec 64) :
    memRegion out 88 = (∃∗ w0 : BitVec 32, out ↦₃₂ w0) ∗ memRegion (out + 4#64) 84 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 4) (k := 84)
        (b' := out + 4#64) rfl (add_ofNat_eq_add out 4#64 4 rfl) (by decide),
      memRegion_four out]

private theorem memRegion_88_some_split (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ o0 : BitVec 32, out ↦₃₂ o0) ∗ (∃∗ o4 : BitVec 32, (out + 4#64) ↦₃₂ o4) ∗
      (∃∗ o8 : BitVec 32, (out + 8#64) ↦₃₂ o8) ∗ (∃∗ o12 : BitVec 32, (out + 12#64) ↦₃₂ o12) ∗
      (∃∗ o16 : BitVec 64, (out + 16#64) ↦₆₄ o16) ∗ (∃∗ o24 : BitVec 32, (out + 24#64) ↦₃₂ o24) ∗
      (∃∗ o28 : BitVec 64, (out + 28#64) ↦₆₄ o28) ∗ (∃∗ o36 : BitVec 8, (out + 36#64) ↦₈ o36) ∗
      (∃∗ o37 : BitVec 8, (out + 37#64) ↦₈ o37) ∗ (∃∗ o38 : BitVec 8, (out + 38#64) ↦₈ o38) ∗
      (∃∗ o39 : BitVec 64, (out + 39#64) ↦₆₄ o39) ∗ (∃∗ o47 : BitVec 64, (out + 47#64) ↦₆₄ o47) ∗
      (∃∗ o55 : BitVec 64, (out + 55#64) ↦₆₄ o55) ∗ (∃∗ o63 : BitVec 8, (out + 63#64) ↦₈ o63) ∗
      (∃∗ o64 : BitVec 64, (out + 64#64) ↦₆₄ o64) ∗ (∃∗ o72 : BitVec 64, (out + 72#64) ↦₆₄ o72) ∗
      (∃∗ o80 : BitVec 32, (out + 80#64) ↦₃₂ o80) ∗ memRegion (out + 84#64) 4 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 4) (k := 84) (b' := out + 4#64) rfl (add_ofNat_eq_add out 4#64 4 rfl) (by decide), ProofLib.memRegion_split' (b := out + 4#64) (n := 4) (k := 80) (b' := out + 8#64) rfl (add_add_ofNat_eq_add out 4#64 8#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 76) (b' := out + 12#64) rfl (add_add_ofNat_eq_add out 8#64 12#64 4 rfl) (by decide), ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 72) (b' := out + 16#64) rfl (add_add_ofNat_eq_add out 12#64 16#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64) (b' := out + 24#64) rfl (add_add_ofNat_eq_add out 16#64 24#64 8 rfl) (by decide), ProofLib.memRegion_split' (b := out + 24#64) (n := 4) (k := 60) (b' := out + 28#64) rfl (add_add_ofNat_eq_add out 24#64 28#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 28#64) (n := 8) (k := 52) (b' := out + 36#64) rfl (add_add_ofNat_eq_add out 28#64 36#64 8 rfl) (by decide), ProofLib.memRegion_split' (b := out + 36#64) (n := 1) (k := 51) (b' := out + 37#64) rfl (add_add_ofNat_eq_add out 36#64 37#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 37#64) (n := 1) (k := 50) (b' := out + 38#64) rfl (add_add_ofNat_eq_add out 37#64 38#64 1 rfl) (by decide), ProofLib.memRegion_split' (b := out + 38#64) (n := 1) (k := 49) (b' := out + 39#64) rfl (add_add_ofNat_eq_add out 38#64 39#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 39#64) (n := 8) (k := 41) (b' := out + 47#64) rfl (add_add_ofNat_eq_add out 39#64 47#64 8 rfl) (by decide), ProofLib.memRegion_split' (b := out + 47#64) (n := 8) (k := 33) (b' := out + 55#64) rfl (add_add_ofNat_eq_add out 47#64 55#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 55#64) (n := 8) (k := 25) (b' := out + 63#64) rfl (add_add_ofNat_eq_add out 55#64 63#64 8 rfl) (by decide), ProofLib.memRegion_split' (b := out + 63#64) (n := 1) (k := 24) (b' := out + 64#64) rfl (add_add_ofNat_eq_add out 63#64 64#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 64#64) (n := 8) (k := 16) (b' := out + 72#64) rfl (add_add_ofNat_eq_add out 64#64 72#64 8 rfl) (by decide), ProofLib.memRegion_split' (b := out + 72#64) (n := 8) (k := 8) (b' := out + 80#64) rfl (add_add_ofNat_eq_add out 72#64 80#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := out + 80#64) (n := 4) (k := 4) (b' := out + 84#64) rfl (add_add_ofNat_eq_add out 80#64 84#64 4 rfl) (by decide),
      memRegion_four out, memRegion_four (out + 4#64),
      memRegion_four (out + 8#64), memRegion_four (out + 12#64),
      ProofLib.memRegion_eight (out + 16#64), memRegion_four (out + 24#64),
      ProofLib.memRegion_eight (out + 28#64),
      memRegion_one (out + 36#64), memRegion_one (out + 37#64), memRegion_one (out + 38#64),
      ProofLib.memRegion_eight (out + 39#64), ProofLib.memRegion_eight (out + 47#64),
      ProofLib.memRegion_eight (out + 55#64), memRegion_one (out + 63#64),
      ProofLib.memRegion_eight (out + 64#64), ProofLib.memRegion_eight (out + 72#64),
      memRegion_four (out + 80#64)]

private def sessionRest (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) : SepProp :=
  ⌜G.alice.bytes = sess.aliceBaseKey ∧
    G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok sess.state.localIdentity.publicKey ∧
    (match sess.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = sess.state.receiverChains.length ∧
    G.pending.isSome = sess.state.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (sess.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
  vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 sess.state.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
    (G.chains.zip sess.state.receiverChains) ∗
  vecGhostAt A G.alice (ss + 0x60#64) ∗
  vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr sess.state.pqRatchetState ∗
  optSenderChainAt A (ss + 0x90#64) G.sender sess.state.senderChain ∗
  ((ss + 0x148#64) ↦₃₂ sess.state.sessionVersion) ∗
  ((ss + 0x14c#64) ↦₃₂ sess.state.previousCounter) ∗
  ((ss + 0x150#64) ↦ₛ G.regIds)

private theorem sessionAt_split (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G sess =
      ⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey⌝ ∗
      optTailVecAt A 48 (ss + 248#64) G.pending ∗
      optTailVecAt A 32 (ss + 296#64) G.kyber ∗
      sessionRest A ss G sess := by
  unfold sessionStateReprAt sessionStateAt sessionRest
  have h1 : (0xf8#64 : BitVec 64) = 248#64 := rfl
  have h2 : (0x128#64 : BitVec 64) = 296#64 := rfl
  have hp :
      ⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ =
      (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey⌝ ∗
        ⌜G.alice.bytes = sess.aliceBaseKey ∧
          G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
          (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝) := by
    rw [pure_sepConj_pure, and_assoc]
  rw [h1, h2, hp]
  sep_ac_rfl

private theorem add_one_beq_zero_of_lt_2_63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private theorem stackAt_unackItems_none_pre (sp : BitVec 64) :
    stackAt sp unackItemsStack =
      memRegion (sp - 16896#64) 336 ∗ stackAt (sp - 176#64) extHookStack ∗
      memRegion (sp - 176#64) 96 ∗ cells (sp - 80#64) 10 := by
  rw [stackAt_unackItems_outer sp, memRegion_176_none_split sp, ← sepConj_assoc]

private theorem stackAt_unackItems_none_post (sp c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 : BitVec 64) :
    memRegion (sp - 16896#64) 336 ∗ stackAt (sp - 176#64) extHookStack ∗
      memRegion (sp - 176#64) 96 ∗
      ((sp - 80#64) ↦₆₄ c9) ∗ ((sp - 72#64) ↦₆₄ c8) ∗
      ((sp - 64#64) ↦₆₄ c7) ∗ ((sp - 56#64) ↦₆₄ c6) ∗
      ((sp - 48#64) ↦₆₄ c5) ∗ ((sp - 40#64) ↦₆₄ c4) ∗
      ((sp - 32#64) ↦₆₄ c3) ∗ ((sp - 24#64) ↦₆₄ c2) ∗
      ((sp - 16#64) ↦₆₄ c1) ∗ ((sp - 8#64) ↦₆₄ c0) ⊢
    stackAt sp unackItemsStack := by
  rw [stackAt_unackItems_none_pre sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  cells_unfold
  exact Entails.sepExists_right c9 (Entails.sepExists_right c8
    (Entails.sepExists_right c7 (Entails.sepExists_right c6
      (Entails.sepExists_right c5 (Entails.sepExists_right c4
        (Entails.sepExists_right c3 (Entails.sepExists_right c2
          (Entails.sepExists_right c1 (Entails.sepExists_right c0 (Entails.refl _))))))))))

private def vecU8BufAt (A : RustAlloc) (v : VecGhost) : SepProp :=
  if v.cap = 0 then emp
  else A.live v.ptr v.cap.toNat 1 ∗ (v.ptr ↦ₛ v.bytes) ∗
    memRegion (v.ptr + BitVec.ofNat 64 v.bytes.length) (v.cap.toNat - v.bytes.length)

private theorem vecGhostAt_split (A : RustAlloc) (a : BitVec 64) (v : VecGhost) :
    vecGhostAt A v a =
      ⌜v.bytes.length ≤ v.cap.toNat ∧ v.cap.toNat < 2 ^ 63 ∧ v.ptr ≠ 0⌝ ∗
      (a ↦₆₄ v.cap) ∗ ((a + 8#64) ↦₆₄ v.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.bytes.length) ∗
      vecU8BufAt A v := by
  unfold vecGhostAt vecU8At vecHeader vecU8BufAt
  sep_ac_rfl

private def kyberCapWord : Option TailVecGhost → BitVec 64
  | none => noneCap
  | some kg => kg.vec.cap

private def optKyberRest (A : RustAlloc) (ss : BitVec 64) : Option TailVecGhost → SepProp
  | none => memRegion (ss + 304#64) 24
  | some kg =>
    ⌜kg.tail.length = 8⌝ ∗
    ⌜kg.vec.bytes.length ≤ kg.vec.cap.toNat ∧ kg.vec.cap.toNat < 2 ^ 63 ∧ kg.vec.ptr ≠ 0⌝ ∗
    ((ss + 304#64) ↦₆₄ kg.vec.ptr) ∗
    ((ss + 312#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
    vecU8BufAt A kg.vec ∗
    ((ss + 320#64) ↦ₛ kg.tail)

private theorem optTailVecAt_296_split (A : RustAlloc) (ss : BitVec 64)
    (kyG : Option TailVecGhost) :
    optTailVecAt A 32 (ss + 296#64) kyG =
      ((ss + 296#64) ↦₆₄ kyberCapWord kyG) ∗ optKyberRest A ss kyG := by
  cases kyG with
  | none =>
    dsimp only [optTailVecAt, kyberCapWord, optKyberRest]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  | some kg =>
    dsimp only [optTailVecAt, kyberCapWord, optKyberRest]
    rw [vecGhostAt_split A (ss + 296#64) kg.vec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl

private theorem stackAt_unackItems_some_post (sp : BitVec 64)
    (s172 s168 : BitVec 32) (s164 s163 s162 : BitVec 8)
    (s160 : BitVec 64) (s152 tag0 : BitVec 8)
    (bs : List (BitVec 8)) (hbs : bs.length = 32)
    (s88 : BitVec 32) (s84 s83 s82 : BitVec 8)
    (c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 : BitVec 64) :
    memRegion (sp - 16896#64) 336 ∗ stackAt (sp - 176#64) extHookStack ∗
      (memRegion (sp - 176#64) 4 ∗ ((sp - 172#64) ↦₃₂ s172) ∗
        ((sp - 168#64) ↦₃₂ s168) ∗ ((sp - 164#64) ↦₈ s164) ∗
        ((sp - 163#64) ↦₈ s163) ∗ ((sp - 162#64) ↦₈ s162) ∗
        memRegion (sp - 161#64) 1 ∗ ((sp - 160#64) ↦₆₄ s160) ∗
        ((sp - 152#64) ↦₈ s152) ∗ memRegion (sp - 151#64) 23 ∗
        ((sp - 128#64) ↦₈ tag0) ∗ ((sp - 127#64) ↦ₛ bs) ∗
        memRegion (sp - 95#64) 7 ∗ ((sp - 88#64) ↦₃₂ s88) ∗
        ((sp - 84#64) ↦₈ s84) ∗ ((sp - 83#64) ↦₈ s83) ∗
        ((sp - 82#64) ↦₈ s82) ∗ memRegion (sp - 81#64) 1 ∗
        (((sp - 80#64) ↦₆₄ c9) ∗ ((sp - 72#64) ↦₆₄ c8) ∗
         ((sp - 64#64) ↦₆₄ c7) ∗ ((sp - 56#64) ↦₆₄ c6) ∗
         ((sp - 48#64) ↦₆₄ c5) ∗ ((sp - 40#64) ↦₆₄ c4) ∗
         ((sp - 32#64) ↦₆₄ c3) ∗ ((sp - 24#64) ↦₆₄ c2) ∗
         ((sp - 16#64) ↦₆₄ c1) ∗ ((sp - 8#64) ↦₆₄ c0))) ⊢
    stackAt sp unackItemsStack := by
  rw [stackAt_unackItems_outer sp, memRegion_176_some_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_right s172 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right s168 (Entails.refl _)) ?_)
  refine sepConj_mono (Entails.sepExists_right s164 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right s163 (Entails.refl _)) ?_)
  refine sepConj_mono (Entails.sepExists_right s162 (Entails.refl _)) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_right s160 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right s152 (Entails.refl _)) (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_right tag0 (Entails.refl _)) ?_
  have hbs_mem : ((sp - 127#64) ↦ₛ bs) ⊢ memRegion (sp - 127#64) 32 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp - 127#64) bs
  refine sepConj_mono hbs_mem (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_right s88 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right s84 (Entails.refl _)) ?_)
  refine sepConj_mono (Entails.sepExists_right s83 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right s82 (Entails.refl _)) (sepConj_mono_right ?_))
  cells_unfold
  exact Entails.sepExists_right c9 (Entails.sepExists_right c8
    (Entails.sepExists_right c7 (Entails.sepExists_right c6
      (Entails.sepExists_right c5 (Entails.sepExists_right c4
        (Entails.sepExists_right c3 (Entails.sepExists_right c2
          (Entails.sepExists_right c1 (Entails.sepExists_right c0 (Entails.refl _))))))))))

private theorem optU32At_none_intro (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ v) ⊢ optU32At a none := by
  dsimp only [optU32At]
  exact sepConj_mono_right (pointsTo32_entails_memRegion (a + 4#64) v)

private theorem unackKyberSliceAt_none_intro (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ v) ⊢ unackKyberSliceAt a none := by
  dsimp only [unackKyberSliceAt]
  exact sepConj_mono_right (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem unackOutAt_some_intro (out : BitVec 64) (kyG : Option TailVecGhost)
    (kyber : Option PendingKyberPreKey) (items : PendingPreKey) (ts : SystemTime)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (pkTag pkVal : BitVec 32)
    (hpk : (out ↦₃₂ pkTag) ∗ ((out + 4#64) ↦₃₂ pkVal) ⊢ optU32At out items.preKeyId)
    (o28 : BitVec 32) :
    ((out ↦₃₂ pkTag) ∗ ((out + 4#64) ↦₃₂ pkVal)) ∗
      optU32At (out + 8#64) (kyber.map (·.preKeyId)) ∗
      ((out + 16#64) ↦₆₄ ts.tvSec) ∗ ((out + 24#64) ↦₃₂ ts.tvNsec) ∗
      ((out + 28#64) ↦₃₂ o28) ∗ ((out + 32#64) ↦ₛ items.baseKey.bytes.toList) ∗
      unackKyberSliceAt (out + 64#64) kyG ∗ ((out + 80#64) ↦₃₂ items.signedPreKeyId) ∗
      memRegion (out + 84#64) 4 ⊢
    unackOutAt out kyG kyber (some items) := by
  dsimp only [unackOutAt]
  refine Entails.sepExists_right ts (Entails.pure_right hts ?_)
  refine sepConj_mono hpk (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  exact sepConj_mono_left (pointsTo32_entails_memRegion (out + 28#64) o28)

private theorem optU32At_out_8_none_intro (out : BitVec 64) (v : BitVec 32) :
    ((out + 8#64) ↦₃₂ 0#32) ∗ ((out + 12#64) ↦₃₂ v) ⊢
    optU32At (out + 8#64) ((none : Option PendingKyberPreKey).map (·.preKeyId)) := by
  simpa only [Option.map, BitVec.add_assoc, BitVec.reduceAdd] using optU32At_none_intro (out + 8#64) v

private theorem unackKyberSliceAt_out_64_none_intro (out : BitVec 64) (v : BitVec 64) :
    ((out + 64#64) ↦₆₄ 0#64) ∗ ((out + 72#64) ↦₆₄ v) ⊢ unackKyberSliceAt (out + 64#64) none := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using unackKyberSliceAt_none_intro (out + 64#64) v

private theorem optU32At_out_8_some_intro (out : BitVec 64) (ky : PendingKyberPreKey) :
    ((out + 8#64) ↦₃₂ 1#32) ∗ ((out + 12#64) ↦₃₂ ky.preKeyId) ⊢
    optU32At (out + 8#64) ((some ky).map (·.preKeyId)) := by
  dsimp only [Option.map, optU32At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.refl _

private theorem unackKyberSliceAt_out_64_some_intro (out : BitVec 64) (kg : TailVecGhost)
    (v : BitVec 64) (hv : v = BitVec.ofNat 64 kg.vec.bytes.length) :
    ((out + 64#64) ↦₆₄ kg.vec.ptr) ∗ ((out + 72#64) ↦₆₄ v) ⊢ unackKyberSliceAt (out + 64#64) (some kg) := by
  subst hv; dsimp only [unackKyberSliceAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.refl _

private def vecU8LiveRest (A : RustAlloc) (v : VecGhost) : SepProp :=
  if v.cap = 0 then emp
  else A.live v.ptr v.cap.toNat 1 ∗ memRegion (v.ptr + BitVec.ofNat 64 v.bytes.length) (v.cap.toNat - v.bytes.length)

private theorem vecU8BufAt_eq_of_le (A : RustAlloc) (v : VecGhost) (hle : v.bytes.length ≤ v.cap.toNat) :
    vecU8BufAt A v = (v.ptr ↦ₛ v.bytes) ∗ vecU8LiveRest A v := by
  unfold vecU8BufAt vecU8LiveRest; split
  · next h0 =>
    have hcap0 : v.cap.toNat = 0 := by rw [h0]; rfl
    simp [List.eq_nil_of_length_eq_zero (by omega : v.bytes.length = 0)]
  · sep_ac_rfl

private theorem sessionAt_some_none_intro (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (g : TailVecGhost) (items : PendingPreKey)
    (hgp : G.pending = some g) (hppk : sess.pendingPreKey = some items)
    (hgk : G.kyber = none) (hky : sess.pendingKyberPreKey = none)
    (hpend : PendingRel (some g) (some items)) (htail : g.tail.length = 24)
    (hvec : g.vec.bytes.length ≤ g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63 ∧ g.vec.ptr ≠ 0) :
    ((ss + 248#64) ↦₆₄ g.vec.cap) ∗ ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
      ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ (g.vec.ptr ↦ₛ g.vec.bytes) ∗ vecU8LiveRest A g.vec ∗
      ((ss + 272#64) ↦ₛ g.tail) ∗ ((ss + 296#64) ↦₆₄ noneCap) ∗ memRegion (ss + 304#64) 24 ∗
      sessionRest A ss G sess ⊢ sessionStateReprAt A ss G sess := by
  rw [sessionAt_split, hgp, hgk]
  refine Entails.pure_right (by rw [hppk, hky]; exact ⟨hpend, trivial⟩) ?_
  dsimp only [optTailVecAt, Nat.reduceSub]
  rw [vecGhostAt_split A (ss + 248#64) g.vec, vecU8BufAt_eq_of_le A g.vec hvec.1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.pure_right htail (Entails.pure_right hvec (Entails.refl _))

private theorem sessionAt_some_some_intro (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (g kg : TailVecGhost)
    (items : PendingPreKey) (ky : PendingKyberPreKey)
    (hgp : G.pending = some g) (hppk : sess.pendingPreKey = some items)
    (hgk : G.kyber = some kg) (hky : sess.pendingKyberPreKey = some ky)
    (hpend : PendingRel (some g) (some items)) (hkyRel : KyberRel (some kg) (some ky))
    (htail : g.tail.length = 24)
    (hvec : g.vec.bytes.length ≤ g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63 ∧ g.vec.ptr ≠ 0)
    (hkgTail : kg.tail.length = 8)
    (hkgVec : kg.vec.bytes.length ≤ kg.vec.cap.toNat ∧ kg.vec.cap.toNat < 2 ^ 63 ∧ kg.vec.ptr ≠ 0) :
    ((ss + 248#64) ↦₆₄ g.vec.cap) ∗ ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
      ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ (g.vec.ptr ↦ₛ g.vec.bytes) ∗ vecU8LiveRest A g.vec ∗
      ((ss + 272#64) ↦ₛ g.tail) ∗ ((ss + 296#64) ↦₆₄ kg.vec.cap) ∗ ((ss + 304#64) ↦₆₄ kg.vec.ptr) ∗
      ((ss + 312#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗ vecU8BufAt A kg.vec ∗ ((ss + 320#64) ↦ₛ kg.tail) ∗
      sessionRest A ss G sess ⊢ sessionStateReprAt A ss G sess := by
  rw [sessionAt_split, hgp, hgk]
  have hrel : PendingRel (some g) sess.pendingPreKey ∧ KyberRel (some kg) sess.pendingKyberPreKey := by
    rw [hppk, hky]; exact ⟨hpend, hkyRel⟩
  refine Entails.pure_right hrel ?_
  dsimp only [optTailVecAt, Nat.reduceSub]
  rw [vecGhostAt_split A (ss + 248#64) g.vec, vecU8BufAt_eq_of_le A g.vec hvec.1,
      vecGhostAt_split A (ss + 296#64) kg.vec]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.pure_right htail (Entails.pure_right hvec ?_)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact Entails.pure_right hkgTail (Entails.pure_right hkgVec (Entails.refl _))

private theorem cells_10_sp_80 (sp : BitVec 64) :
    cells (sp - 80#64) 10 =
      ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c6 : BitVec 64,
        ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c2 : BitVec 64,
          ∃∗ c1 : BitVec 64, ∃∗ c0 : BitVec 64,
            ((sp - 80#64) ↦₆₄ c9) ∗ ((sp - 72#64) ↦₆₄ c8) ∗
            ((sp - 64#64) ↦₆₄ c7) ∗ ((sp - 56#64) ↦₆₄ c6) ∗
            ((sp - 48#64) ↦₆₄ c5) ∗ ((sp - 40#64) ↦₆₄ c4) ∗
            ((sp - 32#64) ↦₆₄ c3) ∗ ((sp - 24#64) ↦₆₄ c2) ∗
            ((sp - 16#64) ↦₆₄ c1) ∗ ((sp - 8#64) ↦₆₄ c0) := by
  cells_unfold

private theorem SepWP.pure_elim_focus {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} (φ : Prop)
    (h : φ → SepWP prog target_pc s P' post)
    (hf : P = ⌜φ⌝ ∗ P') :
    SepWP prog target_pc s P post :=
  hf ▸ SepWP.pure_elim h

private theorem optTailVecAt_248_none (A : RustAlloc) (ss : BitVec 64) :
    optTailVecAt A 48 (ss + 248#64) none =
      ((ss + 248#64) ↦₆₄ noneCap) ∗ memRegion (ss + 256#64) 40 := by
  dsimp only [optTailVecAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem sessionAt_none_intro (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (hgp : G.pending = none) (hppk : sess.pendingPreKey = none)
    (hkyRel : KyberRel G.kyber sess.pendingKyberPreKey) :
    ((ss + 248#64) ↦₆₄ noneCap) ∗ memRegion (ss + 256#64) 40 ∗
      optTailVecAt A 32 (ss + 296#64) G.kyber ∗ sessionRest A ss G sess ⊢
    sessionStateReprAt A ss G sess := by
  rw [sessionAt_split, hgp, optTailVecAt_248_none, sepConj_assoc]
  have hp : PendingRel none sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey := by
    rw [hppk]; exact ⟨trivial, hkyRel⟩
  exact Entails.pure_right hp (Entails.refl _)

private theorem unackOutAt_none_intro (out : BitVec 64) (kyG : Option TailVecGhost)
    (kyber : Option PendingKyberPreKey) :
    (out ↦₃₂ 2#32) ∗ memRegion (out + 4#64) 84 ⊢ unackOutAt out kyG kyber none :=
  Entails.refl _

private theorem SepWPp.pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P' Q Qp oom)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.congr_pre hf (SepWPp.pure_left h)

private theorem SepWPp.of_sepWP_ret {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hpost⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem SepWPp.of_sepWP {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hcont R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

private theorem SepWPp.call_frame {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hf : P = T ∗ F)
    (hexit : ∀ code sf R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R')) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  let specF : Spec Unit :=
    { pre := fun _ s0 => ⌜s0 = s⌝ ∗ (spec.pre x s ∗ F)
      post := fun _ _ sf => spec.post x s sf ∗ F
      onPanic := fun _ _ sf => spec.onPanic x s sf ∗ F
      onExit := fun _ _ _ _ => ⌜False⌝
      onOom := fun _ _ sf => spec.onOom x s sf ∗ F }
  have hcallF : subroutine_ok prog entry specF := by
    refine Arm64.subroutine_ok_outcome_intro fun _ R' s0 hpc0 hrun0 hpre0 hsp0 => ?_
    dsimp only [specF] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨rfl, hpre0⟩
    rw [sepConj_assoc] at hpre0
    refine hcall.mono_outcome x (F ∗ R') s0 hpc0 hrun0 hpre0 hsp0 fun sm hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex_st, hpost⟩ | ⟨hoom_st, hpost⟩
    · rw [← sepConj_assoc] at hpost; exact Or.inl ⟨hret, hcc, hpost⟩
    · rw [← sepConj_assoc] at hpost; exact Or.inr (Or.inl ⟨hpan_st, hpost⟩)
    · exact (hexit code sm R' hex_st hpost).elim
    · rw [← sepConj_assoc] at hpost; exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hpost⟩))
  refine ProofLib.SepWPp.call (x := ()) (F := emp) hcallF hpc hrun hsp_align hlr
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sm hpan_st => by dsimp only [specF]; rw [sepConj_emp]; exact hpan sm hpan_st)
    (fun sm hpcm hrunm hspm hcsm => by dsimp only [specF]; rw [sepConj_emp]; exact hnext sm hpcm hrunm hspm hcsm)
    (fun sm R' hoom_st hpost => by
      dsimp only [specF] at hpost
      rw [emp_sepConj, sepConj_assoc] at hpost
      exact hoom sm R' hoom_st hpost)
  dsimp only [specF]
  rw [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  rw [hf, sepConj_assoc] at hm
  rw [hpre_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, hm⟩

private theorem lsLogOff_eq [LibsignalPlacement] :
    lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

/-! ## Relocatable `[LibsignalPlacement]` Contract and Proofs -/

def unackItemsPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec UnackCall :=
  withVmPreserved
    (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)

private def unackItemsPlacedSpecWhere [LibsignalPlacement] (A : RustAlloc)
    (P : UnackCall → Prop) : Spec UnackCall :=
  let S := withLsCodeLoaded lsmpl (unackItemsPlacedSpec A)
  { S with pre := fun x s => ⌜P x⌝ ∗ S.pre x s }

private theorem unackItems_placed_ok_none [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_36 H) (blkPl_36).base
      (unackItemsPlacedSpecWhere A (fun x => x.sess.pendingPreKey = none)) := by
  simp only [unackItemsPlacedSpecWhere, withLsCodeLoaded, Obj.MultiPlacedLib.withCodeLoaded,
    unackItemsPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec]
  wpp_init x s0
  rcases x with ⟨ss, G, sess, out⟩; dsimp only at *
  have hppk : sess.pendingPreKey = none := by assumption
  nth_rw 1 [sessionAt_split]
  apply SepWPp.pure_elim_focus (PendingRel G.pending sess.pendingPreKey ∧
    KyberRel G.kyber sess.pendingKyberPreKey); intro ⟨hpendRel, hkyRel⟩
  cases hgp : G.pending with
  | some g => rw [hppk, hgp] at hpendRel; exact False.elim hpendRel
  | none =>
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [hppk, optTailVecAt_248_none, memRegion_88_none_split, stackAt_unackItems_none_pre, cells_10_sp_80]
    wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_36).rebase (blkPl_36).base (hooksException H)) blkLib_eq_36
      (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip
    wp_steps 11
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit]; wp_steps 10
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
    simp only [wp_norm, arm64_norm] at hvm
    refine SepWP.fold (sessionAt_none_intro A ss G sess hgp hppk hkyRel) (by sep_focus) ?_
    refine SepWP.fold (unackOutAt_none_intro out G.kyber sess.pendingKyberPreKey) (by sep_focus) ?_
    refine SepWP.fold (stackAt_unackItems_none_post s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    wp_done

set_option maxHeartbeats 1200000 in
private theorem unackItems_placed_ok_some [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (htime_sat : HookSat H lsTimeAddSym (withLsRet timeAddBudgetSpec)) :
    subroutine_ok (lsProg_36 H) (blkPl_36).base
      (unackItemsPlacedSpecWhere A (fun x => ∃ items, x.sess.pendingPreKey = some items)) := by
  have hdeser : subroutine_ok (lsProg_36 H) (lsmpl.base 201) (withLsCl lsmpl deserializePlacedVmSpec) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_36 H) (deserialize_placed_ok_vm H)
  have htime :=
    subroutine_ok_merge_withLsRet (fun _ _ => rfl)
      (ls_hook_ok_of_mem (prog := lsProg_36 H) (i := 36) htime_sat)
  dsimp only [withLsCl, deserializePlacedVmSpec, deserializePlacedSpec] at hdeser
  simp only [unackItemsPlacedSpecWhere, withLsCodeLoaded, Obj.MultiPlacedLib.withCodeLoaded,
    unackItemsPlacedSpec, withVmPreserved, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec]
  wpp_init x s0
  rcases x with ⟨ss, G, sess, out⟩; dsimp only at *
  obtain ⟨items, hppk⟩ : ∃ items, sess.pendingPreKey = some items := by assumption
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  nth_rw 1 [sessionAt_split]
  apply SepWPp.pure_elim_focus (PendingRel G.pending sess.pendingPreKey ∧
    KyberRel G.kyber sess.pendingKyberPreKey); intro ⟨hpendRel, hkyRel⟩
  cases hgp : G.pending with
  | none => rw [hppk, hgp] at hpendRel; exact False.elim hpendRel
  | some g =>
    rw [hppk, hgp] at hpendRel
    have hpendRel' : PendingRel (some g) (some items) := hpendRel
    rcases hpendRel with ⟨hdeserOk, hpkRel, htsRel, hspkRel, _⟩
    rw [optTailVecAt_296_split A ss G.kyber]; dsimp only [optTailVecAt, Nat.reduceSub]
    apply SepWPp.pure_elim_focus (g.tail.length = 24); intro htailLen
    rw [vecGhostAt_split A (ss + 248#64) g.vec]
    apply SepWPp.pure_elim_focus (g.vec.bytes.length ≤ g.vec.cap.toNat ∧
      g.vec.cap.toNat < 2 ^ 63 ∧ g.vec.ptr ≠ 0); intro ⟨hlen_le, hcap_lt, hptr_ne⟩
    have hlen_lt : g.vec.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
    have hlen_toNat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
      rw [BitVec.toNat_ofNat]; omega
    obtain ⟨pkTag, pkVal, hpTail, hpkEnt⟩ :=
      pendingTail_pointsToBytes ss g.tail items htailLen hpkRel htsRel hspkRel
    obtain ⟨bk0, bk1, bk2, bk3, bk4, bk5, bk6, bk7, bk15, bk23, bk31, hbk⟩ :=
      exists_baseKeyChunks_of_length_32 (List.Vector.toList_length items.baseKey.bytes)
    have hbk_sp := Entails.of_eq ((hbk (s0.sp - 127#64)).trans
      (baseKeyChunks_sp_127 s0.sp bk0 bk1 bk2 bk3 bk4 bk5 bk6 bk7 bk15 bk23 bk31)).symm
    have hbk_out := Entails.of_eq ((hbk (out + 32#64)).trans
      (baseKeyChunks_out_32 out bk0 bk1 bk2 bk3 bk4 bk5 bk6 bk7 bk15 bk23 bk31)).symm
    apply SepWPp.of_sepWP (mid := lsρ lsTimeAddSym)
    wp_simp_pre [vecU8BufAt_eq_of_le A g.vec hlen_le, stackAt_unackItems_outer,
      memRegion_176_some_split, memRegion_32_eq_exists_bytes, cells_10_sp_80,
      lsLogOff_eq, BitVec.add_assoc, BitVec.reduceAdd]
    rw [hpTail]; wp_pull_exists
    rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 s82 s83 s84 s88 bs tag0 s152 s160 s162 s163 s164 s168 s172
    refine SepWP.pure_elim_focus (bs.length = 32) ?_ (by sep_focus); intro hbs_len
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 201)
    apply sepWP_seg_ls_vm (Q := (blkPC_36).rebase (blkPl_36).base (hooksException H)) blkLib_eq_36
      (mid := lsmpl.base 201)
    intro _m_strip1
    wp_steps 11
    conv => arg 3; simp only [add_one_beq_zero_of_lt_2_63 hcap_lt, Bool.false_eq_true, ↓reduceIte]
    wp_steps 8
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    apply sepWP_seg_ls_vm (Q := (blkPC_36).rebase (blkPl_36).base (hooksException H)) blkLib_eq_36
      (mid := lsρ lsTimeAddSym)
    intro _m_strip2
    wp_simp_pre [← lsLogOff_eq, hbk (s0.sp - 127#64), baseKeyChunks_sp_127,
      BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit]
    wp_steps 3; wp_simp_pre [sevenLo_sp_127]; wp_steps 1; wp_simp_pre [← sevenLo_sp_127]
    apply blkPC_36_pairStep_0x84 _ _ rfl (by wp_norm_lhs) (by wp_norm_lhs)
    wp_steps 4; wp_simp_pre [sevenLo_sp_88]; wp_steps 1; wp_simp_pre [← sevenLo_sp_88]; wp_steps 1
    refine SepWP.fold hbk_sp (by sep_focus) ?_
    wp_steps 7
    refine SepWP.fold (Entails.of_eq hpTail.symm) (by sep_focus) ?_
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame htime (x := (SystemTime.unixEpoch, items.timestamp.toNat))
      (ret_pc := (blkPl_36).base + 192#64) (T := stackAt (s0.sp - 176#64) extHookStack)
      (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_goal)
      (by dsimp only [timeAddBudgetSpec, withVmPreserved, timeAddSpec]; congr 2)
      ?_ (by sep_focus)
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf _ h => by
        rw [← sepConj_assoc]
        exact allowPanic_frame (fun ⟨hts_none, htr⟩ =>
          ⟨⟨items, hppk, hts_none⟩, by simp only [arm64_norm, hpost] at htr; exact htr⟩) h) ?_
    · exact ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 36 192#64 (by wp_norm_lhs),
        by wp_norm_lhs, by wp_norm_lhs, by decide, by wp_norm_lhs, by wp_norm_lhs⟩
    intro sf hpcf hrunf hspf hcsf
    replace hspf : sf.sp = s0.sp - 176#64 := by rw [hspf]; wp_norm_lhs
    dsimp only [CalleeSavedPreserved] at hcsf
    rcases hcsf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs⟩
    replace hx19 : sf.readReg64 (.gpr 19#5) = out := by rw [hx19]; wp_norm_lhs
    replace hx20 : sf.readReg64 (.gpr 20#5) = ss := by rw [hx20]; wp_norm_lhs
    replace hx21 : sf.readReg64 (.gpr 21#5) = BitVec.zeroExtend 64 items.signedPreKeyId := by rw [hx21]; wp_norm_lhs
    replace hx22 : sf.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 pkTag := by rw [hx22]; wp_norm_lhs
    replace hx23 : sf.readReg64 (.gpr 23#5) = BitVec.zeroExtend 64 pkVal := by rw [hx23]; wp_norm_lhs
    replace hx24 : sf.readReg64 (.gpr 24#5) = bk15 := by rw [hx24]; wp_norm_lhs
    replace hx25 : sf.readReg64 (.gpr 25#5) = bk7 := by rw [hx25]; wp_norm_lhs
    replace hx26 : sf.readReg64 (.gpr 26#5) = kyberCapWord G.kyber := by rw [hx26]; wp_norm_lhs
    replace hx27 : sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := by rw [hx27]; wp_norm_lhs
    replace hx28 : sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) := by rw [hx28]; wp_norm_lhs
    replace hx29 : sf.readReg64 (.gpr 29#5) = s0.sp - 80#64 := by rw [hx29]; wp_norm_lhs
    replace hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by rw [hvregs]; wp_norm_lhs
    dsimp only [timeAddBudgetSpec, withVmPreserved, timeAddSpec]
    rw [show (stackAt (State.sp _) extHookStack) = stackAt (s0.sp - 176#64) extHookStack from
      congrArg (stackAt · extHookStack) (by wp_norm_lhs)]
    apply SepWPp.pure_elim_focus (VmPreserved _ sf); intro hvm_time
    apply SepWPp.pure_elim_focus (SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat =
      some ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ ∧ sf.trace = _)
    rintro ⟨hts_some, htr_sf⟩
    replace htr_sf : sf.trace = s0.trace := by rw [htr_sf]; simp only [arm64_norm, hpost]
    cases hky : sess.pendingKyberPreKey with
    | none =>
      cases hgk : G.kyber with
      | some kg => rw [hky, hgk] at hkyRel; exact False.elim hkyRel
      | none =>
        simp only [hgk, kyberCapWord, noneCap] at hx26
        apply SepWPp.of_sepWP_ret
        wp_simp_pre [hppk, hky, kyberCapWord, optKyberRest, memRegion_88_some_split,
          BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit]
        wp_pull_exists
        apply sepWP_seg_ls_vm (Q := (blkPC_36).rebase (blkPl_36).base (hooksException H)) blkLib_eq_36
          (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip3
        wp_steps 5
        wp_simp_pre [sevenLo_sp_88]; wp_steps 1; wp_simp_pre [← sevenLo_sp_88]
        wp_steps 3; wp_simp_pre [sevenLo_sp_168]; wp_steps 1
        wp_simp_pre [← sevenLo_sp_168, pointsTo32_32_sp_172]; wp_steps 1
        wp_simp_pre [← pointsTo32_32_sp_172]; wp_steps 4
        wp_simp_pre [← pointsTo32_32_out_28, sevenLo_out_32]; wp_steps 1
        wp_simp_pre [← sevenLo_out_32]; wp_steps 14
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm3 : VmPreserved sf _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        have hvm_tot : VmPreserved s0 _ :=
          vmPreserved_trans_eq (vmPreserved_trans_eq hvm1 (vmPreserved_prepend hvm2)) (hvm_time.trans hvm3)
        simp only [wp_norm, arm64_norm] at hvm_tot
        refine SepWP.fold hbk_out (by sep_focus) ?_
        refine SepWP.fold (sessionAt_some_none_intro A ss G sess g items hgp hppk hgk hky
          hpendRel' htailLen ⟨hlen_le, hcap_lt, hptr_ne⟩) (by sep_focus) ?_
        refine SepWP.fold (optU32At_out_8_none_intro out _) (by sep_focus) ?_
        refine SepWP.fold (unackKyberSliceAt_out_64_none_intro out _) (by sep_focus) ?_
        refine SepWP.fold (unackOutAt_some_intro out none none items
          ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ hts_some pkTag pkVal
          (hpkEnt out) _) (by sep_focus) ?_
        refine SepWP.fold (stackAt_unackItems_some_post s0.sp _ _ _ _ _ _ _ _
          items.baseKey.bytes.toList (List.Vector.toList_length items.baseKey.bytes)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
    | some ky =>
      cases hgk : G.kyber with
      | none => rw [hky, hgk] at hkyRel; exact False.elim hkyRel
      | some kg =>
        have hkyRel' : KyberRel (some kg) (some ky) := by rwa [hky, hgk] at hkyRel
        rcases hkyRel' with ⟨hkyBytes, hkyTake⟩
        simp only [hgk, kyberCapWord] at hx26
        dsimp only [kyberCapWord, optKyberRest]
        apply SepWPp.pure_elim_focus (kg.tail.length = 8); intro hkgTailLen
        apply SepWPp.pure_elim_focus (kg.vec.bytes.length ≤ kg.vec.cap.toNat ∧
          kg.vec.cap.toNat < 2 ^ 63 ∧ kg.vec.ptr ≠ 0); intro hkgVec
        have hkyTail := kyberTail_pointsToBytes ss kg.tail ky hkgTailLen hkyTake
        apply SepWPp.of_sepWP_ret
        wp_simp_pre [hppk, hky, hkyTail, memRegion_88_some_split,
          BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit]
        wp_pull_exists
        apply sepWP_seg_ls_vm (Q := (blkPC_36).rebase (blkPl_36).base (hooksException H)) blkLib_eq_36
          (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip3
        wp_steps 2
        conv => arg 3; simp only [add_one_beq_zero_of_lt_2_63 hkgVec.2.1, Bool.false_eq_true, ↓reduceIte]
        wp_steps 5; wp_simp_pre [sevenLo_sp_88]; wp_steps 1; wp_simp_pre [← sevenLo_sp_88]
        wp_steps 3; wp_simp_pre [sevenLo_sp_168]; wp_steps 1
        wp_simp_pre [← sevenLo_sp_168, pointsTo32_32_sp_172]; wp_steps 1
        wp_simp_pre [← pointsTo32_32_sp_172]; wp_steps 4
        wp_simp_pre [← pointsTo32_32_out_28, sevenLo_out_32]; wp_steps 1
        wp_simp_pre [← sevenLo_out_32]; wp_steps 14
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm3 : VmPreserved sf _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        have hvm_tot : VmPreserved s0 _ :=
          vmPreserved_trans_eq (vmPreserved_trans_eq hvm1 (vmPreserved_prepend hvm2)) (hvm_time.trans hvm3)
        simp only [wp_norm, arm64_norm] at hvm_tot
        refine SepWP.fold hbk_out (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq hkyTail.symm) (by sep_focus) ?_
        refine SepWP.fold (sessionAt_some_some_intro A ss G sess g kg items ky hgp hppk hgk hky
          hpendRel' ⟨hkyBytes, hkyTake⟩ htailLen ⟨hlen_le, hcap_lt, hptr_ne⟩ hkgTailLen hkgVec)
          (by sep_focus) ?_
        refine SepWP.fold (optU32At_out_8_some_intro out ky) (by sep_focus) ?_
        refine SepWP.fold (unackKyberSliceAt_out_64_some_intro out kg _ (by rw [hkyBytes])) (by sep_focus) ?_
        refine SepWP.fold (unackOutAt_some_intro out (some kg) (some ky) items
          ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ hts_some pkTag pkVal
          (hpkEnt out) _) (by sep_focus) ?_
        refine SepWP.fold (stackAt_unackItems_some_post s0.sp _ _ _ _ _ _ _ _
          items.baseKey.bytes.toList (List.Vector.toList_length items.baseKey.bytes)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        wp_done

theorem unackItems_ls_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (htime_sat : HookSat H lsTimeAddSym (withLsRet timeAddBudgetSpec)) :
    subroutine_ok (lsProg_36 H) (blkPl_36).base
      (withLsCodeLoaded lsmpl (unackItemsPlacedSpec A)) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  cases hppk : x.sess.pendingPreKey with
  | none =>
    exact unackItems_placed_ok_none.mono_outcome x R s0 hpc hrun
      (by dsimp only [unackItemsPlacedSpecWhere]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hppk, hpre⟩)
      hsp fun _ hout => hout
  | some items =>
    exact (unackItems_placed_ok_some htime_sat).mono_outcome x R s0 hpc hrun
      (by dsimp only [unackItemsPlacedSpecWhere]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨items, hppk⟩, hpre⟩)
      hsp fun _ hout => hout

theorem unackItems_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (htime_sat : HookSat H lsTimeAddSym timeAddBudgetSpec) :
    subroutine_ok (lsProg_36 H) (blkPl_36).base
      (withLsCodeLoaded lsmpl (unackItemsPlacedSpec A)) :=
  unackItems_ls_placed_ok (hookSat_withLsRet htime_sat)

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
