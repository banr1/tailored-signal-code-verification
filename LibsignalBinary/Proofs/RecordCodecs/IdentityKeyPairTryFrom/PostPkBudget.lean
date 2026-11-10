/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPk
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOkBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Post-Loop Public-Key Validation

`RustCliAllocBudget`-threaded relocatable proof of the post-loop `PublicKey::try_from` call and
error dispatch (`+344 .. +392`, `+688 .. +756`) on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPkBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
  hiding rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
    decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
  hiding dropDecodeErrorSpecGen dropDecodeErrorSpecX decodeVarintSliceSpecGen decodeVarintSliceSpecX memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary
  (DecodeGhost identityKeyPairResultAt ls_subroutine_ok_lscro_of_plain sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
  hiding post_pk_ok_396_placed_wp err_store_760_placed_wp
open scoped CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced TwoOptByteFreeEnv noPanicQp sepWPp_frame_noPanic sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOkBudget
  (post_pk_ok_396_placed_wp err_store_760_placed_wp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPkStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pk (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_pk (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_pk (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_pk (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_pk (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_pk (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_pk (s : State) : s.advancePC.sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_pk (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by
  cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pk (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_pk (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_pk (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end PostPkStateSimp

private theorem pkErr_fold_spe7 (sp' : BitVec 64) (b9 : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 0#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 0#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 0#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    memRegion_split (sp' + 96#64) 1 47 (by decide),
    memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe8 (sp' : BitVec 64) (t : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 1#8) ∗ ((sp' + 105#64) ↦₈ t) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 1#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm105 : ((sp' + 105#64) ↦₈ t) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ t
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    memRegion_split (sp' + 96#64) 1 47 (by decide),
    memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe9 (sp' : BitVec 64) (b9 : BitVec 8) (n : Nat) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 2#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 6 ∗ ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (sp' + 120#64) 16 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 2#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 2#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (6 + (8 + (16 + 8)))))) by decide,
    memRegion_split (sp' + 96#64) 1 47 (by decide),
    memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 6 32 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64) 8 24 (by decide),
    memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64 + 8#64) 16 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104
      (sepConj_mono hm105
        (sepConj_mono_right (sepConj_mono_left
          (pointsTo64_entails_memRegion (sp' + 112#64) (BitVec.ofNat 64 n)))))))

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

set_option maxHeartbeats 800000 in
private theorem pkTryFrom_vm_placed_ok_blk [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base (withVmPreserved pkTryFromPlacedSpec) := by
  apply subroutine_ok_withVmPreserved_intro
  intro g R s0 h_pc h_run h_pre h_sp_align
  obtain ⟨ptr, bs, out⟩ := g
  simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff] at h_pre ⊢
  have hpure : s0.readReg64 (Reg.gpr 0#5) = ptr ∧
      (s0.readReg64 (Reg.gpr 1#5)).toNat = bs.length ∧
      s0.readReg64 (Reg.gpr 8#5) = out := by
    have hsat := h_pre
    simp only [Reg.x0, Reg.x1, Reg.x8, sepConj_assoc, satisfies_pure_sepConj] at hsat
    exact hsat.1
  rcases hpure with ⟨h, h_2, h_1⟩
  dsimp only [Reg.x0, Reg.x1, Reg.x8, Reg.x30] at *
  subst h_1 h
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun _ => ?_
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [PublicKeyTryFrom.publicKey_deserialize_nil, pkTryFromResultAt,
      PublicKeyTryFrom.memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    by_vm_steps (
      wp_pull_exists
      wp_steps
      refine SepWP.weaken_pre
        (PublicKeyTryFrom.nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5))
          (s0.readReg64 (Reg.gpr 8#5)) lsLogFilterAddr) ?_
      wp_done
    )
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          PublicKeyTryFrom.ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [PublicKeyTryFrom.publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons,
          PublicKeyTryFrom.memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        by_vm_steps (
          wp_pull_exists
          wp_steps
          have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
            apply BitVec.eq_of_toNat_eq
            simp only [List.length_cons] at h_2
            rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [hx1_eq]
          refine SepWP.weaken_pre
            (PublicKeyTryFrom.badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5))
              (s0.readReg64 (Reg.gpr 8#5)) (BitVec.ofNat 64 (rest.length + 1))
              lsLogFilterAddr rest) ?_
          wp_done
        )
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          PublicKeyTryFrom.ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [PublicKeyTryFrom.publicKey_deserialize_ok_of_ge32 rest hge32]
        dsimp only [pkTryFromResultAt, List.Vector.toList]
        rw [PublicKeyTryFrom.pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          PublicKeyTryFrom.memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
          (Q := (blkPC_211).rebase (blkPl_211).base
            (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
          CryptoVerification.blkLib_eq_211 (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip
        wp_steps
        wp_if hcbz9
        · wp_steps
          refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [h_run, wp_norm, arm64_norm]) fun _m_real _hnsp => ?_
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [h_run, wp_norm, arm64_norm])
            ⟨_hnsp.toVmPreserved (by simp [wp_norm, arm64_norm]),
             fun hm_sat => ?_,
             by simp [wp_norm, arm64_norm],
             by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [wp_norm, arm64_norm]⟩
          rw [satisfies_pure_sepConj]
          exact ⟨by simp [wp_norm, arm64_norm], by convert hm_sat using 1; sep_ac_rfl⟩
        · wp_steps
          refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [h_run, wp_norm, arm64_norm]) fun _m_real _hnsp => ?_
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          refine ProofLib.SepWP.done (by simp [wp_norm, arm64_norm])
            (by simp [h_run, wp_norm, arm64_norm])
            ⟨_hnsp.toVmPreserved (by simp [wp_norm, arm64_norm]),
             fun hm_sat => ?_,
             by simp [wp_norm, arm64_norm],
             by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [wp_norm, arm64_norm]⟩
          rw [satisfies_pure_sepConj]
          exact ⟨by simp [wp_norm, arm64_norm], by convert hm_sat using 1; sep_ac_rfl⟩
    · rw [PublicKeyTryFrom.publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons,
        PublicKeyTryFrom.memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      by_vm_steps (
        wp_pull_exists
        wp_steps
        wp_done
      )

private theorem ikp_pkTryFrom_vm_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_84 H) (lsmpl.base 211)
      (withLsCodeRoLoaded lsmpl (withVmPreserved pkTryFromPlacedSpec)) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_84 H) (pkTryFrom_vm_placed_ok_blk H)

theorem post_344_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {m : IdentityKeyPairStructure}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk_lt : m.publicKey.length < 2 ^ 64) (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (344)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 m.publicKey.length) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ memRegion x.ret 72 ∗
        vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗ vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          lsLogOff ∗
          (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  have hm96_split : memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 40 ∗ memRegion (sp' + 136#64) 8 := by
    have hs := memRegion_split (sp' + 96#64) 40 8 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; exact hs
  have hpk_unpack : vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ⊢
      (pkPtr ↦ₛ m.publicKey) ∗ vecU8BufRest A.repAlloc pkCap pkPtr m.publicKey :=
    Entails.trans (vecU8Buf_entails_slice_rest A.repAlloc pkCap pkPtr m.publicKey)
      (Entails.pure_left fun _ => Entails.refl _)
  refine SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono (Entails.of_eq hm96_split)
        (sepConj_mono_right (sepConj_mono_left hpk_unpack)))) ?_
  simp only [sepConj_assoc]
  have hcall := ikp_pkTryFrom_vm_placed_ok H
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  have _hsp_align := hst.spAligned
  have _hx1_nat : (BitVec.ofNat 64 m.publicKey.length).toNat = m.publicKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpk_lt]
  have ha96 : sp' + 144#64 - 48#64 = sp' + 96#64 := by bv_omega
  refine sepWPp_of_sepWP_lscro hst.crl (mid := lsmpl.base 211) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (pkPtr, m.publicKey, sp' + 96#64) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (356))
    (by simp [*, hst.trace, arm64_norm])
    (T := (pkPtr ↦ₛ m.publicKey) ∗ memRegion (sp' + 96#64) 40 ∗ lsLogOff)
    (φ := pkPtr = pkPtr ∧ m.publicKey.length = m.publicKey.length ∧ sp' + 144#64 - 48#64 = sp' + 96#64)
    (by simp [*, withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec, arm64_norm])
    ⟨rfl, rfl, ha96⟩ (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_pre fun hvm2 => ?_
  refine SepWPp.pure_pre fun htr2 => ?_
  have hpool_s2 : A.pool lim st s = A.pool lim st s2 := by
    have hp2 := (A.pool_transport lim st _ s2 hvm2).symm
    simpa [arm64_norm] using hp2
  have hst1 := hst.of_steps hcrl1 (by tryFromPost_sp [hsp_eq])
    (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
    (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm])
  have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
  have _hsp2_eq := hst2.sp
  have _hsp2_align := hst2.spAligned
  have _hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp [*, arm64_norm])
  have _hx20_2 : s2.readReg64 .x20 = pkPtr := hcs2.2.1.trans (by simp [*, arm64_norm])
  have _hx21_2 : s2.readReg64 .x21 = skCap := hcs2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx22_2 : s2.readReg64 .x22 = pkCap := hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx23_2 : s2.readReg64 .x23 = skPtr := hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length :=
    hcs2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx29_2 : s2.readReg64 .x29 = sp' + 144#64 :=
    hcs2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29] at _hx19_2 _hx20_2 _hx21_2 _hx22_2 _hx23_2 _hx24_2 _hx25_2 _hx29_2
  have hpk_fold := slice_rest_entails_vecU8Buf A.repAlloc pkCap pkPtr m.publicKey
  refine SepWPp.mono_pre
    (P' := pkTryFromResultAt (sp' + 96#64) (PublicKey.deserialize m.publicKey) ∗
      memRegion (sp' + 136#64) 8 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
      vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗ vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
      lsLogOff ∗ A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100))
    (by rw [hpool_s2]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpk_fold)))))
        apply entails_of_eq; sep_ac_rfl) ?_
  cases hpk : PublicKey.deserialize m.publicKey with
  | ok pk =>
    dsimp only [pkTryFromResultAt]
    obtain ⟨w0, b8, w9, h13, w15, w23, b31, hpk_cells⟩ :=
      pointsToBytes32_exists_pkCells pk.bytes.toList pk.bytes.2
    have hm15 : memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 =
        memRegion (sp' + 129#64) 15 := by
      have hs := (memRegion_split (sp' + 129#64) 7 8 (by decide)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; exact hs
    simp only [BitVec.add_assoc, BitVec.reduceAdd, hpk_cells (sp' + 97#64), pkCells, sepConj_assoc]
    have h15_pre :
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 ∗
          memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗ vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
          lsLogOff ∗ A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100) ⊢
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 15 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗ vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
          lsLogOff ∗ A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100) := by
      rw [← hm15]; apply entails_of_eq; sep_ac_rfl
    refine SepWPp.mono_pre h15_pre ?_; clear h15_pre
    refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (396)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (396))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have _hb8_ext : ∀ u : BitVec 8, (u.zeroExtend 32).zeroExtend 64 = u.zeroExtend 64 := by decide
    refine SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic (F := lsLogOff)
        (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
          (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
            identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
              A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt sp' (skipFieldStackX 100)))
        (post_pk_ok_396_placed_wp d (x := x) (st := st)
          (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
          hdec hpk hsk_lt
          (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          hpk_cells (by simp [*, arm64_norm]))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, by
          refine Entails.trans (sepConj_mono_left hentf) ?_
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
          apply entails_of_eq; sep_ac_rfl⟩)
    unfold pkCells; apply entails_of_eq; sep_ac_rfl
  | error e =>
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error e := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey
      simp [hdec, hpk, Bind.bind, Except.bind, Except.map]
    cases e with
    | noKeyTypeIdentifier =>
      dsimp only [pkTryFromResultAt]
      have hm31 : memRegion (sp' + 96#64 + 9#64) 31 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 30 := by
        rw [memRegion_split (sp' + 96#64 + 9#64) 1 30 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm31]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun b9 => ?_
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_
      wp_steps_sync_pool ((blkPl_84).base + bv% (760))
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      refine SepWPp.mono_pre ?_
        (sepWPp_frame_noPanic
          (F := memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff)
          (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
            (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
              (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
                A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp' (skipFieldStackX 100)))
          (err_store_760_placed_wp d (x := x) (st := st)
            (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
            (pkBs := m.publicKey) (skBs := m.privateKey)
            (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
              (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
              (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, speWord, arm64_norm]) rfl
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (ikpResult_err_spe7 A.repAlloc x.ret _ htry_err))
          fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, by
            refine Entails.trans (sepConj_mono_left hentf) ?_
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
            apply entails_of_eq; sep_ac_rfl⟩)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe7 sp' b9))))
      apply entails_of_eq; sep_ac_rfl
    | badKeyType t =>
      dsimp only [pkTryFromResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_
      wp_steps_sync_pool ((blkPl_84).base + bv% (760))
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      have _ht_mask : ∀ u : BitVec 8,
          0#64 ||| (((u.zeroExtend 32).zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      have _ht_mask2 : ∀ u : BitVec 8,
          0#64 ||| ((u.zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      refine SepWPp.mono_pre ?_
        (sepWPp_frame_noPanic
          (F := memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff)
          (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
            (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
              (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
                A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp' (skipFieldStackX 100)))
          (err_store_760_placed_wp d (x := x) (st := st)
            (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
            (pkBs := m.publicKey) (skBs := m.privateKey)
            (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
              (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
              (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, speWord, arm64_norm])
            (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (ikpResult_err_spe8 A.repAlloc x.ret t htry_err))
          fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, by
            refine Entails.trans (sepConj_mono_left hentf) ?_
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
            apply entails_of_eq; sep_ac_rfl⟩)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe8 sp' t))))
      apply entails_of_eq; sep_ac_rfl
    | badKeyLength n =>
      dsimp only [pkTryFromResultAt]
      have hm7 : memRegion (sp' + 96#64 + 9#64) 7 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 6 := by
        rw [memRegion_split (sp' + 96#64 + 9#64) 1 6 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm7]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun b9 => ?_
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_
      wp_steps_sync_pool ((blkPl_84).base + bv% (760))
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      refine SepWPp.mono_pre ?_
        (sepWPp_frame_noPanic
          (F := memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff)
          (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
            (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
              (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
                A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp' (skipFieldStackX 100)))
          (err_store_760_placed_wp d (x := x) (st := st)
            (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
            (pkBs := m.publicKey) (skBs := m.privateKey)
            (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
              (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
              (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp only [arm64_norm]; generalize BitVec.ofNat 64 n = w; bv_kernel)
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (ikpResult_err_spe9 A.repAlloc x.ret n htry_err))
          fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, by
            refine Entails.trans (sepConj_mono_left hentf) ?_
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
            apply entails_of_eq; sep_ac_rfl⟩)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe9 sp' b9 n))))
      apply entails_of_eq; sep_ac_rfl
    | _ =>
      dsimp only [pkTryFromResultAt]
      exact SepWPp.pure_pre fun h => h.elim

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPkBudget
