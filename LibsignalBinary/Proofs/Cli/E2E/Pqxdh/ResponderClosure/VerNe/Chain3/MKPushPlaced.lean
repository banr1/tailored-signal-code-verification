/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKPush
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.CodePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.EntryPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Placed `message::merge<Chain> [local#4]`: MessageKeys Push (`Chain3MkPushPlacedStmt`)

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.MKPush`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Call framing helper for `withLsCl` -/

private theorem call_frame_lscl_keys [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_lscl_c3 (F := F) x hcall hpc hrun hsp hcl hlr ?_ ?_ ?_ ?_ hoom
  · intro R' hm
    refine intro_withLsCl_c3 hcl ?_
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf code R' hex hm
    dsimp only [withLsCl] at hm
    exact hexit sf code R' hex hm
  · intro sf hpan
    dsimp only [withLsCl]
    exact hpanic sf hpan
  · intro sm hpcm hrunm hspm hclm hcsm
    dsimp only [withLsCl]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact hnext sm hpcm hrunm hspm hcsm hclm

/-! ## 2. Step 4d (`+0x244 → +0x178`): inner exit and `grow_one` check -/

set_option maxHeartbeats 400000 in
theorem step_c3mk_push4d_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (hC : Chain3CalleesPlacedW ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = lsmpl.base 516 + 0x178#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.spAligned = true →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      Chain3MkRegs s sm →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 keys.length →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
  have hG' := hC.grow
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false := bne_self_eq_false _
  change s.pc = (blkPl_516).base + 0x244#64 at hpc
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  apply SepWPp.fold (vecOf_keys_open a keys) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    rw [memRegion_spare_eq_emp_of_full cap ptr keys.length hfull, stackAt_c3Sub_to_growOne (sp0 - 0xf0#64)]
    simp only [emp_sepConj]
    apply SepWPp.fold (arrayAt_prostMsgKeyAt_move_bytes A0 keys ptr) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 43) hcl ?_
    unfold Prost.sliceCursorAt; iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine call_frame_lscl_keys (x := (a + 0x30#64, cap, ptr, bs))
      (ret_pc := lsmpl.base 516 + 0x178#64) hcl1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm]; rfl)
      (growOne_placed_pre_eq_extW_keys a cap ptr (sp0 - 0xf0#64) bs _ (by simp only [hsp, arm64_norm]) hbs_cap)
      ⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩ (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hclm
    have hregs_m : Chain3MkRegs s sm :=
      Chain3MkRegs.trans
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩
        (Chain3MkRegs.of_calleeSaved hcsm)
    have h20_m : sm.readReg64 .x20 = a := hregs_m.2.1.trans hx20
    have h24_m : sm.readReg64 .x24 = 104#64 := hregs_m.2.2.2.2.2.1.trans hx24
    have h25_m : sm.readReg64 .x25 = BitVec.ofNat 64 keys.length := by
      have h25_cs := hcsm.2.2.2.2.2.2.1
      simp only [arm64_norm] at h25_cs
      change sm.readReg64 (Reg.gpr 25#5) = _
      rw [h25_cs, hfull, BitVec.ofNat_toNat]; rfl
    have hspm' : sm.sp = sp0 - 0xf0#64 := by simpa only [hsp, arm64_norm] using hspm
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm'.trans hsp.symm) hsp_align
    refine SepWPp.fold (growOne_placed_post_elim_sp_extW_keys a cap ptr (sp0 - 0xf0#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    simp only [sepConj_assoc]; apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [htr, arm64_norm] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_c3Sub_to_growOne (sp0 - 0xf0#64)).symm) (by sep_frame)
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm cap' ptr' hcap'_le hcap'_lt hptr'
      hpcm hrunm hspm' hsp_align_m hclm htr_m' hregs_m h20_m h24_m h25_m)
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    have hbne_cap : (BitVec.ofNat 64 keys.length != cap) = true := by
      rw [bne_iff_ne, ne_eq, ← beq_iff_eq, hbeq_cap]; decide
    rw [memRegion_spare_split_of_lt cap ptr keys.length hcap_le' hcap_lt]
    refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x178#64) hcl ?_
    unfold Prost.sliceCursorAt; iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hcl1 (by simp only [htr, arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm]⟩
      (by simp only [h20, arm64_norm])
      (by simp only [h24, arm64_norm])
      (by simp only [arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

/-! ## 3. Step 4e (`+0x178 → +0x0a8`): 104-byte copy and length increment -/

set_option maxHeartbeats 400000 in
theorem step_c3mk_push4e_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x178#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 keys.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0xa8#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A0 mk (sp0 - 0xe8#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length; have hadd1 := ofNat_add_one_eq keys.length
  change s.pc = (blkPl_516).base + 0x178#64 at hpc
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 keys.length := hx25
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0xa8#64) hcl ?_
  apply SepWP.fold (prostMsgKeyAt_move_chunks104 A0 (sp0 - 0xe8#64) mk) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0; apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2; apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4; apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro H
  apply SepWP.pure_elim; intro hmov
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)))) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) d0 d1 d2 d3 d4 d5 dw6]
  iterate 21 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6]
  apply SepWP.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_frame)
  apply SepWP.fold (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 0xe8#64) q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  apply SepWP.fold (vecOf_keys_push_fold a cap' ptr' keys mk hcap_le hcap_lt hptr) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm]) ?_; intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]; rfl) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hcl1 (by simp only [htr, arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 4. Main theorem: `chain3MkPush_placed_ok` -/

set_option maxHeartbeats 400000 in
theorem chain3MkPush_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3MkPushPlacedStmt ext := by
  intro hC a bufRef slot ptr_rest sp0 keys mk rest x R s0 s F ret Q
    hbound hpc hrun hsp halign hcl htr hx19 hx20 hx24 hx25 hnext
  have hsp_align : s.spAligned = true := c3mk_push_spAligned hsp halign
  refine SepWPp.focus_pre
    (step_c3mk_push4d_placed hC a bufRef slot ptr_rest sp0 keys rest hbound
      hpc hrun hsp hsp_align hcl htr hx19 hx20 hx24 hx25 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hregs4 hx20_4 hx24_4 hx25_4
  refine SepWPp.focus_pre
    (step_c3mk_push4e_placed a cap' ptr' sp0 keys mk hcap'_le hcap'_lt hptr'
      hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hx20_4 hx24_4 hx25_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hcl5 htr5 hregs5
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5))
  exact sep_ac_seedChain (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
