/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Fmt

/-!
# `core::fmt::write` Verification for `u64` and Constant Pieces

Placement-generic `SepWP` and `subroutine_ok` specifications for `core::fmt::write`
formatting `Some(v)` via `fmtValNlTemplateBytes` and `<u64 as Display>::fmt`, and along the
`Arguments::new_const` fast path.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

/-! ## `.rodata` Template and Arithmetic Helpers -/

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := h ▸ Entails.refl P

private theorem fmtValNlTemplate_split (a : BitVec 64) :
    (a ↦ᵣ fmtValNlTemplateBytes) =
      (a ↦₈ᵣ 0xc0#8) ∗ ((a + 1#64) ↦₈ᵣ 0x01#8) ∗
      ((a + 2#64) ↦ᵣ [0x0a#8]) ∗ ((a + 3#64) ↦₈ᵣ 0x00#8) := by
  have h1 := pointsToBytesRO_append a [0xc0#8] [0x01#8, 0x0a#8, 0x00#8]
  have h2 := pointsToBytesRO_append (a + 1#64) [0x01#8] [0x0a#8, 0x00#8]
  have h3 := pointsToBytesRO_append (a + 2#64) [0x0a#8] [0x00#8]
  dsimp only [fmtValNlTemplateBytes, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil] at h1 h2 h3 ⊢
  rw [h1, pointsToBytesRO_singleton a 0xc0#8, h2, pointsToBytesRO_singleton (a + 1#64) 0x01#8,
      show a + 1#64 + 1#64 = a + 2#64 by simp [bv_lin_norm],
      h3, show a + 2#64 + 1#64 = a + 3#64 by simp [bv_lin_norm],
      pointsToBytesRO_singleton (a + 3#64) 0x00#8]

private theorem template_nl_bounds {templateAddr : BitVec 64}
    (htpl_ne : templateAddr ≠ 0#64) (htpl_fit : templateAddr.toNat + 12 ≤ Arm64.USER_VA_LIMIT) :
    templateAddr + 2#64 ≠ 0#64 ∧
    (templateAddr + 2#64).toNat + ([0x0a#8] : List (BitVec 8)).length + 8 ≤ Arm64.USER_VA_LIMIT := by
  have : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
  have hpos : 0 < templateAddr.toNat :=
    Classical.byContradiction fun h =>
      htpl_ne (BitVec.eq_of_toNat_eq (by change templateAddr.toNat = 0; omega))
  have hadd : (templateAddr + 2#64).toNat = templateAddr.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun h => ?_, by simp only [List.length_singleton]; omega⟩
  have hz : (templateAddr + 2#64).toNat = 0 := by rw [h]; rfl
  omega

private theorem sp_cw_lo_of_sp_lo {sp0 : BitVec 64} (hsp_lo : 0x200 ≤ sp0.toNat) :
    0x100 ≤ (sp0 - 0x70#64).toNat := by
  have h := sp0.isLt
  rw [BitVec.toNat_sub_of_le (show (0x70#64 : BitVec 64) ≤ sp0 by
    rw [BitVec.le_def]; change 112 ≤ sp0.toNat; omega)]
  change 256 ≤ sp0.toNat - 112
  omega

private theorem getLsbD_zero_of_and_one_eq_zero {x : BitVec 64} (h : x &&& 1#64 = 0#64) :
    x.getLsbD 0 = false := by
  revert h; bv_bits

theorem emitted_append_u64Nl_eq_formatGetResult (emitted : List (BitVec 8)) (v : BitVec 64) :
    emitted ++ formatDecimalNat v.toNat ++ [0x0a#8] = emitted ++ formatGetResult (some v) := by
  simp [formatGetResult, bytesOfString, List.append_assoc]

/-! ## `core::fmt::write` Specification and Verification -/

/-- Spatial bundle of unchanged caller and `.rodata` resources for `core::fmt::write` on
    `fmtValNlTemplateBytes` and a single `u64` `Display` argument. -/
def hbCoreFmtWriteU64NlRes (C : HbCliLayout)
    (templateAddr argsPtr valPtr v : BitVec 64) : SepProp :=
  HbAdapterWriteVtableRo C ∗
  (templateAddr ↦ᵣ fmtValNlTemplateBytes) ∗
  (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
  (valPtr ↦₆₄ v) ∗
  (argsPtr ↦₆₄ valPtr) ∗
  ((argsPtr + 8#64) ↦₆₄ C.u64DisplayFmtAddr)

/-- `Spec Unit` contract for `core::fmt::write` (`C.coreFmtWriteAddr`) formatting `v : BitVec 64`
    followed by `'\n'` via `fmtValNlTemplateBytes` and `<u64 as core::fmt::Display>::fmt`. -/
def hbCoreFmtWriteU64NlSpec (C : HbCliLayout) (writerPtr : BitVec 64)
    (writeStackBytes : Nat) (W : List (BitVec 8) → State → SepProp)
    (templateAddr argsPtr valPtr v : BitVec 64) (emitted : List (BitVec 8)) : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = writerPtr ∧
     s0.readReg64 .x1 = C.adapterWriteVtableAddr ∧
     s0.readReg64 .x2 = templateAddr ∧
     s0.readReg64 .x3 = argsPtr ∧
     argsPtr &&& 1#64 = 0#64 ∧
     0x200 ≤ s0.sp.toNat⌝ ∗
    hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
    W emitted s0 ∗
    stackFrameAt s0.sp (0xf0 + max 0x30 writeStackBytes)
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
    hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
    W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) sf ∗
    stackFrameAt s0.sp (0xf0 + max 0x30 writeStackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbCoreFmtWrite_u64Nl_wp {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    {target_pc ret_pc sp0 templateAddr argsPtr valPtr v : BitVec 64}
    {emitted : List (BitVec 8)} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : HbFmtCode P C)
    (hw : HbFmtWriter P C writerPtr writeStackBytes W)
    (hext : ∀ pc, P.externAt? pc = none)
    (htpl_ne : templateAddr ≠ 0#64) (htpl_fit : templateAddr.toNat + 12 ≤ Arm64.USER_VA_LIMIT)
    (hpc : s0.pc = C.coreFmtWriteAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true) (hsp_lo : 0x200 ≤ sp0.toNat)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = writerPtr)
    (hx1 : s0.readReg64 .x1 = C.adapterWriteVtableAddr)
    (hx2 : s0.readReg64 .x2 = templateAddr)
    (hx3 : s0.readReg64 .x3 = argsPtr)
    (hx3_even : argsPtr &&& 1#64 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = 0#64 → FmtIoStatePreserved s0 sf →
      SepWP P target_pc sf
        ((hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
          W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) sf ∗
          stackFrameAt sp0 (0xf0 + max 0x30 writeStackBytes)) ∗ F)
        post oom) :
    SepWP P target_pc s0
      ((hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
        W emitted s0 ∗
        stackFrameAt sp0 (0xf0 + max 0x30 writeStackBytes)) ∗ F)
      post oom := by
  subst hsp
  let ws := max 0x30 writeStackBytes
  have hws_le : ws ≤ 2 ^ 32 := by have := hw.stack_le; omega
  let sp_cw := s0.sp - 0x70#64
  let formatterPtr := s0.sp - 104#64
  have hsp_cw_lo : 0x100 ≤ sp_cw.toNat := sp_cw_lo_of_sp_lo hsp_lo
  obtain ⟨hnl_ne, hnl_fit⟩ := template_nl_bounds htpl_ne htpl_fit
  have hx3_bit0 : argsPtr.getLsbD 0 = false := getLsbD_zero_of_and_one_eq_zero hx3_even
  have hx0' : s0.readReg64 (.gpr 0#5) = writerPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = C.adapterWriteVtableAddr := hx1
  have hx2' : s0.readReg64 (.gpr 2#5) = templateAddr := hx2
  have hx3' : s0.readReg64 (.gpr 3#5) = argsPtr := hx3
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  conv =>
    arg 4
    rw [show 0xf0 + max 0x30 writeStackBytes = 0x70 + (0x80 + ws) by dsimp only [ws]; omega,
        stackFrameAt_split s0.sp 0x70 (0x80 + ws) (by omega),
        ← stackAt_eq_stackFrameAt s0.sp 0x70, stackAt_eq_cells s0.sp 14]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  iterate 14 (apply SepWP.exists_elim; intro _)
  rename_i v_slot0 _ _ _ _ _ _ _ _ _ _ _ _ _
  let CwSavedSlots : SepProp :=
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
    ((s0.sp - 72#64) ↦₆₄ ret_pc) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))
  let TplRest : SepProp :=
    (templateAddr ↦₈ᵣ 0xc0#8) ∗
    ((templateAddr + 1#64) ↦₈ᵣ 0x01#8) ∗
    ((templateAddr + 2#64) ↦ᵣ [0x0a#8]) ∗
    ((templateAddr + 3#64) ↦₈ᵣ 0x00#8) ∗
    (argsPtr ↦₆₄ valPtr) ∗
    ((argsPtr + 8#64) ↦₆₄ C.u64DisplayFmtAddr)
  refine SepWP.seq_noSyscalls (mid_pc := C.u64DisplayFmtAddr)
    (Q := fun s1 P1 =>
      (P1 ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
        W emitted s0 ∗ stackFrameAt sp_cw (0x80 + ws)) ∗
        (TplRest ∗ ((s0.sp - 112#64) ↦₆₄ v_slot0) ∗ CwSavedSlots ∗ F)) ∧
      s1.sp = sp_cw ∧ s1.spAligned = true ∧
      s1.readReg64 Reg.lr = C.coreFmtWriteAddr + 0x60#64 ∧
      s1.readReg64 .x0 = valPtr ∧ s1.readReg64 .x1 = formatterPtr ∧
      s1.readReg64 (.gpr 20#5) = writerPtr ∧
      s1.readReg64 (.gpr 22#5) = templateAddr + 1#64 ∧
      s1.readReg64 (.gpr 24#5) = C.adapterWriteStrAddr ∧
      s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    hext ?_ ?_
  · have hc_cw : (P.withSvc noSyscalls).hasCode C.coreFmtWriteAddr coreFmtWriteWords :=
      hcode.coreWrite_words
    dsimp only [hbCoreFmtWriteU64NlRes, HbAdapterWriteVtableRo]
    rw [fmtValNlTemplate_split templateAddr]
    iterate 30 wp_step
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [u64DisplayStaticRes, HbAdapterWriteVtableRo, TplRest, CwSavedSlots,
        formatterPtr, sp_cw]
      apply entails_of_eq; simp only [bv_lin_norm]; ac_rfl
    · simp [wp_norm, arm64_norm, sp_cw]
    · unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align
    · simp [wp_norm, arm64_norm, bv_lin_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm, formatterPtr, bv_lin_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp (config := { decide := true }) [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  · intro s1 P1 hpc1 hrun1 hpure01 ⟨hent1, hsp1, hsp_align1, hlr1, hx0_1, hx1_1,
      hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hvregs1⟩
    have hent1' : P1 ⊢ (u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
        W emitted s1 ∗ stackFrameAt sp_cw (0x80 + ws)) ∗
        (TplRest ∗ ((s0.sp - 112#64) ↦₆₄ v_slot0) ∗ CwSavedSlots ∗ F) :=
      Entails.trans hent1
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (hw.pure_transport emitted hpure01))))
    refine SepWP.weaken_pre hent1' ?_
    refine u64DisplayFmt_default_wp hcode hw hext hpc1 hrun1 hsp1 hsp_align1 hsp_cw_lo
      hlr1 hx0_1 hx1_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcs12 hx0_2 hio12
    have hio02 := FmtIoStatePreserved.trans hpure01.toIo hio12
    have hsp_align2 : s2.spAligned = true := by unfold State.spAligned at *; rwa [hsp2, ← hsp1]
    have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
    have hx20_2 : s2.readReg64 (.gpr 20#5) = writerPtr := hcs12.2.1.trans hx20_1
    have hx22_2 : s2.readReg64 (.gpr 22#5) = templateAddr + 1#64 := hcs12.2.2.2.1.trans hx22_1
    have hx24_2 : s2.readReg64 (.gpr 24#5) = C.adapterWriteStrAddr := hcs12.2.2.2.2.2.1.trans hx24_1
    have hx27_2 : s2.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
      hcs12.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 : s2.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) :=
      hcs12.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 :=
      hcs12.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    let FrameNl : SepProp :=
      stackFrameAt (sp_cw - BitVec.ofNat 64 writeStackBytes) (0x80 + ws - writeStackBytes) ∗
      u64DisplayStaticRes C writerPtr valPtr formatterPtr v ∗
      (templateAddr ↦₈ᵣ 0xc0#8) ∗ ((templateAddr + 1#64) ↦₈ᵣ 0x01#8) ∗
      ((templateAddr + 3#64) ↦₈ᵣ 0x00#8) ∗
      (argsPtr ↦₆₄ valPtr) ∗ ((argsPtr + 8#64) ↦₆₄ C.u64DisplayFmtAddr) ∗
      ((s0.sp - 112#64) ↦₆₄ v_slot0) ∗ CwSavedSlots ∗ F
    refine SepWP.seq_noSyscalls (mid_pc := C.adapterWriteStrAddr)
      (Q := fun s3 P3 =>
        (P3 ⊢ (W (emitted ++ formatDecimalNat v.toNat) s2 ∗
          ((templateAddr + 2#64) ↦ᵣ [0x0a#8]) ∗ stackFrameAt sp_cw writeStackBytes) ∗ FrameNl) ∧
        s3.sp = sp_cw ∧ s3.spAligned = true ∧
        s3.readReg64 Reg.lr = C.coreFmtWriteAddr + 0x90#64 ∧
        s3.readReg64 .x0 = writerPtr ∧
        s3.readReg64 .x1 = templateAddr + 2#64 ∧
        s3.readReg64 .x2 = 1#64 ∧
        s3.readReg64 (.gpr 22#5) = templateAddr + 2#64 ∧
        s3.readReg64 (.gpr 23#5) = 1#64 ∧
        s3.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
        s3.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0)
      hext ?_ ?_
    · have hc_cw : (P.withSvc noSyscalls).hasCode C.coreFmtWriteAddr coreFmtWriteWords :=
        hcode.coreWrite_words
      dsimp only [TplRest]
      iterate 12 wp_step
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2]) ?_
      refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hws_split : stackFrameAt sp_cw (0x80 + ws) =
            stackFrameAt sp_cw writeStackBytes ∗
              stackFrameAt (sp_cw - BitVec.ofNat 64 writeStackBytes) (0x80 + ws - writeStackBytes) := by
          conv => lhs; rw [show 0x80 + ws = writeStackBytes + (0x80 + ws - writeStackBytes) by omega]
          exact stackFrameAt_split sp_cw writeStackBytes (0x80 + ws - writeStackBytes) (by omega)
        dsimp only [FrameNl]
        rw [hws_split]; apply entails_of_eq; ac_rfl
      · simp [wp_norm, arm64_norm, hsp2]
      · unfold State.spAligned at *; simpa [wp_norm, arm64_norm] using hsp_align2
      · simp [wp_norm, arm64_norm, bv_lin_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm, bv_lin_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm]
      · simp (config := { decide := true }) [wp_norm, arm64_norm, hx27_2]
      · simp (config := { decide := true }) [wp_norm, arm64_norm, hx28_2]
      · simpa [wp_norm, arm64_norm] using hvregs2
    · intro s3 P3 hpc3 hrun3 hpure23 ⟨hent3, hsp3, hsp_align3, hlr3, hx0_3, hx1_3, hx2_3,
        hx22_3, hx23_3, hx27_3, hx28_3, hvregs3⟩
      have hio03 := FmtIoStatePreserved.trans hio02 hpure23.toIo
      have hent3' : P3 ⊢ (W (emitted ++ formatDecimalNat v.toNat) s3 ∗
          ((templateAddr + 2#64) ↦ᵣ [0x0a#8]) ∗ stackFrameAt sp_cw writeStackBytes) ∗ FrameNl :=
        Entails.trans hent3
          (sepConj_mono_left (sepConj_mono_left
            (hw.pure_transport (emitted ++ formatDecimalNat v.toNat) hpure23)))
      refine SepWP.weaken_pre hent3' ?_
      refine SepWP.call_subroutine_frame
        (hw.write_str_ro (emitted ++ formatDecimalNat v.toNat) [0x0a#8] (templateAddr + 2#64)
          rfl hnl_ne hnl_fit)
        (x := ()) (F := FrameNl) hpc3 hrun3 hsp_align3 hlr3 ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
      · intro R hm
        dsimp only; simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0_3, hx1_3, hx2_3⟩, by simpa [hsp3, sepConj_assoc] using hm⟩
      · intro s4 hpc4 hrun4 hsp4 hcs34
        apply SepWP.of_reaches_pc; intro R hm
        dsimp only at hm; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        obtain ⟨⟨hx0_4, hio34⟩, hm⟩ := hm
        have hio04 := FmtIoStatePreserved.trans hio03 hio34
        have hsp4' : s4.sp = sp_cw := hsp4.trans hsp3
        have hsp_align4 : s4.spAligned = true := by
          unfold State.spAligned at *; rwa [hsp4', ← hsp3]
        have hx0_4' : s4.readReg64 (.gpr 0#5) = 0#64 := hx0_4
        have hx22_4 : s4.readReg64 (.gpr 22#5) = templateAddr + 2#64 :=
          hcs34.2.2.2.1.trans hx22_3
        have hx23_4 : s4.readReg64 (.gpr 23#5) = 1#64 := hcs34.2.2.2.2.1.trans hx23_3
        have hx27_4 : s4.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
          hcs34.2.2.2.2.2.2.2.2.1.trans hx27_3
        have hx28_4 : s4.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) :=
          hcs34.2.2.2.2.2.2.2.2.2.1.trans hx28_3
        have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
          hcs34.2.2.2.2.2.2.2.2.2.2.2.trans hvregs3
        apply SepWP.to_reaches_pc ?_
          (P := (W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) s4 ∗
            ((templateAddr + 2#64) ↦ᵣ [0x0a#8]) ∗ stackFrameAt sp_cw writeStackBytes) ∗ FrameNl)
          (by simpa [hsp3, sepConj_assoc] using hm)
        refine SepWP.seq_noSyscalls (mid_pc := ret_pc)
          (Q := fun sf Pf =>
            (Pf ⊢ (hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
              W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) s4 ∗
              stackFrameAt s0.sp (0xf0 + ws)) ∗ F) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = 0#64)
          hext ?_ ?_
        · have hc_cw : (P.withSvc noSyscalls).hasCode C.coreFmtWriteAddr coreFmtWriteWords :=
            hcode.coreWrite_words
          dsimp only [FrameNl, CwSavedSlots, u64DisplayStaticRes, formatterPtr, sp_cw] at hsp3 hsp4' ⊢
          iterate 15 wp_step
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4]) ?_
          refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_⟩
          · let Frame14 : SepProp :=
              ((s0.sp - 112#64) ↦₆₄ v_slot0) ∗
              ((s0.sp - 104#64) ↦₆₄ writerPtr) ∗
              ((s0.sp - 96#64) ↦₆₄ C.adapterWriteVtableAddr) ∗
              ((s0.sp - 88#64) ↦₆₄ 0x60000020#64) ∗
              CwSavedSlots
            have h14_ent : Frame14 ⊢ stackFrameAt s0.sp 0x70 := by
              dsimp only [Frame14, CwSavedSlots]
              rw [← stackAt_eq_stackFrameAt s0.sp 0x70, stackAt_eq_cells s0.sp 14]
              simp only [Nat.reduceMul]
              iterate 13 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
              exact cells_sub_one_entails 8
            have hws_mrg : stackFrameAt (s0.sp - 0x70#64) writeStackBytes ∗
                stackFrameAt (s0.sp - 0x70#64 - BitVec.ofNat 64 writeStackBytes)
                  (0x80 + ws - writeStackBytes) =
                stackFrameAt (s0.sp - 0x70#64) (0x80 + ws) := by
              symm; conv => lhs; rw [show 0x80 + ws = writeStackBytes + (0x80 + ws - writeStackBytes) by omega]
              exact stackFrameAt_split (s0.sp - 0x70#64) writeStackBytes
                (0x80 + ws - writeStackBytes) (by omega)
            dsimp only [hbCoreFmtWriteU64NlRes]
            rw [fmtValNlTemplate_split templateAddr]
            refine Entails.trans (Q :=
              ((HbAdapterWriteVtableRo C ∗
                ((templateAddr ↦₈ᵣ 0xc0#8) ∗ ((templateAddr + 1#64) ↦₈ᵣ 0x01#8) ∗
                 ((templateAddr + 2#64) ↦ᵣ [0x0a#8]) ∗ ((templateAddr + 3#64) ↦₈ᵣ 0x00#8)) ∗
                (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
                (valPtr ↦₆₄ v) ∗ (argsPtr ↦₆₄ valPtr) ∗
                ((argsPtr + 8#64) ↦₆₄ C.u64DisplayFmtAddr)) ∗
               W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) s4 ∗
               (Frame14 ∗ (stackFrameAt (s0.sp - 0x70#64) writeStackBytes ∗
                stackFrameAt (s0.sp - 0x70#64 - BitVec.ofNat 64 writeStackBytes)
                  (0x80 + ws - writeStackBytes)))) ∗ F)
              (by apply entails_of_eq; dsimp only [Frame14, CwSavedSlots]; simp only [bv_lin_norm]; ac_rfl) ?_
            apply sepConj_mono_left
            refine sepConj_mono_right (sepConj_mono_right ?_)
            rw [hws_mrg]
            refine Entails.trans (sepConj_mono_left h14_ent) ?_
            rw [← stackFrameAt_split s0.sp 0x70 (0x80 + ws) (by omega),
                show 0x70 + (0x80 + ws) = 0xf0 + ws by omega]
            exact Entails.refl _
          · simp [wp_norm, arm64_norm, bv_lin_norm]
          · simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, hx27_4, hx28_4, hvregs4]
          · simp (config := { decide := true }) [wp_norm, arm64_norm]
        · intro sf Pf hpcf hrunf hpure4f ⟨hentf, hspf, hcs0f, hx0f⟩
          have hio0f := FmtIoStatePreserved.trans hio04 hpure4f.toIo
          have hentf' : Pf ⊢ (hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
              W (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) sf ∗
              stackFrameAt s0.sp (0xf0 + max 0x30 writeStackBytes)) ∗ F :=
            Entails.trans hentf
              (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
                (hw.pure_transport (emitted ++ formatDecimalNat v.toNat ++ [0x0a#8]) hpure4f))))
          exact SepWP.weaken_pre hentf' (hnext sf hpcf hrunf hspf hcs0f hx0f hio0f)

theorem hbCoreFmtWrite_u64Nl_ok {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    (hcode : HbFmtCode P C)
    (hw : HbFmtWriter P C writerPtr writeStackBytes W)
    (hext : ∀ pc, P.externAt? pc = none)
    (templateAddr argsPtr valPtr v : BitVec 64) (emitted : List (BitVec 8))
    (htpl_ne : templateAddr ≠ 0#64) (htpl_fit : templateAddr.toNat + 12 ≤ Arm64.USER_VA_LIMIT) :
    subroutine_ok P C.coreFmtWriteAddr
      (hbCoreFmtWriteU64NlSpec C writerPtr writeStackBytes W
        templateAddr argsPtr valPtr v emitted) := by
  refine subroutine_ok_of_sepWP_init fun _ R s0 hpc hrun hpre hsp => ?_
  dsimp only [hbCoreFmtWriteU64NlSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx3_even, hsp_lo⟩, hmem⟩ := hpre
  refine ⟨(hbCoreFmtWriteU64NlRes C templateAddr argsPtr valPtr v ∗
      W emitted s0 ∗ stackFrameAt s0.sp (0xf0 + max 0x30 writeStackBytes)) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbCoreFmtWrite_u64Nl_wp hcode hw hext htpl_ne htpl_fit hpc hrun rfl hsp hsp_lo rfl
    hx0 hx1 hx2 hx3 hx3_even fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hio_f => ?_
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_emp] at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hio_f⟩, by simpa [sepConj_assoc] using hm⟩

/-! ## `core::fmt::write` on `Arguments::new_const` -/

private theorem getLsbD_zero_of_and_one_eq_one {x : BitVec 64} (h : x &&& 1#64 = 1#64) :
    x.getLsbD 0 = true ∧ (BitVec.zeroExtend 64 (BitVec.truncate 32 x)).getLsbD 0 = true := by
  refine ⟨?_, ?_⟩ <;> { revert h; bv_bits }

theorem hbCoreFmtWrite_const_to_write_str_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 writerPtr piecesPtr fmtArg3 : BitVec 64}
    {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords C.coreFmtWriteAddr coreFmtWriteWords)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.coreFmtWriteAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = writerPtr)
    (hx1 : s0.readReg64 .x1 = C.adapterWriteVtableAddr)
    (hx2 : s0.readReg64 .x2 = piecesPtr)
    (hx3 : s0.readReg64 .x3 = fmtArg3)
    (hx3_odd : fmtArg3 &&& 1#64 = 1#64)
    (hnext : ∀ s1 : State, s1.pc = C.adapterWriteStrAddr → s1.status = .Running →
      s1.sp = sp0 → s1.spAligned = true →
      s1.readReg64 Reg.lr = ret_pc →
      CalleeSavedPreserved s0 s1 → FmtPureStatePreserved s0 s1 →
      s1.readReg64 .x0 = writerPtr →
      s1.readReg64 .x1 = piecesPtr →
      s1.readReg64 .x2 = fmtArg3 >>> 1 →
      SepWP P target_pc s1
        ((HbAdapterWriteVtableRo C ∗ stackFrameAt sp0 0x70) ∗ F)
        post oom) :
    SepWP P target_pc s0
      ((HbAdapterWriteVtableRo C ∗ stackFrameAt sp0 0x70) ∗ F)
      post oom := by
  subst hsp
  obtain ⟨hx3_bit0_64, hx3_bit0_32⟩ := getLsbD_zero_of_and_one_eq_one hx3_odd
  have hx0' : s0.readReg64 (.gpr 0#5) = writerPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = C.adapterWriteVtableAddr := hx1
  have hx2' : s0.readReg64 (.gpr 2#5) = piecesPtr := hx2
  have hx3' : s0.readReg64 (.gpr 3#5) = fmtArg3 := hx3
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  refine SepWP.seq_noSyscalls (mid_pc := C.adapterWriteStrAddr)
    (Q := fun s1 P1 =>
      (P1 ⊢ (HbAdapterWriteVtableRo C ∗ stackFrameAt s0.sp 0x70) ∗ F) ∧
      s1.sp = s0.sp ∧ s1.spAligned = true ∧
      s1.readReg64 Reg.lr = ret_pc ∧
      CalleeSavedPreserved s0 s1 ∧
      s1.readReg64 .x0 = writerPtr ∧
      s1.readReg64 .x1 = piecesPtr ∧
      s1.readReg64 .x2 = fmtArg3 >>> 1)
    hext ?_ (fun s1 P1 hpc1 hrun1 hpure ⟨hent, hsp1, hsp_al1, hlr1, hcs1, hx0_1, hx1_1, hx2_1⟩ =>
      SepWP.weaken_pre hent (hnext s1 hpc1 hrun1 hsp1 hsp_al1 hlr1 hcs1 hpure hx0_1 hx1_1 hx2_1))
  have hc_cw : (P.withSvc noSyscalls).hasCode C.coreFmtWriteAddr coreFmtWriteWords := hc
  dsimp only [HbAdapterWriteVtableRo]
  conv =>
    arg 4
    rw [← stackAt_eq_stackFrameAt s0.sp 0x70, stackAt_eq_cells s0.sp 14]
    simp (disch := decide) only [Nat.reduceMul, ProofLib.cells_sub_succ, Nat.reduceSub,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]
  iterate 14 (apply SepWP.exists_elim; intro _)
  iterate 23 wp_step
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp [CpuAuxPreserved.refl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sepConj_mono_left
    refine sepConj_mono_right ?_
    rw [← stackAt_eq_stackFrameAt s0.sp 0x70, stackAt_eq_cells s0.sp 14]
    simp only [Nat.reduceMul]
    iterate 13 (refine cells_sub_succ_entails _ _ ?_; simp only [Nat.reduceSub])
    exact cells_sub_one_entails 8
  · simp [wp_norm, arm64_norm, bv_lin_norm]
  · unfold State.spAligned at *; simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_align
  · simp [wp_norm, arm64_norm]
  · simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, *]
  · simp (config := { decide := true }) [wp_norm, arm64_norm]
  · simp (config := { decide := true }) [wp_norm, arm64_norm]
  · simp (config := { decide := true }) [wp_norm, arm64_norm]

/-- `Spec Unit` contract for `core::fmt::write` (`C.coreFmtWriteAddr`) on `Arguments::new_const`
    (`fmtArg3 &&& 1#64 = 1#64`, `fmtArg3 >>> 1 = BitVec.ofNat 64 bs.length`). -/
def hbCoreFmtWriteConstSpec (C : HbCliLayout) (writerPtr : BitVec 64)
    (writeStackBytes : Nat) (W : List (BitVec 8) → State → SepProp)
    (piecesPtr fmtArg3 : BitVec 64) (bs emitted : List (BitVec 8)) : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = writerPtr ∧
     s0.readReg64 .x1 = C.adapterWriteVtableAddr ∧
     s0.readReg64 .x2 = piecesPtr ∧
     s0.readReg64 .x3 = fmtArg3 ∧
     fmtArg3 &&& 1#64 = 1#64 ∧
     fmtArg3 >>> 1 = BitVec.ofNat 64 bs.length⌝ ∗
    HbAdapterWriteVtableRo C ∗
    (piecesPtr ↦ᵣ bs) ∗
    W emitted s0 ∗
    stackFrameAt s0.sp (max 0x70 writeStackBytes)
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
    HbAdapterWriteVtableRo C ∗
    (piecesPtr ↦ᵣ bs) ∗
    W (emitted ++ bs) sf ∗
    stackFrameAt s0.sp (max 0x70 writeStackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbCoreFmtWrite_const_wp {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    {target_pc ret_pc sp0 piecesPtr fmtArg3 : BitVec 64}
    {bs emitted : List (BitVec 8)} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasWords C.coreFmtWriteAddr coreFmtWriteWords)
    (hws_le : writeStackBytes ≤ 2 ^ 32)
    (hpure_W : ∀ {s1 s2 : State}, FmtPureStatePreserved s1 s2 → W emitted s1 ⊢ W emitted s2)
    (hwrite : subroutine_ok P C.adapterWriteStrAddr
      ({ pre := fun (_ : Unit) s =>
           ⌜s.readReg64 .x0 = writerPtr ∧
             s.readReg64 .x1 = piecesPtr ∧
             s.readReg64 .x2 = BitVec.ofNat 64 bs.length⌝ ∗
           W emitted s ∗
           (piecesPtr ↦ᵣ bs) ∗
           stackFrameAt s.sp writeStackBytes
         post := fun _ s sf =>
           ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s sf⌝ ∗
           W (emitted ++ bs) sf ∗
           (piecesPtr ↦ᵣ bs) ∗
           stackFrameAt s.sp writeStackBytes } : Spec Unit))
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.coreFmtWriteAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : s0.spAligned = true)
    (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = writerPtr)
    (hx1 : s0.readReg64 .x1 = C.adapterWriteVtableAddr)
    (hx2 : s0.readReg64 .x2 = piecesPtr)
    (hx3 : s0.readReg64 .x3 = fmtArg3)
    (hx3_odd : fmtArg3 &&& 1#64 = 1#64)
    (hx3_len : fmtArg3 >>> 1 = BitVec.ofNat 64 bs.length)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = 0#64 → FmtIoStatePreserved s0 sf →
      SepWP P target_pc sf
        ((HbAdapterWriteVtableRo C ∗ (piecesPtr ↦ᵣ bs) ∗
          W (emitted ++ bs) sf ∗
          stackFrameAt sp0 (max 0x70 writeStackBytes)) ∗ F)
        post oom) :
    SepWP P target_pc s0
      ((HbAdapterWriteVtableRo C ∗ (piecesPtr ↦ᵣ bs) ∗
        W emitted s0 ∗
        stackFrameAt sp0 (max 0x70 writeStackBytes)) ∗ F)
      post oom := by
  let ws := max 0x70 writeStackBytes
  have hsplit70 : stackFrameAt sp0 ws =
      stackFrameAt sp0 0x70 ∗ stackFrameAt (sp0 - 0x70#64) (ws - 0x70) := by
    conv => lhs; rw [show ws = 0x70 + (ws - 0x70) by omega]
    exact stackFrameAt_split sp0 0x70 (ws - 0x70) (by omega)
  have hsplit_ws : stackFrameAt sp0 ws =
      stackFrameAt sp0 writeStackBytes ∗
        stackFrameAt (sp0 - BitVec.ofNat 64 writeStackBytes) (ws - writeStackBytes) := by
    conv => lhs; rw [show ws = writeStackBytes + (ws - writeStackBytes) by omega]
    exact stackFrameAt_split sp0 writeStackBytes (ws - writeStackBytes) (by omega)
  refine SepWP.weaken_pre
    (P' := (HbAdapterWriteVtableRo C ∗ stackFrameAt sp0 0x70) ∗
      (stackFrameAt (sp0 - 0x70#64) (ws - 0x70) ∗ (piecesPtr ↦ᵣ bs) ∗ W emitted s0 ∗ F))
    (by change _ ⊢ _; rw [hsplit70]; apply entails_of_eq; ac_rfl) ?_
  refine hbCoreFmtWrite_const_to_write_str_wp hc hext hpc hrun hsp hsp_align hlr
    hx0 hx1 hx2 hx3 hx3_odd fun s1 hpc1 hrun1 hsp1 hsp_al1 hlr1 hcs01 hpure01 hx0_1 hx1_1 hx2_1 => ?_
  let FrameTail : SepProp :=
    stackFrameAt (sp0 - BitVec.ofNat 64 writeStackBytes) (ws - writeStackBytes) ∗
    HbAdapterWriteVtableRo C ∗ F
  have hent1 : (HbAdapterWriteVtableRo C ∗ stackFrameAt sp0 0x70) ∗
      (stackFrameAt (sp0 - 0x70#64) (ws - 0x70) ∗ (piecesPtr ↦ᵣ bs) ∗ W emitted s0 ∗ F) ⊢
      (W emitted s1 ∗ (piecesPtr ↦ᵣ bs) ∗ stackFrameAt sp0 writeStackBytes) ∗ FrameTail := by
    refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left (hpure_W hpure01)))
    apply entails_of_eq
    dsimp only [FrameTail]
    rw [show (HbAdapterWriteVtableRo C ∗ stackFrameAt sp0 0x70) ∗
        (stackFrameAt (sp0 - 0x70#64) (ws - 0x70) ∗ (piecesPtr ↦ᵣ bs) ∗ W emitted s0 ∗ F) =
        (stackFrameAt sp0 0x70 ∗ stackFrameAt (sp0 - 0x70#64) (ws - 0x70)) ∗
        (HbAdapterWriteVtableRo C ∗ (piecesPtr ↦ᵣ bs) ∗ W emitted s0 ∗ F) by ac_rfl,
        ← hsplit70, hsplit_ws]
    ac_rfl
  refine SepWP.weaken_pre hent1 ?_
  refine SepWP.call_subroutine_frame hwrite
    (x := ()) (F := FrameTail) hpc1 hrun1 hsp_al1 hlr1 ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R hm
    dsimp only; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1.trans hx3_len⟩, by simpa [hsp1, sepConj_assoc] using hm⟩
  · intro sf hpcf hrunf hspf hcs1f
    apply SepWP.of_reaches_pc; intro R hm
    dsimp only at hm; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨⟨hx0_f, hio1f⟩, hm⟩ := hm
    have hio0f := FmtIoStatePreserved.trans hpure01.toIo hio1f
    have hspf' : sf.sp = sp0 := hspf.trans hsp1
    have hcs0f := CalleeSavedPreserved.trans hcs01 hcs1f
    apply SepWP.to_reaches_pc ?_
      (P := ((HbAdapterWriteVtableRo C ∗ (piecesPtr ↦ᵣ bs) ∗
        W (emitted ++ bs) sf ∗ stackFrameAt sp0 ws) ∗ F))
    · refine Satisfies.mono (sepConj_mono_left ?_)
        (show sf.mem ⊨ ((W (emitted ++ bs) sf ∗ (piecesPtr ↦ᵣ bs) ∗
          stackFrameAt sp0 writeStackBytes) ∗ FrameTail) ∗ R from
          by simpa [hsp1, sepConj_assoc] using hm)
      dsimp only [FrameTail]
      rw [hsplit_ws]; apply entails_of_eq; ac_rfl
    · exact hnext sf hpcf hrunf hspf' hcs0f hx0_f hio0f

theorem hbCoreFmtWrite_const_ok {P : Program} {C : HbCliLayout}
    {writerPtr : BitVec 64} {writeStackBytes : Nat} {W : List (BitVec 8) → State → SepProp}
    (hc : P.hasWords C.coreFmtWriteAddr coreFmtWriteWords)
    (hws_le : writeStackBytes ≤ 2 ^ 32)
    (hpure_W : ∀ (emitted : List (BitVec 8)) {s1 s2 : State},
      FmtPureStatePreserved s1 s2 → W emitted s1 ⊢ W emitted s2)
    (piecesPtr fmtArg3 : BitVec 64) (bs emitted : List (BitVec 8))
    (hwrite : subroutine_ok P C.adapterWriteStrAddr
      ({ pre := fun (_ : Unit) s =>
           ⌜s.readReg64 .x0 = writerPtr ∧
             s.readReg64 .x1 = piecesPtr ∧
             s.readReg64 .x2 = BitVec.ofNat 64 bs.length⌝ ∗
           W emitted s ∗
           (piecesPtr ↦ᵣ bs) ∗
           stackFrameAt s.sp writeStackBytes
         post := fun _ s sf =>
           ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s sf⌝ ∗
           W (emitted ++ bs) sf ∗
           (piecesPtr ↦ᵣ bs) ∗
           stackFrameAt s.sp writeStackBytes } : Spec Unit))
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P C.coreFmtWriteAddr
      (hbCoreFmtWriteConstSpec C writerPtr writeStackBytes W piecesPtr fmtArg3 bs emitted) := by
  refine subroutine_ok_of_sepWP_init fun _ R s0 hpc hrun hpre hsp => ?_
  dsimp only [hbCoreFmtWriteConstSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx3_odd, hx3_len⟩, hmem⟩ := hpre
  refine ⟨(HbAdapterWriteVtableRo C ∗ (piecesPtr ↦ᵣ bs) ∗
      W emitted s0 ∗ stackFrameAt s0.sp (max 0x70 writeStackBytes)) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbCoreFmtWrite_const_wp hc hws_le (hpure_W emitted) hwrite hext
    hpc hrun rfl hsp rfl hx0 hx1 hx2 hx3 hx3_odd hx3_len
    fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hio_f => ?_
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_emp] at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hio_f⟩, by simpa [sepConj_assoc] using hm⟩

end CaseStudies.Hashbrown.Proofs.StdCli
