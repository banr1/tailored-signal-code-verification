/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
public import VerifiedLibraries.RustStd.Proofs.Wave2.AllocRawVecGrow
public meta import ProofLib.ProgramReflection

/-!
# Crate-Local `<alloc::raw_vec::RawVecInner>::finish_grow`

Proves `cliIoFinishGrow_ok` and `cliIoFinishGrow_ok_withCodeLoaded` against
`VerifiedLibraries.RustStd.allocFinishGrowSpec A` for `signalSessionIoMultiLib` block `4`
(`168` B, `0x20`-byte stack frame, specialized to `elem_size = 1, elem_align = 1`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  SameCpuState
  RustStdAlloc RustLayoutOk NullAllowed
  PoolPreserved AllocCallPreserved IoFrame StdErrnoCell
  vecHeader ioVecBuf
  rustStdAllocSpec rustStdReallocSpec
  allocAllocShimSpec allocFinishGrowSpec
  allocVecGrowLb allocVecGrowLk
  allocSatisfies_ioVecBuf_bounds
)
open VerifiedLibraries.RustStd.Io (
  allocCallPreserved_of_seg allocCallPreserved_trans
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoWithCodeLoaded subroutine_ok_of_cliIoWithCodeLoaded
  cliIoResolve_eq_base sepWP_seg_cliIo_block_pure
  cliIoBlocks_len cliIoFinishGrowSym cliIoFinishGrow_lookup
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustNoAllocShimSym
  cliIoLib04 cliIoPl04 cliIoPC04 cliIoBlockNoSvc0_04
)

section
arm64_proof_prelude

private abbrev cliIoFinishGrowSavedSlots (s0 : State) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem cliIoFinishGrow_stack_split (sp : BitVec 64) :
    stackAt sp (32 + Rust.hookStack) =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3,
        Rust.hookFrame (sp - 32#64) ∗
        (((sp - 32#64) ↦₆₄ st0) ∗ ((sp - 24#64) ↦₆₄ st1) ∗
          ((sp - 16#64) ↦₆₄ st2) ∗ ((sp - 8#64) ↦₆₄ st3)) := by
  rw [show 32 + Rust.hookStack = Rust.hookStack + 8 * 4 by decide,
    stackAt_split_cells sp Rust.hookStack 4 (by decide)]
  simp only [Nat.reduceMul, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, ProofLib.stackAt, Rust.hookFrame]
  simp only [bv_lin_norm]

private theorem cliIoFinishGrow_stack_refold (sp : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) :
    Rust.hookFrame (sp - 32#64) ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      stackAt sp (32 + Rust.hookStack) := by
  rw [cliIoFinishGrow_stack_split sp]
  exact Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <| Entails.refl _

/-- Callee-saved GPRs `x21..x28` untouched by `finish_grow`. -/
private def GrowHighGprs (s0 s1 : State) : Prop :=
  s1.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s1.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)

private theorem GrowHighGprs.trans {s0 s1 s2 : State}
    (h01 : GrowHighGprs s0 s1) (h12 : GrowHighGprs s1 s2) :
    GrowHighGprs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem GrowHighGprs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    GrowHighGprs s0 s1 :=
  ⟨h.readReg64_x21, h.readReg64_x22, h.readReg64_x23, h.readReg64_x24,
   h.readReg64_x25, h.readReg64_x26, h.readReg64_x27, h.readReg64_x28⟩

private theorem cliIo4_lt : 4 < signalSessionIoMultiLib.blocks.length := by
  rw [cliIoBlocks_len]; decide

private theorem cliIoFinishGrow_realloc_pc [CliIoPlacement] :
    cliIoPl04.base + 40#64 + (cliIoPl04.ρ cliIoRustReallocSym - cliIoPl04.base - 40#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym := by
  change cliIoPl04.base + 40#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym - cliIoPl04.base - 40#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym
  bv_lin

private theorem cliIoFinishGrow_shim_pc [CliIoPlacement] :
    cliIoPl04.base + 84#64 + (cliIoPl04.ρ cliIoRustNoAllocShimSym - cliIoPl04.base - 84#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym := by
  change cliIoPl04.base + 84#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym - cliIoPl04.base - 84#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym
  bv_lin

private theorem cliIoFinishGrow_alloc_pc [CliIoPlacement] :
    cliIoPl04.base + 96#64 + (cliIoPl04.ρ cliIoRustAllocSym - cliIoPl04.base - 96#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym := by
  change cliIoPl04.base + 96#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym - cliIoPl04.base - 96#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym
  bv_lin

private theorem rustLayoutOk_one {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega, by decide⟩

private theorem bit63_eq_zero_of_lt {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem bit63_eq_one_of_ge {n : Nat} (hge : 2 ^ 63 ≤ n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).getLsbD 63 = true := by
  have hd : n / 2 ^ 63 = 1 := by omega
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

/-- Shared null-return error epilogue of `finish_grow` at `cliIoPl04.base + 104#64` (`+0x68 .. +0x84`). -/
private theorem cliIoFinishGrow_epilogue_err [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 104#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnull : NullAllowed newCap 1)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithCodeLoaded cliIoMpl (allocFinishGrowSpec A)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (Rust.hookFrame (s0.sp - 32#64) ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗ ioVecBuf A oldCap oldPtr bs ∗
        A.pool lb lk se ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hpool_ef⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef : A.pool lb lk se = A.pool lb lk sf :=
    (A.pool_transport lb lk se sf hpool_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithCodeLoaded, allocFinishGrowSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right true <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 1#64 <|
      Entails.sepExists_right (BitVec.ofNat 64 newCap) <| Entails.refl _)
  simp only [↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  rw [pure_sepConj_of_true hnull]
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

/-- Shared success epilogue of `finish_grow` at `cliIoPl04.base + 140#64` (`+0x8c .. +0xa4`). -/
private theorem cliIoFinishGrow_epilogue_ok [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr newPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 140#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx0 : se.readReg64 .x0 = newPtr)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnew_lt63 : newCap < 2 ^ 63)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithCodeLoaded cliIoMpl (allocFinishGrowSpec A)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (Rust.hookFrame (s0.sp - 32#64) ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 newCap) newPtr bs ∗
        A.pool (allocVecGrowLb A lb oldCap.toNat newCap) (allocVecGrowLk lk oldCap.toNat) se ∗
        StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = newPtr := (hcpu_e.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hpool_ef⟩ :=
    allocCallPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef :
      A.pool (allocVecGrowLb A lb oldCap.toNat newCap) (allocVecGrowLk lk oldCap.toNat) se =
      A.pool (allocVecGrowLb A lb oldCap.toNat newCap) (allocVecGrowLk lk oldCap.toNat) sf :=
    (A.pool_transport _ _ se sf hpool_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithCodeLoaded, allocFinishGrowSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right false <|
      Entails.sepExists_right newPtr <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 0#64 <| Entails.refl _)
  simp only [Bool.false_eq_true, ↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (by rw [pure_sepConj_of_true hnew_lt63]; exact Entails.refl _)))
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

set_option maxHeartbeats 800000 in
/-- Placement-generic, `{oom}`-polymorphic proof of `signal_session_io`'s crate-local
    `<alloc::raw_vec::RawVecInner>::finish_grow` (`signalSessionIoMultiLib` block `4`,
    `168` B / `42` insns) given `hshim` (`allocAllocShimSpec`), `halloc` (`rustStdAllocSpec A`),
    and `hrealloc` (`rustStdReallocSpec A`). -/
theorem cliIoFinishGrow_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym) allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym) (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym) (rustStdReallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (cliIoWithCodeLoaded mpl (allocFinishGrowSpec A)) := by
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 4 cliIoFinishGrowSym cliIo4_lt cliIoFinishGrow_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk⟩ R s0 hpc hrun hpre hsp0
  dsimp only [cliIoWithCodeLoaded, MultiPlacedLib.withCodeLoaded, allocFinishGrowSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le_new, hcan_if⟩, hmem⟩
  have ⟨hbs_le_old, hold_lt, holdPtr_ne⟩ :
      bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64 :=
    allocSatisfies_ioVecBuf_bounds (m := s0.mem)
      (R := stackAt s0.sp (32 + Rust.hookStack) ∗ vecHeader outPtr v0 v1 v2 ∗
        A.pool lb lk s0 ∗ StdErrnoCell s0.tpidrEl0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  wp_conv_pre =>
    rw [cliIoFinishGrow_stack_split s0.sp]
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 => ?_
  by_cases hge63 : 2 ^ 63 ≤ newCap
  · -- `2 ^ 63 ≤ newCap < 2 ^ 64`): `tbnz x3, #63, 0x34` taken; returns `CapacityOverflow` (`{1, 0, v2}`).
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = true :=
      bit63_eq_one_of_ge hge63 hnew_lt64
    have hnull : NullAllowed newCap 1 := by unfold NullAllowed; omega
    apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
      (mid := s0.readReg64 .lr)
    intro s1' hcpu1_0
    have hcpu1 := hcpu1_0.1
    change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
      fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
    have hcpu_f := hcpu_f0.1
    have ⟨hacp_0f, hpool_0f⟩ :=
      allocCallPreserved_of_seg hcpu1_0 hcpu_f0 hnsp_f hsym_f
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0f : A.pool lb lk s0 = A.pool lb lk sf :=
      (A.pool_transport lb lk s0 sf hpool_0f).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun1'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · exact hcpu_f.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    refine SepWP.done hpc_f hrun_f
      ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
    have hstk_back := cliIoFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right true <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right v2 <| Entails.refl _)
    simp only [↓reduceIte, hsp1_in, hpool_eq_0f, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true hacp_0f]
    rw [pure_sepConj_of_true hnull]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail
  · -- `0 < newCap < 2 ^ 63`): valid layout `RustLayoutOk newCap 1`
    have hnew_lt63 : newCap < 2 ^ 63 := Nat.lt_of_not_ge hge63
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = false :=
      bit63_eq_zero_of_lt hnew_lt63
    have hcan : A.CanAlloc lb lk newCap 1 := hcan_if hnew_lt63
    have hlay : RustLayoutOk newCap 1 := rustLayoutOk_one hnew_pos hnew_lt63
    have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by bv_omega
    have hnew_beq0 : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    by_cases hold0 : oldCap = 0#64
    · -- `oldCap = 0#64`: `cbz x1, 0x50` taken → `shim` (`+0x54`) → `__rust_alloc` (`+0x60`)
      subst hold0
      have hbs_nil : bs = [] := by simpa using hbs_le_old
      subst hbs_nil
      apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = 0#64 := (hcpu1.readReg64 .x1).trans hx1
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_shim_pc (by simpa [arm64_norm] using hrun1')
        fun sm_sh hcpu_sh0 hcl_sh hnsp_sh hsym_sh => ?_
      have hcpu_sh := hcpu_sh0.1
      have ⟨hacp_0sh, hpool_0sh⟩ :=
        allocCallPreserved_of_seg hcpu1_0 hcpu_sh0 hnsp_sh hsym_sh
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0sh : A.pool lb lk s0 = A.pool lb lk sm_sh :=
        (A.pool_transport lb lk s0 sm_sh hpool_0sh).symm
      have hpc_sh : sm_sh.pc = signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym :=
        hcpu_sh.pc_eq.trans cliIoFinishGrow_shim_pc
      have hrun_sh : sm_sh.status = .Running := hcpu_sh.status_eq.trans hrun1'
      have hsp_sh_eq : sm_sh.sp = s0.sp - 32#64 :=
        hcpu_sh.sp_eq.trans (by simp [arm64_norm])
      have hsp_sh : sm_sh.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_sh_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_sh : sm_sh.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) := by
        rw [hcpu_sh.readReg64 .lr]; simp [arm64_norm]
      have hx19_sh : sm_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hx20_sh : sm_sh.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hgprs_sh : GrowHighGprs s0 sm_sh := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_sh.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_sh : calleeSavedVRegs sm_sh = calleeSavedVRegs s0 :=
        hcpu_sh.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0sh]
      apply seqCodeLoaded hcl_sh
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64))
      apply (SepWP.call_subroutine_frame hshim (x := ())
        hpc_sh hrun_sh hsp_sh hlr_sh
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [allocAllocShimSpec, VerifiedLibraries.RustStd.Io.rustAllocShimSpec]
        rw [hsp_sh_eq]
        exact Satisfies.mono (by sep_frame) hm'
      · intro sf_sh hpc_sfsh hrun_sfsh hsp_sfsh hcs_sfsh
        refine SepWP.done hpc_sfsh hrun_sfsh fun hcl_sfsh => ?_
        dsimp only [allocAllocShimSpec, VerifiedLibraries.RustStd.Io.rustAllocShimSpec]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hacp_sh, hbrk_sh⟩
        have hpool_sh : PoolPreserved sm_sh sf_sh :=
          ⟨hacp_sh.2.2.2.2.1, hbrk_sh, hacp_sh.2.2.2.1⟩
        have hpool_eq_sh : A.pool lb lk sm_sh = A.pool lb lk sf_sh :=
          (A.pool_transport lb lk sm_sh sf_sh hpool_sh).symm
        have hsp_sfsh_eq : sf_sh.sp = s0.sp - 32#64 := hsp_sfsh.trans hsp_sh_eq
        have hx19_sfsh : sf_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfsh.readReg64_x19.trans hx19_sh
        have hx20_sfsh : sf_sh.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfsh.readReg64_x20.trans hx20_sh
        have hgprs_sfsh : GrowHighGprs s0 sf_sh :=
          hgprs_sh.trans (GrowHighGprs.of_calleeSaved hcs_sfsh)
        have hvregs_sfsh : calleeSavedVRegs sf_sh = calleeSavedVRegs s0 :=
          hcs_sfsh.vregs.trans hvregs_sh
        apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfsh
          (mid := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
        intro sa' hcpu_a0
        have hcpu_a := hcpu_a0.1
        change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
        have hpc_a' : sa'.pc = cliIoPl04.base + 88#64 := hcpu_a.pc_eq.trans hpc_sfsh
        have hrun_a' : sa'.status = .Running := hcpu_a.status_eq.trans hrun_sfsh
        have hsp_a_in : sa'.sp = s0.sp - 32#64 := hcpu_a.sp_eq.trans hsp_sfsh_eq
        have hx19_a' : sa'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          (hcpu_a.readReg64 _).trans hx19_sfsh
        have hx20_a' : sa'.readReg64 (.gpr 20#5) = outPtr :=
          (hcpu_a.readReg64 _).trans hx20_sfsh
        wp_sym_steps
        refine SepWP.done cliIoFinishGrow_alloc_pc (by simpa [arm64_norm] using hrun_a')
          fun sm_al hcpu_al0 hcl_al hnsp_al hsym_al => ?_
        have hcpu_al := hcpu_al0.1
        have ⟨hacp_shal, hpool_shal⟩ :=
          allocCallPreserved_of_seg hcpu_a0 hcpu_al0 hnsp_al hsym_al
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_shal : A.pool lb lk sf_sh = A.pool lb lk sm_al :=
          (A.pool_transport lb lk sf_sh sm_al hpool_shal).symm
        have hacp_0al : AllocCallPreserved s0 sm_al :=
          allocCallPreserved_trans hacp_0sh (allocCallPreserved_trans hacp_sh hacp_shal)
        have htp_0al : sm_al.tpidrEl0 = s0.tpidrEl0 := hacp_0al.2.2.2.1
        have hfs_0al : sm_al.fs = s0.fs := hacp_0al.1
        have hio_0al : IoFrame s0 sm_al := ⟨hacp_0al.2.1, hacp_0al.2.2.1⟩
        have hpc_al : sm_al.pc = signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym :=
          hcpu_al.pc_eq.trans cliIoFinishGrow_alloc_pc
        have hrun_al : sm_al.status = .Running := hcpu_al.status_eq.trans hrun_a'
        have hsp_al_eq : sm_al.sp = s0.sp - 32#64 :=
          (hcpu_al.sp_eq.trans (by simp [arm64_norm])).trans hsp_a_in
        have hsp_al : sm_al.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_al_eq]; exact s0.spAligned_sub 32#64 hsp0
        have hlr_al : sm_al.readReg64 .lr =
            cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
              "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) := by
          rw [hcpu_al.readReg64 .lr]; simp [arm64_norm]
        have hx0_al_nat : (sm_al.readReg64 .x0).toNat = newCap := by
          rw [hcpu_al.readReg64 .x0]; simpa [arm64_norm] using hnew_toNat
        have hx1_al_nat : (sm_al.readReg64 .x1).toNat = 1 := by
          rw [hcpu_al.readReg64 .x1]; simp [arm64_norm]
        have hx19_al : sm_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx19_a'
        have hx20_al : sm_al.readReg64 (.gpr 20#5) = outPtr := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx20_a'
        have hgprs_al : GrowHighGprs s0 sm_al := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.2
        have hvregs_al : calleeSavedVRegs sm_al = calleeSavedVRegs s0 :=
          hcpu_al.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs sa').trans
              (hcpu_a.calleeSavedVRegs.trans hvregs_sfsh))
        wp_conv_pre => simp only [hsp_sh_eq, hpool_eq_sh, hpool_eq_shal]
        apply seqCodeLoaded hcl_al
          (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64))
        apply (SepWP.call_subroutine_frame halloc (x := (newCap, 1, lb, lk))
          hpc_al hrun_al hsp_al hlr_al
          (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
          (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (h_oom := fun _ sf_oom _ hm_oom => by
            have hm' := Satisfies.drop_mid hm_oom
            dsimp only [rustStdAllocSpec] at hm'
            rw [satisfies_pure_sepConj] at hm' ⊢
            exact ⟨⟨sm_al, hio_0al, hfs_0al, hm'.1⟩, hm'.2⟩))
        · intro R' hm'
          dsimp only [rustStdAllocSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          rw [hsp_al_eq, htp_0al]
          exact ⟨⟨hx0_al_nat, hx1_al_nat, hlay, hcan⟩, Satisfies.mono (by sep_frame) hm'⟩
        · intro sf_al hpc_sfal hrun_sfal hsp_sfal hcs_sfal
          refine SepWP.done hpc_sfal hrun_sfal fun hcl_sfal => ?_
          dsimp only [rustStdAllocSpec]
          wp_conv_pre => simp only [sepConj_assoc]
          apply SepWP.pure_elim; intro hacp_al
          have hsp_sfal_eq : sf_al.sp = s0.sp - 32#64 := hsp_sfal.trans hsp_al_eq
          have hx19_sfal : sf_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            hcs_sfal.readReg64_x19.trans hx19_al
          have hx20_sfal : sf_al.readReg64 (.gpr 20#5) = outPtr :=
            hcs_sfal.readReg64_x20.trans hx20_al
          have hgprs_sfal : GrowHighGprs s0 sf_al :=
            hgprs_al.trans (GrowHighGprs.of_calleeSaved hcs_sfal)
          have hvregs_sfal : calleeSavedVRegs sf_al = calleeSavedVRegs s0 :=
            hcs_sfal.vregs.trans hvregs_al
          by_cases hx0_al0 : sf_al.readReg64 .x0 = 0#64
          · -- `__rust_alloc` returned null: `+0x64` (`cbnz x0, 0x8c`) falls through to `+0x68`
            wp_conv_pre =>
              simp only [show (0 : BitVec 64) = 0#64 from rfl,
                hx0_al0, ↓reduceIte, hsp_al_eq, htp_0al, sepConj_assoc]
              rw [sepConj_left_comm (Rust.hookFrame _) ⌜NullAllowed newCap 1⌝,
                sepConj_left_comm (StdErrnoCell _) ⌜NullAllowed newCap 1⌝]
            apply SepWP.pure_elim; intro hnull_al
            apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 104#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_al0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hpool_be⟩ :=
              allocCallPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be : A.pool lb lk sf_al = A.pool lb lk se :=
              (A.pool_transport lb lk sf_al se hpool_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader]
              sep_entail) <|
              cliIoFinishGrow_epilogue_err A hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnull_al
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
          · -- `__rust_alloc` returned `newPtr ≠ 0`: `+0x64` (`cbnz x0, 0x8c`) jumps to `+0x8c`
            let newPtr := sf_al.readReg64 .x0
            have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_al0
            wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_al0, ↓reduceIte, hsp_al_eq, htp_0al,
              pure_sepConj_of_true (Nat.mod_one (sf_al.readReg64 .x0).toNat), sepConj_assoc]
            apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 140#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hpool_be⟩ :=
              allocCallPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be :
                A.pool (lb + A.cost newCap 1) (lk + 1) sf_al =
                A.pool (allocVecGrowLb A lb (0#64).toNat newCap) (allocVecGrowLk lk (0#64).toNat) se :=
              (A.pool_transport _ _ sf_al se hpool_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx0_e : se.readReg64 .x0 = newPtr :=
              (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader, ioVecBuf]
              simp only [↓reduceIte, hnew_ne0, hnew_toNat, List.length_nil, Nat.sub_zero,
                BitVec.add_zero, pointsToBytes_nil]
              rw [pure_sepConj_of_true ⟨Nat.zero_le 0, by decide, holdPtr_ne⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (by rw [pure_sepConj_of_true ⟨Nat.zero_le _, hnew_lt63, hx0_al0⟩]; exact Entails.refl _)))))
              sep_entail) <|
              cliIoFinishGrow_epilogue_ok A hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx0_e hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnew_lt63
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
    · -- `oldCap ≠ 0#64`: `cbz x1, 0x50` not taken → `__rust_realloc` (`+0x28`)
      have hold_beq0 : (oldCap == 0#64) = false := beq_false_of_ne hold0
      have hold_nat_ne0 : oldCap.toNat ≠ 0 := by
        intro h0; exact hold0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      wp_conv_pre =>
        simp only [ioVecBuf, hold0, ↓reduceIte,
          pure_sepConj_of_true
            (⟨hbs_le_old, hold_lt, holdPtr_ne⟩ : bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64),
          sepConj_assoc]
      apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = oldCap := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = oldPtr := (hcpu1.readReg64 .x2).trans hx2
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_realloc_pc (by simpa [arm64_norm] using hrun1')
        fun sm_re hcpu_re0 hcl_re hnsp_re hsym_re => ?_
      have hcpu_re := hcpu_re0.1
      have ⟨hacp_0re, hpool_0re⟩ :=
        allocCallPreserved_of_seg hcpu1_0 hcpu_re0 hnsp_re hsym_re
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0re : A.pool lb lk s0 = A.pool lb lk sm_re :=
        (A.pool_transport lb lk s0 sm_re hpool_0re).symm
      have htp_0re : sm_re.tpidrEl0 = s0.tpidrEl0 := hacp_0re.2.2.2.1
      have hio_0re : IoFrame s0 sm_re := ⟨hacp_0re.2.1, hacp_0re.2.2.1⟩
      have hfs_0re : sm_re.fs = s0.fs := hacp_0re.1
      have hpc_re : sm_re.pc = signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym :=
        hcpu_re.pc_eq.trans cliIoFinishGrow_realloc_pc
      have hrun_re : sm_re.status = .Running := hcpu_re.status_eq.trans hrun1'
      have hsp_re_eq : sm_re.sp = s0.sp - 32#64 :=
        hcpu_re.sp_eq.trans (by simp [arm64_norm])
      have hsp_re : sm_re.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_re_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_re : sm_re.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64) := by
        rw [hcpu_re.readReg64 .lr]; simp [arm64_norm]
      have hx0_re : sm_re.readReg64 .x0 = oldPtr := by
        rw [hcpu_re.readReg64 .x0]; simp [arm64_norm]
      have hx1_re_nat : (sm_re.readReg64 .x1).toNat = oldCap.toNat := by
        rw [hcpu_re.readReg64 .x1]; simpa [arm64_norm] using congrArg BitVec.toNat hx1_1'
      have hx2_re_nat : (sm_re.readReg64 .x2).toNat = 1 := by
        rw [hcpu_re.readReg64 .x2]; simp [arm64_norm]
      have hx3_re_nat : (sm_re.readReg64 .x3).toNat = newCap := by
        rw [hcpu_re.readReg64 .x3]; simpa [arm64_norm] using hnew_toNat
      have hx19_re : sm_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hx20_re : sm_re.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hgprs_re : GrowHighGprs s0 sm_re := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_re.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_re : calleeSavedVRegs sm_re = calleeSavedVRegs s0 :=
        hcpu_re.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0re]
      apply seqCodeLoaded hcl_re
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64))
      apply (SepWP.call_subroutine_frame hrealloc
        (x := (oldPtr, oldCap.toNat, 1, newCap, bs, lb, lk))
        hpc_re hrun_re hsp_re hlr_re
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ sf_oom _ hm_oom => by
          have hm' := Satisfies.drop_mid hm_oom
          dsimp only [rustStdReallocSpec] at hm'
          rw [satisfies_pure_sepConj] at hm' ⊢
          exact ⟨⟨sm_re, hio_0re, hfs_0re, hm'.1⟩, hm'.2⟩))
      · intro R' hm'
        dsimp only [rustStdReallocSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        rw [hsp_re_eq, htp_0re]
        exact ⟨⟨hx0_re, hx1_re_nat, hx2_re_nat, hx3_re_nat, hlay, hbs_le_old, hbs_le_new, hcan⟩,
          Satisfies.mono (by sep_frame) hm'⟩
      · intro sf_re hpc_sfre hrun_sfre hsp_sfre hcs_sfre
        refine SepWP.done hpc_sfre hrun_sfre fun hcl_sfre => ?_
        dsimp only [rustStdReallocSpec]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; intro hacp_re
        have hsp_sfre_eq : sf_re.sp = s0.sp - 32#64 := hsp_sfre.trans hsp_re_eq
        have hx19_sfre : sf_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfre.readReg64_x19.trans hx19_re
        have hx20_sfre : sf_re.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfre.readReg64_x20.trans hx20_re
        have hgprs_sfre : GrowHighGprs s0 sf_re :=
          hgprs_re.trans (GrowHighGprs.of_calleeSaved hcs_sfre)
        have hvregs_sfre : calleeSavedVRegs sf_re = calleeSavedVRegs s0 :=
          hcs_sfre.vregs.trans hvregs_re
        by_cases hx0_re0 : sf_re.readReg64 .x0 = 0#64
        · -- `__rust_realloc` returned null: `+0x2c` (`cbnz x0, 0x8c`) + `+0x30` (`b 0x68`) → `+0x68`
          wp_conv_pre =>
            simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_re0, ↓reduceIte, hsp_re_eq, htp_0re, sepConj_assoc]
            rw [sepConj_left_comm (Rust.hookFrame _) ⌜NullAllowed newCap 1⌝,
              sepConj_left_comm (StdErrnoCell _) ⌜NullAllowed newCap 1⌝]
          apply SepWP.pure_elim; intro hnull_re
          apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 104#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_re0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hpool_be⟩ :=
            allocCallPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be : A.pool lb lk sf_re = A.pool lb lk se :=
            (A.pool_transport lb lk sf_re se hpool_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, ioVecBuf]
            simp only [hold0, ↓reduceIte]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_old, hold_lt, holdPtr_ne⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_err A hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnull_re
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
        · -- `__rust_realloc` returned `newPtr ≠ 0`: `+0x2c` (`cbnz x0, 0x8c`) jumps to `+0x8c`
          let newPtr := sf_re.readReg64 .x0
          have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_re0
          wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
            hx0_re0, ↓reduceIte, hsp_re_eq, htp_0re,
            pure_sepConj_of_true (Nat.mod_one (sf_re.readReg64 .x0).toNat), sepConj_assoc]
          apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 140#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hpool_be⟩ :=
            allocCallPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be :
              A.pool (lb + A.cost newCap 1 - A.cost oldCap.toNat 1) lk sf_re =
              A.pool (allocVecGrowLb A lb oldCap.toNat newCap) (allocVecGrowLk lk oldCap.toNat) se := by
            simp only [allocVecGrowLb, allocVecGrowLk, hold_nat_ne0, ↓reduceIte]
            exact (A.pool_transport _ _ sf_re se hpool_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx0_e : se.readReg64 .x0 = newPtr :=
            (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, ioVecBuf]
            simp only [hnew_ne0, ↓reduceIte, hnew_toNat]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_new, hnew_lt63, hx0_re0⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_ok A hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx0_e hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnew_lt63
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩

/-- `withCodeLoaded` projection of `cliIoFinishGrow_ok`. -/
theorem cliIoFinishGrow_ok_withCodeLoaded {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym) allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym) (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym) (rustStdReallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (allocFinishGrowSpec A)) :=
  subroutine_ok_of_cliIoWithCodeLoaded (cliIoFinishGrow_ok A hpl hext4 hshim halloc hrealloc)

end

end LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow
