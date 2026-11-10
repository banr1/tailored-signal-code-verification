/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# `memset`-Free Block `53` `96`-Byte Segments (`CryptoCalleesPlacedBudgetAuxBSat`)

Relocatable Block `53` segment proofs (`seg0_96_hmc`..`seg3_96_hmc`,
`iter_a1_96_hmc`..`iter_c_96_hmc`, `iter_d_continue_96_hmc`, `iter_d_done_96_hmc`) for
`<GenericHkdf<Hmac<Sha256>>>::expand_multi_info` (`okmLen = 96`, `info.length = 46`)
parameterized only by `H lsMemcpySym = some memcpyHook` and
`H lsCompress256Sym = some (compress256Hook C.F)` (zero `memset` assumptions), so they
instantiate both on `H` and on `hmacNoMemsetExcHooks C.F H`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxBSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ)
open CryptoVerification.LibsignalAesCbc (memcpyHook)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (Frame HmacSt RW RunsTo TraceEq blkPC_53 blkPl_53 expPlacedFakeB hmacInnerInit hmacOuterInit
   length_hmacWith lsCompress256Sym lsMemcpySym rw_of_perm_eq shaStateBytes_length)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandSaved HmacSt.of_copy_empty_esp_64 HmacSt.of_copy_esp_64_240
   HmacSt.of_write32_empty StateDone StateLoop StateLoopA1 StateLoopFin StateX0p StateX1Placed
   StateX1b StateX2Placed StateX2r agreesOutside_esp_write64 agreesOutside_esp_write8
   agreesOutside_writeBytes_le esp esp_aligned mem_setMem readBytes_32_esp_32_of_208
   readBytes_eq_of_agreesOutside_esp t1 t1_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ExpandCommon.of_write64_esp0_and_low64 ExpandPre96_46 HmacSt.of_memcpy_counter_64_0_46
   HmacStGen.of_copy_esp_64_240 HmacStGen.of_memcpy14_counter StateLoopA2_96Placed
   StateLoopB1_96Placed StateLoopB2_96Placed StateLoopB_96 StateLoopC_96Placed)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (placed_memcpy_budget_steps_sat_exact)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm s2_compress256_step_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private def RunsToVmFrom (prog : Program) (s₀ s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ sf : State,
      Steps prog s sf ∧ VmPreserved s sf ∧ TraceEq s₀ sf ∧ P sf ∧ prog.CodeLoaded sf.mem

private theorem runsToVm_of_from {prog : Program} {s : State} {P : State → Prop}
    (h : RunsToVmFrom prog s s P) : RunsToVm prog s P :=
  fun hL =>
    let ⟨sf, hst, hvm, ⟨htr, hv⟩, hp, hL'⟩ := h hL
    ⟨sf, hst, hvm, htr, hv, hp, hL'⟩

private theorem runsToVmFrom_refl {prog : Program} {s₀ s : State} {P : State → Prop} (h : P s)
    (htr : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩)) :
    RunsToVmFrom prog s₀ s P :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, htr, h, hL⟩

private theorem runsToVmFrom_step {prog : Program} {s₀ s : State} {inst : Instr} {P : State → Prop}
    (hrun : s.status = .Running) (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToVmFrom prog s₀ (execInst inst s) P)
    (hnsvc0 : inst.isSvc0 = false := by decide)
    (hnmsr : inst.isMsrTpidrEl0 = false := by decide)
    (hsvc : prog.svc = Syscall.standard := by first | rfl | exact RunsTo.lsProg_svc) :
    RunsToVmFrom prog s₀ s P := by
  intro hL
  have hfm := Program.fetchMem_of_fetch hL hfetch
  have hstep : Step prog s (execInst inst s) :=
    Program.evalInst_eq_execInst inst s hsvc ▸ Step.exec hrun hfm
  have hvm1 : VmPreserved s (execInst inst s) :=
    (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s).toVmPreserved
      (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s)
  obtain ⟨sf, hst, hvm, htr, hP, hL''⟩ := h (hstep.codeLoaded hL)
  exact ⟨sf, .step hstep hst, hvm1.trans hvm, htr, hP, hL''⟩

local macro "s2_step_vm" : tactic =>
  `(tactic| (
    refine runsToVmFrom_step (inst := ?inst) ?hrun ?hfetch ?_ ?hnsvc0 ?hnmsr
    case hfetch => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
    (case hnsvc0 => rfl); (case hnmsr => rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry,
      execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect,
      execCondCompare, execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit,
      execStr, execLdp, execStp, evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg,
      checkRegSPAligned, checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal,
      Reg.fromZRBits, Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

private theorem s2_memcpy_step_vm_of_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (H : LibsignalHooks) [IsLsBlockProg prog i H] (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running) (hsp : s.spAligned = true) (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len) (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs) (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len) (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber, RunsToVmFrom prog
      (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c)
      (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (htr0 : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToVmFrom prog s₀ s Q := by
  intro hL
  obtain ⟨c, hst1, hvm1, htr1, hv1⟩ :=
    placed_memcpy_budget_steps_sat_exact (prog := prog) (i := i) h_mc
      hrun hpc hx0 hx1 hx2 hlr hsp hread hrw hreadable hdisj hi hunmut
  obtain ⟨sf, hst2, hvm2, htr2, hQ, hL2⟩ := h c (hst1.codeLoaded hL)
  exact ⟨sf, hst1.trans hst2, hvm1.trans hvm2, (htr2.trans ⟨htr1, hv1⟩).trans htr0, hQ, hL2⟩

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

private theorem readable_sub {m : Memory} {b b' : BitVec 64} {n n' : ℕ}
    (hr : m.Readable b n) (h : ∀ a, InRegion b' n' a → InRegion b n a) :
    m.Readable b' n' :=
  fun a ha => hr a (h a ha)

private theorem disj_esp_info46_46 {s₀ : State} {infoPtr : BitVec 64}
    (hout : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a) :
    DisjointRegions (esp s₀ + 64#64) 46 infoPtr 46 := by
  have h_i0 := hout infoPtr (by unfold InRegion; bv_omega)
  have h_in := hout (infoPtr + 45#64) (by unfold InRegion; bv_omega)
  unfold OutsideRegion at h_i0 h_in; unfold DisjointRegions esp; bv_omega

private theorem disj_esp_info46_32 {s₀ : State} {infoPtr : BitVec 64}
    (hout : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a) :
    DisjointRegions (esp s₀ + 96#64) 32 infoPtr 32 := by
  have h_i0 := hout infoPtr (by unfold InRegion; bv_omega)
  have h_in := hout (infoPtr + 31#64) (by unfold InRegion; bv_omega)
  unfold OutsideRegion at h_i0 h_in; unfold DisjointRegions esp; bv_omega

private theorem disj_esp_info46_14 {s₀ : State} {infoPtr : BitVec 64}
    (hout : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a) :
    DisjointRegions (esp s₀ + 64#64) 14 (infoPtr + 32#64) 14 := by
  have h_i0 := hout (infoPtr + 32#64) (by unfold InRegion; bv_omega)
  have h_in := hout (infoPtr + 45#64) (by unfold InRegion; bv_omega)
  unfold OutsideRegion at h_i0 h_in; unfold DisjointRegions esp; bv_omega

section Segments96Hmc

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

theorem seg0_96_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (StateX0p expPlacedFakeB 96 s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al := hpre.sp_aligned
  have hesp := esp_aligned hsp_al
  have hrw : s₀.mem.RW (esp s₀) 496 := by
    unfold esp; exact hpre.rw_stack.sub (by bv_omega)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    by rw [State.status_setMem]; simp only [arm64_norm, hrun],
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact
      { m400 := by simp (config := { decide := true }) only [arm64_norm]
        m408 := by simp (config := { decide := true }) only [arm64_norm]
        m416 := by simp (config := { decide := true }) only [arm64_norm]
        m424 := by simp (config := { decide := true }) only [arm64_norm]
        m432 := by simp (config := { decide := true }) only [arm64_norm]
        m440 := by simp (config := { decide := true }) only [arm64_norm]
        m448 := by simp (config := { decide := true }) only [arm64_norm]
        m456 := by simp (config := { decide := true }) only [arm64_norm]
        m464 := by simp (config := { decide := true }) only [arm64_norm]
        m472 := by simp (config := { decide := true }) only [arm64_norm]
        m480 := by simp (config := { decide := true }) only [arm64_norm]
        m488 := by simp (config := { decide := true }) only [arm64_norm] }
  · exact ExpandFrame.of_agreesOutside_esp (off := 400#64) (sz := 96)
      (Frame.refl s₀.mem _) (by prove_agrees_esp) (by decide)

theorem seg1_96_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX0p expPlacedFakeB 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX1Placed C.F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 144 := hpre.readable_x0 hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    hpre.info_ptr_eq hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.frame).2.2.1
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved
       (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame
       (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    rfl, rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.frame)
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])

theorem seg2a_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hread_info : s₀.mem.Readable infoPtr 46)
    (hx : StateX1Placed C.F prk info infoPtr 96 s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX1b expPlacedFakeB C.F prk info 96 s₀) := by
  apply runsToVm_of_from
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 46#64 := by rw [hx.x26_eq, hpre.info_len_eq]
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq
  have hx2 : s.readReg64 .x2 = 46#64 := by rw [hx.x2_eq, hpre.info_len_eq]
  have hlr := hx.lr_eq; have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 46 := hrw_esp.sub (by bv_omega)
  have hrd_info_s : s.mem.Readable infoPtr 46 :=
    (hx.common.frame.readable_iff infoPtr 46).mpr hread_info
  have hdisj_info : 46 = 0 ∨ DisjointRegions (esp s₀ + 64#64) 46 infoPtr 46 :=
    Or.inr (disj_esp_info46_46 hpre.out_info_stk)
  have hbytes_info : s.mem.readBytes infoPtr 46 = info :=
    hpre.info_bytes_eq hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = 46 := by rw [hx2]; rfl
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hbytes_info hrw_dst hrd_info_s hdisj_info fun c => ?_
  dsimp only [applyMemcpyClobber]
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 46 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 46 (by rw [hpre.info_len_eq])
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  iterate 13 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_⟩
  rw [mem_setMem]
  exact HmacSt.of_memcpy_counter_64_0_46 hx.hmac_64 hpre.info_len_eq

theorem seg2b_96_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX1b expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX2Placed C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 144) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx22, hx23, hx26, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_esp_64_240 hx.hmac_64
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])

theorem seg3_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX2r expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) := by
  apply runsToVm_of_from
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 : s.readReg64 .x26 = 64#64 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 := hrw_x2.sub (by bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩).sub_right
      (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step_vm
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl hx.t1_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2) (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem (s₀.readReg64 .x2) (t1 C.F prk info) 32
      (by rw [t1_length])
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 9 s2_step_vm
  refine runsToVmFrom_refl ?_
  refine ⟨by simp only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    rfl, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht1_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = t1 C.F prk info := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 0#64) 32 (esp s₀ + 208#64) 32 := by
        rw [BitVec.add_zero]
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info)
      (by rw [t1_length]; decide)

theorem iter_a1_96_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 144 := hpre.readable_x0 hx.common.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.common.frame).2.2.1
  iterate 26 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 256) hx.common hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.common.frame)
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
  · dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256
      (by unfold DisjointRegions; bv_omega) (by prove_agrees_esp) (by decide) hx.t_cache
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 64#64) 256 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_a2_96_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar 96 i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hm8 := hx.common.m8_eq
  have hm16 := hx.common.m16_eq
  have hx8 := hx.x8_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.common.frame
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr := hpre.info_ptr_eq hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.common.frame
  iterate 19 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_write64_esp0_and_low64 hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) rfl,
    rfl, rfl, rfl, rfl, hx19, hx22, hx23, hx26, rfl,
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacSt.of_write32_empty hx.hmac_64 hx.t_cache ht_len
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd64 : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd0 : DisjointRegions (esp s₀ + 0#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 0#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      refine readBytes_eq_of_agreesOutside_esp s₀ _ 0#64 8 hd0
        (by rw [BitVec.add_zero]
            exact (AgreesOutside.rfl' _ (esp s₀) 8).write64 (by bv_omega) (by decide))
        (by omega) ?_
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd64 (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_b1_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hread_info : s₀.mem.Readable infoPtr 46)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  apply runsToVm_of_from
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq; have hlr := hx.lr_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq; have hx28 := hx.x28_eq; have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) 32 := hrw_esp.sub (by bv_omega)
  have hrd_info32 : s.mem.Readable infoPtr 32 :=
    readable_sub ((hx.common.frame.readable_iff infoPtr 46).mpr hread_info)
      (fun a ha => by unfold InRegion at ha ⊢; bv_omega)
  have hdisj_info : 32 = 0 ∨ DisjointRegions (esp s₀ + 96#64) 32 infoPtr 32 :=
    Or.inr (disj_esp_info46_32 hpre.out_info_stk)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hread_info32 : s.mem.readBytes infoPtr 32 = info.take 32 := by
    have h := readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 0 32 (by rw [hpre.info_len_eq]; decide)
    simpa using h
  have htake32_len : (info.take 32).length = 32 := by simp [hpre.info_len_eq]
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hread_info32 hrw_dst hrd_info32 hdisj_info fun c => ?_
  dsimp only [applyMemcpyClobber]
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 96#64) (info.take 32) = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) (info.take 32) 32 (by rw [htake32_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hcnt1_m1 : m₁.read64 (esp s₀ + 160#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega)]
    have h := hx.hmac_64.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 96#64 = esp s₀ + 160#64 by bv_lin] at h
  have hx27_96 : esp s₀ + 64#64 + 96#64 = esp s₀ + 160#64 := by bv_lin
  have hx27_64 : esp s₀ + 64#64 + 64#64 = esp s₀ + 128#64 := by bv_lin
  iterate 7 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ (m₁.write64 (esp s₀ + 160#64) 2#64) (esp s₀ + 160#64) 8 :=
    agreesOutside_esp_write64 (AgreesOutside.rfl' _ _ _) (by decide)
  have hm0_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀) = infoPtr + 32#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.m0_eq
  have hblk_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 64#64) 64 =
      tPrev ++ info.take 32 := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [readBytes_add m₁ (esp s₀ + 64#64) 32 32,
        show esp s₀ + 64#64 + BitVec.ofNat 64 32 = esp s₀ + 96#64 by bv_lin]
    have hleft : m₁.readBytes (esp s₀ + 64#64) 32 = tPrev := by
      refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
      have h := hx.hmac_64.2.1; rwa [ht_len] at h
    have hright : m₁.readBytes (esp s₀ + 96#64) 32 = info.take 32 := by
      rw [← hm1_def]
      have h := readBytes_writeBytes_same s.mem (esp s₀ + 96#64) (info.take 32) (by omega)
      rwa [htake32_len] at h
    rw [hleft, hright]
  have hist_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (hmacInnerInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.1
    rwa [show esp s₀ + 64#64 + 64#64 = esp s₀ + 128#64 by bv_lin] at h
  have hcnt1_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 160#64) = 2#64 := by
    simp (config := { decide := true }) only [arm64_norm]
  have host_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 104#64 = esp s₀ + 168#64 by bv_lin] at h
  have hcnt2_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    refine (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.2
    rwa [show esp s₀ + 64#64 + 136#64 = esp s₀ + 200#64 by bv_lin] at h
  have hokm_m2 :
      (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 96#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 96#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 160#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 160#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 160#64) (sz := 8) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx27_64],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp (config := { decide := true }) only [arm64_norm, hx28],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hm0_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hblk_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]; exact hokm_m2⟩

theorem iter_b2_96_hc256 (hc256 : H lsCompress256Sym = some (compress256Hook C.F))
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_128 : s.mem.RW (esp s₀ + 128#64) 32 := hrw_esp.sub (by bv_omega)
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hpre.info_len_eq]
  refine s2_compress256_step_of_eq hc256 hrun hpc hx0 hx1 hx2 hlr
    hx.ist_128 hx.blk_64 hblk_len hrw_128 ?_
  generalize hist_def : shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 128#64) ist' = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 128#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 128#64) ist' 32 (by rw [hist'_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hm0_m1 : m₁.read64 (esp s₀) = infoPtr + 32#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega), hx.m0_eq]
  iterate 11 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8)
      (esp s₀ + 127#64) 1 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  have hpos_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read8
      (esp s₀ + 127#64) = 14#8 :=
    Memory.read8_write8_same _ _ _
  have hist_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 128#64) 32 =
      shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [← hm1_def, hist_def]
    have h :=
      readBytes_writeBytes_same s.mem (esp s₀ + 128#64) ist' (by rw [hist'_len]; decide)
    rwa [hist'_len] at h
  have hcnt1_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 160#64) = 2#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt1_160
  have host_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.ost_168
  have hcnt2_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt2_200
  have hokm_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 128#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 128#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 127#64) 1 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 127#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 127#64) (sz := 1) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hpos_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hokm_m2⟩

theorem iter_b3_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hread_info : s₀.mem.Readable infoPtr 46)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  apply runsToVm_of_from
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq; have hlr := hx.lr_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq; have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 14 := hrw_esp.sub (by bv_omega)
  have hrd_info14 : s.mem.Readable (infoPtr + 32#64) 14 :=
    readable_sub ((hx.common.frame.readable_iff infoPtr 46).mpr hread_info)
      (fun a ha => by unfold InRegion at ha ⊢; bv_omega)
  have hdisj_info : 14 = 0 ∨ DisjointRegions (esp s₀ + 64#64) 14 (infoPtr + 32#64) 14 :=
    Or.inr (disj_esp_info46_14 hpre.out_info_stk)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hdrop_len : (info.drop 32).length = 14 := by simp [hpre.info_len_eq]
  have hread_info14 : s.mem.readBytes (infoPtr + 32#64) 14 = info.drop 32 := by
    have h := readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 32 14 (by rw [hpre.info_len_eq])
    exact h.trans (List.take_of_length_le (by rw [hdrop_len]))
  have hx2_nat : (s.readReg64 .x2).toNat = 14 := by rw [hx2]; rfl
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hread_info14 hrw_dst hrd_info14 hdisj_info fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (esp s₀ + 64#64) (info.drop 32)
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hpos_m1 : m₁.read8 (esp s₀ + 127#64) = 14#8 := by
    rw [hA1.1 (esp s₀ + 127#64) (by simp only [OutsideRegion]; bv_omega), hx.pos_127]
  dsimp only [m₁] at hrw_wb hpos_m1
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  let cnt := BitVec.ofNat 8 (i + 1)
  have hA2 : AgreesOutside m₁
      (((m₁.write8 (esp s₀ + 240#64) cnt).write8 (esp s₀ + 78#64) cnt).write8 (esp s₀ + 127#64) 15#8)
      (esp s₀ + 64#64) 177 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · rw [mem_setMem]
    exact HmacStGen.of_memcpy14_counter ht_len hpre.info_len_eq
      hx.ist_128 hx.cnt1_160 hx.ost_168 hx.cnt2_200
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 64#64) 14 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      simp only [arm64_norm]
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)

theorem iter_c_96_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 144) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19,
    by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    hx22, hx23, hx24,
    by rcases hrem with rfl | rfl <;> rfl,
    hx28, ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacStGen.of_copy_esp_64_240 hx.hmac_64
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 144 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 144 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_d_continue_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar tNext : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 1 64 32 s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  apply runsToVm_of_from
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq; have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 32#64) 32 := hrw_x2.sub (by bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
      (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step_vm
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl ht_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 32#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 32#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step_vm
  refine runsToVmFrom_refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 64 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
    rw [show (64 : ℕ) = 32 + 32 from rfl, readBytes_add m₁ (s₀.readReg64 .x2) 32 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) 32 = okmSoFar := by
      have hd1 : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (s₀.readReg64 .x2) 32 := by
        unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + 32#64) 32 = tNext := by
      have h := readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 32#64) tNext (by omega)
      rwa [ht_len] at h
    rw [hleft, hright]

theorem iter_d_done_96_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 2 32 64 s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateDone expPlacedFakeB C.F prk info 96 s₀) := by
  apply runsToVm_of_from
  generalize htNext : hmacWith C.F prk (tPrev ++ info ++ [3#8]) = tNext
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [← htNext, length_hmacWith]
  rw [htNext] at hokm
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 64#64) 32 := hrw_x2.sub (by bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 64#64) ⟨by decide, by bv_omega⟩).sub_right
      (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step_vm
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl ht_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 64#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 64#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step_vm
  refine runsToVmFrom_refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    ?_⟩
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 96 :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
  rw [show (96 : ℕ) = 64 + 32 from rfl, readBytes_add m₁ (s₀.readReg64 .x2) 64 32]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) 64 = okmSoFar := by
    have hd1 : DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (s₀.readReg64 .x2) 64 := by
      unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + 64#64) 32 = tNext := by
    have h := readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 64#64) tNext (by omega)
    rwa [ht_len] at h
  rw [hleft, hright, hokm]

end Segments96Hmc

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxBSat
