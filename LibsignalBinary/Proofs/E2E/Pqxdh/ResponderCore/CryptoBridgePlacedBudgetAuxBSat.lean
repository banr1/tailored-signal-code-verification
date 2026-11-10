/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop -- proof-setup: allow-public-import
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat

/-!
# `memset`-Free Block `53` Segments for `CryptoBridgePlacedBudgetAuxSat` (`CryptoBridgePlacedBudgetAuxBSat`)

Relocatable Block `53` segment proofs (`seg0_hmc`..`seg3_hmc`, `iter_a1_hmc`..`iter_d_done_hmc`,
`epilogue_raw_hmc`) for `<GenericHkdf<Hmac<Sha256>>>::expand_multi_info` (`okmLen ∈ {64, 80}`,
`info.length < 23`) parameterized only by `HookSatExactMemcpy H lsMemcpySym` (zero `memset`
assumptions).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxBSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet
  (Frame HmacSt RW RunsTo TraceEq blkPC_53 blkPl_53 expPlacedFakeB length_hmacWith
   lsMemcpySym rw_of_perm_eq zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPost ExpandPre ExpandSaved HmacSt.of_copy_empty_esp_64
   HmacSt.of_copy_esp_64_240 HmacSt.of_memcpy_counter HmacSt.of_write32_empty StateDone
   StateLoop StateLoopA1 StateLoopA2Placed StateLoopB StateLoopCPlaced StateLoopFin StateX0p
   StateX1Placed StateX1b StateX2Placed StateX2r agreesOutside_counter_writes
   agreesOutside_esp_write8 agreesOutside_writeBytes_le and64_255_ofNat64
   and_0xffffffffff_ofNat64 canWrite_esp_64_add cmp32_lt63_lemmas cmp_lt32_lemmas cmp_lt64_lemmas
   esp esp_aligned esp_eq_add mem_setMem read64_x0_write64_esp read64_x1_write_esp
   readBytes_32_esp_32_of_208 readBytes_eq_of_agreesOutside_esp t1 t1_length
   zeroExtend32_ofNat8_eq_truncate32 zeroExtend64_add1_truncate32_ofNat64
   zeroExtend64_add32_truncate32_ofNat64 zeroExtend64_and255_truncate32_ofNat64
   zeroExtend64_ofNat8)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (placed_memcpy_budget_steps_sat_exact)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat (RunsToVm)
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
    (hrun : s.status = .Running)
    (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToVmFrom prog s₀ (execInst inst s) P)
    (hnsvc0 : inst.isSvc0 = false := by decide)
    (hnmsr : inst.isMsrTpidrEl0 = false := by decide)
    (hsvc : prog.svc = Syscall.standard := by first | rfl | exact RunsTo.lsProg_svc) :
    RunsToVmFrom prog s₀ s P := by
  intro hL
  have hfm := Program.fetchMem_of_fetch hL hfetch
  have hstep : Step prog s (execInst inst s) :=
    Program.evalInst_eq_execInst inst s hsvc ▸ Step.exec hrun hfm
  have hL' : prog.CodeLoaded (execInst inst s).mem := hstep.codeLoaded hL
  have hvm1 : VmPreserved s (execInst inst s) :=
    (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s).toVmPreserved
      (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s)
  obtain ⟨sf, hst, hvm, htr, hP, hL''⟩ := h hL'
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
    (H : LibsignalHooks) [IsLsBlockProg prog i H]
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToVmFrom prog
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

private theorem disj_esp_info {s₀ : State} {off infoPtr : BitVec 64} {n : ℕ}
    (hn : n < 64) (hoff : off.toNat ≤ 240)
    (hout : ∀ a, InRegion infoPtr n a → OutsideRegion (s₀.sp - 640#64) 640 a) :
    n = 0 ∨ DisjointRegions (esp s₀ + off) n infoPtr n := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · have h_mod : (BitVec.ofNat 64 (n - 1)).toNat = n - 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h0_in : InRegion infoPtr n infoPtr := by unfold InRegion; bv_omega
    have hn_in : InRegion infoPtr n (infoPtr + BitVec.ofNat 64 (n - 1)) := by
      unfold InRegion; bv_omega
    have h_i0 := hout infoPtr h0_in
    have h_in := hout (infoPtr + BitVec.ofNat 64 (n - 1)) hn_in
    refine Or.inr ?_
    unfold DisjointRegions OutsideRegion esp at *
    bv_omega

private theorem hmacSt_of_memcpy_counter_64_0 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key [])
    (hinfo : info.length < 23) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 64#64) info).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 info.length)).write8
      (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 info.length) 1#8).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (info.length + 1)))
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  have hm := HmacSt.of_memcpy_counter h₀ (by decide) hinfo
    (b1 := BitVec.ofNat 8 info.length) (c := 1#8)
  dsimp only [List.length_nil, Nat.zero_add, List.nil_append] at hm
  have h64_0 : esp s₀ + 64#64 + BitVec.ofNat 64 0 = esp s₀ + 64#64 := by bv_lin
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  rw [h64_0, h127, h240, Nat.zero_add] at hm
  exact hm

private theorem hmacSt_of_memcpy_counter_64_32 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key tPrev)
    (ht : tPrev.length = 32)
    (hinfo : info.length < 23) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 96#64) info).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length))).write8
      (esp s₀ + 240#64) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length)) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length + 1)))
      (esp s₀ + 64#64) F key (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := by
  have hm := HmacSt.of_memcpy_counter h₀ (by omega) hinfo
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
  dsimp only [] at hm
  have h96 : esp s₀ + 64#64 + BitVec.ofNat 64 tPrev.length = esp s₀ + 96#64 := by
    rw [ht]; bv_lin
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  have hpos : esp s₀ + 64#64 + BitVec.ofNat 64 (tPrev.length + info.length) =
      esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length) := by
    rw [ht]
  have hlen1 : tPrev.length + info.length + 1 = 32 + info.length + 1 := by omega
  rw [h96, h127, h240, hpos, hlen1] at hm
  exact hm

private theorem disj_esp_x2_sub_96_64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen dstOff : ℕ} {s₀ : State}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (h0 : dstOff ≠ 0) (hdst : dstOff ≤ okmLen) :
    DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff ∧
    DisjointRegions (esp s₀ + 96#64) 23 (s₀.readReg64 .x2) dstOff :=
  ⟨(hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
     ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
     ⟨by omega, by have := hpre.okm_len; bv_omega⟩,
   (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 96#64)
     ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
     ⟨by omega, by have := hpre.okm_len; bv_omega⟩⟩

section SegsHmc

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

theorem seg0_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (StateX0p expPlacedFakeB okmLen s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al : (s₀.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    ExpandFrame.rw_esp hpre (Frame.refl s₀.mem _)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc], hrun,
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3], ?_, ?_⟩
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

theorem seg1_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX0p expPlacedFakeB okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX1Placed C.F prk info infoPtr okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := ExpandFrame.readable_x0 hpre hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := ExpandFrame.readable_x1 hpre hx.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.frame).2.2.1
  have h_okm_ule : BitVec.ule 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ult : BitVec.ult (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_hi : BitVec.ult 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ls : BitVec.ule (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_cmp : (AddWithCarry64 (BitVec.ofNat 64 okmLen) (bv% (2 ^ 64 - 33)) true).2.c = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  rcases cmp_lt64_lemmas (by have := hpre.info_lt; omega : info.length < 64) with
    ⟨h_info_ule, h_info_ult, h_info_cmp⟩
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.frame)
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

theorem seg2a_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hread_info : s₀.mem.Readable infoPtr info.length)
    (hdisj_info : info.length = 0 ∨ DisjointRegions infoPtr info.length (s₀.sp - 640#64) 640)
    (hx : StateX1Placed C.F prk info infoPtr okmLen s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX1b expPlacedFakeB C.F prk info okmLen s₀) := by
  apply runsToVm_of_from
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
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) info.length := hrw_esp.sub (by bv_omega)
  have hrd_info_s : s.mem.Readable infoPtr info.length :=
    (hx.common.frame.readable_iff infoPtr info.length).mpr hread_info
  have hdisj_info_esp :
      info.length = 0 ∨ DisjointRegions (esp s₀ + 64#64) info.length infoPtr info.length :=
    disj_esp_info (by omega) (by decide) hpre.out_info_stk
  have hbytes_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hbytes_info hrw_dst hrd_info_s hdisj_info_esp fun c => ?_
  dsimp only [applyMemcpyClobber]
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 23 (by omega)
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 13 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
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
      (by rw [mem_setMem, mem_setMem]; exact agreesOutside_counter_writes (by omega : info.length < 63))
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hpre.okm_len with rfl | rfl <;> rfl
  · rw [mem_setMem]
    exact hmacSt_of_memcpy_counter_64_0 hx.hmac_64 hinfo_lt

theorem seg2b_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX1b expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX2Placed C.F prk info okmLen s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
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

theorem seg3_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX2r expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB okmLen (t1 C.F prk info) (t1 C.F prk info) 1 (okmLen - 32) 32 s₀) := by
  apply runsToVm_of_from
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
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by decide, by unfold esp; bv_omega⟩)
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
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  have h_rem_ne : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
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
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info)
      (by rw [t1_length]; decide)

theorem iter_a1_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 :=
    ExpandFrame.readable_x0 hpre hx.common.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.common.frame).2.2.1
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
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.common.frame)
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
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_a2_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 :=
    ExpandFrame.readable_x1 hpre hx.common.frame
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.common.frame
  rcases cmp_lt32_lemmas (by have := hpre.info_lt; omega : info.length < 32) with
    ⟨h_info_ule32, h_info_ult32, h_info_cmp32⟩
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 64) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, rfl, hx19, rfl, hx22, hx23, rfl, hx26, rfl, ?_, ?_⟩
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
    · have hd : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_b_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hread_info : s₀.mem.Readable infoPtr info.length)
    (hdisj_info : info.length = 0 ∨ DisjointRegions infoPtr info.length (s₀.sp - 640#64) 640)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  apply runsToVm_of_from
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) info.length := hrw_esp.sub (by bv_omega)
  have hrd_info_s : s.mem.Readable infoPtr info.length :=
    (hx.common.frame.readable_iff infoPtr info.length).mpr hread_info
  have hdisj_info_esp :
      info.length = 0 ∨ DisjointRegions (esp s₀ + 96#64) info.length infoPtr info.length :=
    disj_esp_info (by omega) (by decide) hpre.out_info_stk
  have hbytes_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hbytes_info hrw_dst hrd_info_s hdisj_info_esp fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (esp s₀ + 96#64) info
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) info 23 (by omega)
  have hrw_wb : m₁.RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : 32 + info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  dsimp only [m₁] at hrw_wb hcw_pos1 hcw_pos2
  have hadd32 := zeroExtend64_add32_truncate32_ofNat64 (by omega : info.length < 32)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : 32 + info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : 32 + info.length < 64)
  have hze8_32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : 32 + info.length < 64)
  have hze8_64 := zeroExtend64_ofNat8 (by omega : 32 + info.length < 64)
  have hi1_ze := zeroExtend64_truncate32_ofNat64 (by omega : i + 1 < 64)
  rcases cmp32_lt63_lemmas (by omega : 32 + info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : 32 + info.length < 63)
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 96#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 := agreesOutside_counter_writes (m₁ := m₁) (s₀ := s₀)
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
    (b2 := BitVec.ofNat 8 (32 + info.length + 1)) (by omega : 32 + info.length < 63)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by rw [mem_setMem, mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
    exact hmacSt_of_memcpy_counter_64_32 hx.hmac_64 ht_len hinfo_lt
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · rcases disj_esp_x2_sub_96_64 hpre h0 hdst with ⟨hd2, hd1⟩
      rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
      refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 64#64 177 hd2 hA2
        (by have := hpre.okm_len; omega) ?_
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre

theorem iter_c_hmc {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19, ?_, hx22, hx23, hx24, ?_, hx28, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
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
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_d_continue_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hi : i = 1)
    (hdst : dstOff + 32 ≤ okmLen)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i 48 dstOff s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB okmLen tNext (okmSoFar ++ tNext) (i + 1) 16 (dstOff + 32) s₀) := by
  apply runsToVm_of_from
  subst hi
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
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
  have hx26 : s.readReg64 .x26 = 16#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hdisj_dst :
      32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step_vm
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl ht_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]; rfl
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) (dstOff + 32) :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by omega, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
      (by have := hpre.okm_len; omega) ?_
    rw [readBytes_add m₁ (s₀.readReg64 .x2) dstOff 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
      by_cases h0 : dstOff = 0
      · subst h0; exact hx.okm_pre
      · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (s₀.readReg64 .x2) dstOff := by
          unfold DisjointRegions; have := hpre.okm_len; bv_omega
        exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 = tNext := by
      conv_lhs => rw [← ht_len]
      exact readBytes_writeBytes_same s.mem _ tNext (by omega)
    rw [hleft, hright]

theorem iter_d_done_hmc (hmc : HookSatExactMemcpy H lsMemcpySym)
    {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand C.F prk info okmLen)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateDone expPlacedFakeB C.F prk info okmLen s₀) := by
  apply runsToVm_of_from
  let tNext := hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have hmin : min rem 32 = rem := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := by
    have h := hx.x26_eq; rw [hmin, Nat.sub_self] at h; exact h
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) rem :=
    readable_of_rw (hrw_esp.sub (by have := hpre.okm_len; bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hdisj_dst :
      rem = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (esp s₀ + 208#64) rem :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by omega, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by omega, by have := hpre.okm_len; unfold esp; bv_omega⟩)
  have hread_rem : s.mem.readBytes (esp s₀ + 208#64) rem = tNext.take rem := by
    have hslice := readBytes_slice_of_readBytes_eq s.mem (esp s₀ + 208#64) tNext
      (by rw [length_hmacWith]; exact hx.t_208) 0 rem (by rw [length_hmacWith]; omega)
    simpa using hslice
  iterate 4 s2_step_vm
  have hx2_nat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_vm_of_exact H hmc
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl hx2_nat rfl hread_rem hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) (tNext.take rem)
  have htake_len : (tNext.take rem).length = rem := by
    rw [List.length_take, length_hmacWith]; omega
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    agreesOutside_writeBytes_le s.mem _ (tNext.take rem) rem (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) okmLen :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
    (by have := hpre.okm_len; omega) ?_
  conv_lhs => rw [← hdst]
  rw [readBytes_add m₁ (s₀.readReg64 .x2) dstOff rem]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (s₀.readReg64 .x2) dstOff := by
        unfold DisjointRegions; have := hpre.okm_len; bv_omega
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem = tNext.take rem := by
    conv_lhs => rw [← htake_len]
    exact readBytes_writeBytes_same s.mem _ (tNext.take rem) (by omega)
  rw [hleft, hright, hokm]

theorem epilogue_raw_hmc {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateDone expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (ExpandPost C.F prk info okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  rcases hx.common.saved with ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end SegsHmc

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxBSat
