/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps

/-!
# Bounded `read_stdin` Chunk Loop

Proves `cliIoReadStdin_loop` for `signalSessionIoMultiLib` block `0` (`signal_session_io::read_stdin`)
from loop header `+0x48` (`STDIN_CAP = 2^20 = 1,048,576`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinLoop

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  RustStdAlloc PoolPreserved
  AllocCallPreserved IoFrame StdErrnoCell
  vecHeader ioVecBuf ioResultVecOk
  rustStdDeallocSpec allocFinishGrowSpec
  AllocSeqFits allocSeqPool
)
open VerifiedLibraries.RustStd.Io (allocCallPreserved_of_seg)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoReadSym cliIoMemcpySym cliIoFinishGrowSym cliIoRustDeallocSym
  cliIoPl00 cliIoPC00 cliIoBlockNoSvc0_00
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  poolPreserved_of_syscall ioFrame_trans ioFrame_of_allocCall
  cliIoStdinCap cliIoCap cliIoStdinCap_eq cliIoCap_mono
  cliIoCap_pos cliIoCap_lt_pow63 cliIoCap_lt_pow64
  cliIoCapIdx cliIoCapIdx_le le_cliIoCap_cliIoCapIdx
  cliIoCapIdx_eq_of_bounds cliIoCapIdx_cap_self
  cliIoReadCaps cliIoFinalCap cliIoFinalCap_zero cliIoFinalCap_pos
  allocSeqPool_cliIoReadCaps_zero allocSeqPool_cliIoReadCaps_pos
  AllocSeqFits_canAlloc_zero AllocSeqFits_canAlloc_succ
  wantBytes wantBytes_pos wantBytes_le_4096
  overCap_forces_eq_max dvd_4096_preserved no_grow_capIdx_eq grow_step_bounds
  bit63_eq_zero_of_lt bv64_ult_ofNat_true bv64_ult_ofNat_false
  bv64_beq_ofNat_false bv64_sub_ofNat
  cliIoSavedRegs12 stackBuf4096_repack
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadStdin32Spec sp_sub_4224_va_bound
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (
  cliIo0_lt cliIoReadStdin_read_pc
  cliIoReadStdin_ok_epilogue cliIoReadStdin_err_epilogue
  cliIoReadStdin_grow_from_zero cliIoReadStdin_grow_from_pos
  CliIoMidPreserved cliIoReadStdin_memcpy_backedge
)

/-- Spatial + `fs` postcondition of `read_stdin` (`rem = s0.fs.stdin.drop d0.offset`). -/
def cliIoStdinLoopResult {oom : State → State → Prop} (A : RustStdAlloc oom)
    (sret : BitVec 64) (d0 : FdEntry) (lb lk : Nat) (s0 sf : State) : SepProp :=
  let rem := s0.fs.stdin.drop d0.offset
  if rem.length ≤ cliIoStdinCap then
    ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + rem.length })⌝ ∗
      (∃∗ ptr : BitVec 64,
        ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 8 rem.length)) ptr rem) ∗
      A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 8 rem.length)).1
        (allocSeqPool A 1 lb lk (cliIoReadCaps 8 rem.length)).2 sf
  else
    ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) })⌝ ∗
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
      A.pool lb lk sf

/-- OOM postcondition of `read_stdin` (`k ≤ min rem.length cliIoStdinCap` bytes consumed). -/
def cliIoStdinOom (oom : State → State → Prop) (d0 : FdEntry) (s0 sf : State) : SepProp :=
  ⌜∃ k sm, k ≤ min (s0.fs.stdin.drop d0.offset).length cliIoStdinCap ∧
    IoFrame s0 sm ∧
    sm.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + k }) ∧
    oom sm sf⌝

section
arm64_proof_prelude

/-- Post-`read` EOF (`x0 = 0#64`) branch `+0x58 → +0x138 .. +0x160`: jumps to `Ok` epilogue. -/
private theorem cliIoReadStdin_after_read_eof [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret v0 v1 v2 cap ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 0#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = cap)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      CliIoMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ ioResultVecOk A sret cap ptr bs ∗
          A.pool lb_cur lk_cur sf ∗ StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A cap ptr bs ∗ A.pool lb_cur lk_cur sr ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 312#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 0#64 := (hcpu_r.readReg64 _).trans hx0
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hpool_re⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur se :=
    (A.pool_transport _ _ sr se hpool_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_ok_epilogue A hext0 hlo hhi hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx25)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((CliIoMidPreserved.of_alloc hacp_re).trans (CliIoMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` over-cap (`len = 1048576`, `n = 1`, `want = 1`) branch `+0x58 .. +0x84 → +0x164`. -/
private theorem cliIoReadStdin_after_read_overcap [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    {s0 sr : State} {sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4224 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = 1#64)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap 8))
    (hx23 : sr.readReg64 (.gpr 23#5) = 1#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = 1048576#64)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (htp : sr.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      CliIoMidPreserved sr sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
          A.pool lb lk sf ∗ StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sr
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 (cliIoCap 8)) ptr bs ∗
        A.pool (lb + A.cost (cliIoCap 8) 1) (lk + 1) sr ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 356#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = 1#64 := (hcpu_r.readReg64 _).trans hx0
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = 1#64 := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
  have hcpu_e := hcpu_e0.1
  have ⟨hacp_re, hpool_re⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_e0 hnsp_e hsym_e
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool (lb + A.cost (cliIoCap 8) 1) (lk + 1) sr =
      A.pool (lb + A.cost (cliIoCap 8) 1) (lk + 1) se :=
    (A.pool_transport _ _ sr se hpool_re).symm
  rw [hpool_eq]
  exact cliIoReadStdin_err_epilogue A hext0 hdealloc hlo hhi
    (cliIoCap_pos 8) (cliIoCap_lt_pow63 (by decide)) hcl_e
    (hcpu_e.pc_eq.trans (by simp [arm64_norm])) (hcpu_e.status_eq.trans hrun_r') hsp0
    (hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_e.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx21)
    (hacp_re.2.2.2.1.trans htp)
    (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
      hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f
        ((CliIoMidPreserved.of_alloc hacp_re).trans (CliIoMidPreserved.of_alloc hacp_ef)) hent

/-- Post-`read` in-cap no-grow (`0 < n ≤ want`, `len + n ≤ cap ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0xc4 .. +0xc8 → +0xcc = 204#64`. -/
private theorem cliIoReadStdin_after_read_nogrow [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hlen_cap : len + n ≤ cap) (hcap_max : cap ≤ 1048576)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sc : State,
      sc.pc = cliIoPl00.base + 204#64 → sc.status = .Running → sc.sp = s0.sp - 4224#64 →
      sc.readReg64 (.gpr 19#5) = sret → sc.readReg64 (.gpr 20#5) = ptr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = 4096#64 → sc.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 26#5) = 1048576#64 → sc.readReg64 (.gpr 27#5) = 1048577#64 →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
      AllocCallPreserved sr sc → PoolPreserved sr sc →
      SepWP P (s0.readReg64 .lr) sc Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : want < 2 ^ 64), hn_le_want]
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1048576 - len < 2 ^ 64)]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len + n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64), hlen_cap]
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hlen_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 204#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
  have hcpu_c := hcpu_c0.1
  have ⟨hacp_rc, hpp_rc⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_c0 hnsp_c hsym_c
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sc (hcpu_c.pc_eq.trans (by simp [arm64_norm])) (hcpu_c.status_eq.trans hrun_r')
    (hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_c.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_c.readReg64]; simp [arm64_norm])
    (by rw [hcpu_c.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_c hacp_rc hpp_rc

/-- Post-`read` in-cap grow (`0 < n ≤ want`, `cap < len + n ≤ 1048576`) branch
    `+0x58 .. +0x90 → +0x94 = 148#64`. -/
private theorem cliIoReadStdin_after_read_grow [CliIoPlacement]
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    {s0 sr : State} {sret ptr : BitVec 64} {Pre : SepProp}
    {cap len want n : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hn_pos : 0 < n) (hn_le_want : n ≤ want) (hwant_le : want ≤ 4096)
    (hgt_cap : cap < len + n) (hlen_max : len + n ≤ 1048576)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem)
    (hpc : sr.pc = cliIoPl00.base + 88#64) (hrun : sr.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sr.sp = s0.sp - 4224#64)
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 n)
    (hx19 : sr.readReg64 (.gpr 19#5) = sret) (hx20 : sr.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sr.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap)
    (hx23 : sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sr.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sr.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sr.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sr.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hcont : ∀ sg : State,
      sg.pc = cliIoPl00.base + 148#64 → sg.status = .Running → sg.sp = s0.sp - 4224#64 →
      sg.readReg64 .x0 = BitVec.ofNat 64 n →
      sg.readReg64 (.gpr 19#5) = sret → sg.readReg64 (.gpr 20#5) = ptr →
      sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sg.readReg64 (.gpr 24#5) = 4096#64 → sg.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sg.readReg64 (.gpr 26#5) = 1048576#64 → sg.readReg64 (.gpr 27#5) = 1048577#64 →
      sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + n) →
      sg.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sg = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem →
      AllocCallPreserved sr sg → PoolPreserved sr sg →
      SepWP P (s0.readReg64 .lr) sg Pre post oomProp) :
    SepWP P (s0.readReg64 .lr) sr Pre post oomProp := by
  have hn_beq0 : (BitVec.ofNat 64 n == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) (by omega) (by decide)
  have hbit63 : (BitVec.ofNat 64 n).getLsbD 63 = false := bit63_eq_zero_of_lt (by omega)
  have hule_w : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 want) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : want < 2 ^ 64), hn_le_want]
  have hult_w : (BitVec.ofNat 64 want).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le_want (by omega)
  have hsub26 : 1048576#64 - BitVec.ofNat 64 len = BitVec.ofNat 64 (1048576 - len) :=
    bv64_sub_ofNat (by omega)
  have hule_rem : (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (1048576 - len)) = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1048576 - len < 2 ^ 64)]; omega
  have hult_rem : (BitVec.ofNat 64 (1048576 - len)).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false (by omega) (by omega)
  have hadd28 : BitVec.ofNat 64 n + BitVec.ofNat 64 len = BitVec.ofNat 64 (len + n) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hule_cap : (BitVec.ofNat 64 (len + n)).ule (BitVec.ofNat 64 cap) = false := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len + n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64)]; omega
  have hult_cap : (BitVec.ofNat 64 cap).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (by omega)
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := cliIoPl00.base + 148#64)
  intro sr' hcpu_r0
  have hcpu_r := hcpu_r0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = cliIoPl00.base + 88#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r' : sr'.spAligned = true := by
    rw [hcpu_r.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx0_r' : sr'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_r.readReg64 _).trans hx0
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := (hcpu_r.readReg64 _).trans hx21
  have hx23_r' : sr'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_r.readReg64 _).trans hx23
  have hx25_r' : sr'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len := (hcpu_r.readReg64 _).trans hx25
  have hx26_r' : sr'.readReg64 (.gpr 26#5) = 1048576#64 := (hcpu_r.readReg64 _).trans hx26
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_r')
    fun sg hcpu_g0 hcl_g hnsp_g hsym_g => ?_
  have hcpu_g := hcpu_g0.1
  have ⟨hacp_rg, hpp_rg⟩ :=
    allocCallPreserved_of_seg hcpu_r0 hcpu_g0 hnsp_g hsym_g
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  exact hcont sg (hcpu_g.pc_eq.trans (by simp [arm64_norm])) (hcpu_g.status_eq.trans hrun_r')
    (hcpu_g.sp_eq.trans ((by simp [arm64_norm] : _ = sr'.sp).trans (hcpu_r.sp_eq.trans hsp_eq)))
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx0_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx19)
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx20)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx21_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx24)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx25_r'])
    (by rw [hcpu_g.readReg64]; simp [arm64_norm, hx26_r'])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx27)
    (by rw [hcpu_g.readReg64]; simp [arm64_norm])
    (by rw [hcpu_g.readReg64]; simp only [arm64_norm]; exact (hcpu_r.readReg64 _).trans hx29)
    (hcpu_g.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
      (hcpu_r.calleeSavedVRegs.trans hvregs)))
    hcl_g hacp_rg hpp_rg

/-- Step `+0x48 .. +0x54` and call `muslReadStdin32Spec`, landing at `+0x58 = 88#64`. -/
private theorem cliIoReadStdin_do_read [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    {s0 sl : State} {d0 : FdEntry} {sret ptr cap_bv : BitVec 64} {R_frame : SepProp}
    {len want stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4256 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hwant_le : want ≤ 4096)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hfs : sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }))
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem)
    (hpc : sl.pc = cliIoPl00.base + 72#64) (hrun : sl.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sl.sp = s0.sp - 4224#64)
    (hx19 : sl.readReg64 (.gpr 19#5) = sret) (hx20 : sl.readReg64 (.gpr 20#5) = ptr)
    (hx21 : sl.readReg64 (.gpr 21#5) = cap_bv)
    (hx23 : sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want)
    (hx24 : sl.readReg64 (.gpr 24#5) = 4096#64)
    (hx25 : sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len)
    (hx26 : sl.readReg64 (.gpr 26#5) = 1048576#64)
    (hx27 : sl.readReg64 (.gpr 27#5) = 1048577#64)
    (hx29 : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sl = calleeSavedVRegs s0)
    (hcont : ∀ (sr : State) (oldBuf : List (BitVec 8)),
      let rem := s0.fs.stdin.drop d0.offset
      let chunk := (rem.drop len).take want
      oldBuf.length = want →
      sr.pc = cliIoPl00.base + 88#64 → sr.status = .Running → sr.sp = s0.sp - 4224#64 →
      sr.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      sr.readReg64 (.gpr 19#5) = sret → sr.readReg64 (.gpr 20#5) = ptr →
      sr.readReg64 (.gpr 21#5) = cap_bv →
      sr.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want →
      sr.readReg64 (.gpr 24#5) = 4096#64 →
      sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sr.readReg64 (.gpr 26#5) = 1048576#64 →
      sr.readReg64 (.gpr 27#5) = 1048577#64 →
      sr.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs sr = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sr.mem →
      sr.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (len + chunk.length) }) →
      sr.trace = sl.trace → sr.sigActions = sl.sigActions →
      sr.tpidrEl0 = sl.tpidrEl0 → sr.brkStart = sl.brkStart →
      SepWP P (s0.readReg64 .lr) sr
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗
          (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
            memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
          R_frame ∗ A.pool lb_cur lk_cur sr)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sl
      (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        R_frame ∗ A.pool lb_cur lk_cur sl)
      post oomProp := by
  have hwant_toNat : (BitVec.ofNat 64 want).toNat = want := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  wp_conv_pre =>
    rw [memRegion_split_le (s0.sp - 4224#64) want 4096 hwant_le (by decide),
      memRegion_eq_exists_bytes (s0.sp - 4224#64) want (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro oldBuf
  wp_conv_pre =>
    rw [← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _) ⌜oldBuf.length = want⌝]
    simp only [sepConj_assoc]
  apply SepWP.pure_elim; intro hold_len
  apply sepWP_seg_cliIo_block_pure 0 cliIo0_lt hext0 cliIoBlockNoSvc0_00 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
  intro sl' hcpu_l0
  have hcpu_l := hcpu_l0.1
  change SepWP (cliIoPC00.rebase cliIoPl00.base (fun _ => none)) _ _ _ _
  have hpc_l' : sl'.pc = cliIoPl00.base + 72#64 := hcpu_l.pc_eq.trans hpc
  have hrun_l' : sl'.status = .Running := hcpu_l.status_eq.trans hrun
  have hsp_l_in : sl'.sp = s0.sp - 4224#64 := hcpu_l.sp_eq.trans hsp_eq
  have hsp_l' : sl'.spAligned = true := by
    rw [hcpu_l.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4224#64 hsp0
  have hx23_l' : sl'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 want := (hcpu_l.readReg64 _).trans hx23
  wp_sym_steps
  refine SepWP.done cliIoReadStdin_read_pc (by simpa [arm64_norm] using hrun_l')
    fun sm_rd hcpu_rd0 hcl_rd hnsp_rd hsym_rd => ?_
  have hcpu_rd := hcpu_rd0.1
  have ⟨hacp_lrd, hpool_lrd⟩ :=
    allocCallPreserved_of_seg hcpu_l0 hcpu_rd0 hnsp_rd hsym_rd
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_lrd : A.pool lb_cur lk_cur sl = A.pool lb_cur lk_cur sm_rd :=
    (A.pool_transport _ _ sl sm_rd hpool_lrd).symm
  have hpc_rd : sm_rd.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym :=
    hcpu_rd.pc_eq.trans cliIoReadStdin_read_pc
  have hrun_rd : sm_rd.status = .Running := hcpu_rd.status_eq.trans hrun_l'
  have hsp_rd_eq : sm_rd.sp = s0.sp - 4224#64 :=
    hcpu_rd.sp_eq.trans ((by simp [arm64_norm] : _ = sl'.sp).trans hsp_l_in)
  have hsp_rd : sm_rd.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_rd_eq]; exact s0.spAligned_sub 4224#64 hsp0
  have hlr_rd : sm_rd.readReg64 .lr = cliIoPl00.base + 88#64 := by
    rw [hcpu_rd.readReg64 .lr]; simp [arm64_norm]
  have hx0_rd : sm_rd.readReg32 .x0 = 0#32 := by
    simp only [State.readReg32]; rw [hcpu_rd.readReg64 .x0]; simp [arm64_norm]
  have hx1_rd : sm_rd.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_rd.readReg64 .x1]; simp [arm64_norm]
  have hx2_rd : sm_rd.readReg64 .x2 = BitVec.ofNat 64 want := by
    rw [hcpu_rd.readReg64 .x2]; simp [arm64_norm]
  have hfs_rd : sm_rd.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) :=
    hacp_lrd.1.trans hfs
  have hfds_rd : sm_rd.fs.fds 0#64 = some { d0 with offset := d0.offset + len } := by
    rw [hfs_rd]; simp [FsState.setFd]
  rw [hpool_eq_lrd]
  let d_cur : FdEntry := { d0 with offset := d0.offset + len }
  apply seqCodeLoaded hcl_rd (mid := cliIoPl00.base + 88#64)
  apply (SepWP.call_subroutine_frame hread
    (x := (s0.sp - 4224#64, BitVec.ofNat 64 want, d_cur, oldBuf))
    hpc_rd hrun_rd hsp_rd hlr_rd
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslReadStdin32Spec]
    rw [hsp_rd_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_rd, hx1_rd, hx2_rd,
      by rw [hwant_toNat]; simp only [Arm64.MAX_RW_COUNT]; omega,
      by rw [hwant_toNat]; exact sp_sub_4224_va_bound (by omega) hsp_va hwant_le,
      by rw [hwant_toNat]; exact hold_len, hfds_rd, hkind, hcanr⟩, ?_⟩
    rw [stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sr hpc_sr hrun_sr hsp_sr hcs_rdsr
    refine SepWP.done hpc_sr hrun_sr fun hcl_sr => ?_
    wp_conv_pre => dsimp only [muslReadStdin32Spec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sr, hfs_sr, htr_sr, hsys_sr⟩
    have hpool_eq_sr : A.pool lb_cur lk_cur sm_rd = A.pool lb_cur lk_cur sr :=
      (A.pool_transport _ _ sm_rd sr (poolPreserved_of_syscall hsys_sr)).symm
    have hchunk_eq :
        (sm_rd.fs.stdin.drop d_cur.offset).take (BitVec.ofNat 64 want).toNat =
          ((s0.fs.stdin.drop d0.offset).drop len).take want := by
      rw [hfs_rd, FsState.stdin_setFd, hwant_toNat]
      dsimp only [d_cur]
      rw [← List.drop_drop]
    have hfs_sr' : sr.fs = s0.fs.setFd 0#64
        (some { d0 with offset := d0.offset + (len + (((s0.fs.stdin.drop d0.offset).drop len).take want).length) }) := by
      rw [hfs_sr, hchunk_eq, hfs_rd, FsState.setFd_setFd_same]
      dsimp only [d_cur]
      rw [Nat.add_assoc]
    have hsp_sr_eq : sr.sp = s0.sp - 4224#64 := hsp_sr.trans hsp_rd_eq
    refine SepWP.weaken_pre ?_
      (hcont sr oldBuf hold_len hpc_sr hrun_sr hsp_sr_eq
        (by rwa [hchunk_eq] at hx0_sr)
        (by rw [hcs_rdsr.readReg64_x19, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx19)
        (by rw [hcs_rdsr.readReg64_x20, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx20)
        (by rw [hcs_rdsr.readReg64_x21, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx21)
        (by rw [hcs_rdsr.readReg64_x23, hcpu_rd.readReg64]; simp only [arm64_norm]; exact hx23_l')
        (by rw [hcs_rdsr.readReg64_x24, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx24)
        (by rw [hcs_rdsr.readReg64_x25, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx25)
        (by rw [hcs_rdsr.readReg64_x26, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx26)
        (by rw [hcs_rdsr.readReg64_x27, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx27)
        (by rw [hcs_rdsr.readReg64_x29, hcpu_rd.readReg64]; simp only [arm64_norm]; exact (hcpu_l.readReg64 _).trans hx29)
        (hcs_rdsr.vregs.trans (hcpu_rd.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sl').trans (hcpu_l.calleeSavedVRegs.trans hvregs))))
        hcl_sr hfs_sr' (htr_sr.trans hacp_lrd.2.1) (hsys_sr.2.1.trans hacp_lrd.2.2.1)
        (hsys_sr.1.trans hacp_lrd.2.2.2.1) (hsys_sr.2.2.brkStart_eq.trans hacp_lrd.2.2.2.2.1))
    rw [hpool_eq_sr, hchunk_eq, hsp_rd_eq,
      stackAt_shrink (s0.sp - 4224#64) (stackBytes - 4224) 32 (by omega) (by omega)]
    sep_entail

/-- Full bounded `4096`-byte `read_stdin` loop from header `+0x48 = 72#64` by strong induction on
    `fuel = cliIoStdinCap + 1 - len`. -/
theorem cliIoReadStdin_loop [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext0 : CliIoBlockNoExtern cliIoMpl P 0)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    {s0 : State} {d0 : FdEntry} {sret v0 v1 v2 : BitVec 64}
    {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop}
    (hlo : 4256 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hkind : d0.kind = .stdio) (hcanr : d0.accMode.canRead = true)
    (hfits : AllocSeqFits A 1 lb lk (cliIoReadCaps 8 (s0.fs.stdin.drop d0.offset).length))
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ cliIoStdinLoopResult A sret d0 lb lk s0 sf ∗
          StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    ∀ (fuel : Nat) (sl : State) (ptr st0 st1 st2 st3 : BitVec 64) (cap len lb_cur lk_cur : Nat),
      cliIoStdinCap + 1 - len ≤ fuel →
      len ≤ min (s0.fs.stdin.drop d0.offset).length cliIoStdinCap →
      (len < (s0.fs.stdin.drop d0.offset).length → 4096 ∣ len) →
      cap = cliIoFinalCap 8 len →
      lb_cur = (allocSeqPool A 1 lb lk (cliIoReadCaps 8 len)).1 →
      lk_cur = (allocSeqPool A 1 lb lk (cliIoReadCaps 8 len)).2 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sl.mem →
      sl.pc = cliIoPl00.base + 72#64 → sl.status = .Running → sl.sp = s0.sp - 4224#64 →
      sl.readReg64 (.gpr 19#5) = sret → sl.readReg64 (.gpr 20#5) = ptr →
      sl.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sl.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 1048576 len) →
      sl.readReg64 (.gpr 24#5) = 4096#64 → sl.readReg64 (.gpr 25#5) = BitVec.ofNat 64 len →
      sl.readReg64 (.gpr 26#5) = 1048576#64 → sl.readReg64 (.gpr 27#5) = 1048577#64 →
      sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sl = calleeSavedVRegs s0 →
      sl.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + len }) →
      sl.trace = s0.trace → sl.sigActions = s0.sigActions →
      sl.tpidrEl0 = s0.tpidrEl0 → sl.brkStart = s0.brkStart →
      SepWP P (s0.readReg64 .lr) sl
        (stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 cap) ptr ((s0.fs.stdin.drop d0.offset).take len) ∗
          A.pool lb_cur lk_cur sl ∗ StdErrnoCell s0.tpidrEl0)
        post (cliIoStdinOom oom d0 s0) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro sl ptr st0 st1 st2 st3 cap len lb_cur lk_cur
      hfuel hlen_le hdvd hcap_eq hlb_eq hlk_eq hcl hpc hrun hsp_eq
      hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
      hfs_sl htr_sl hsig_sl htp_sl hbs_sl
    let rem := s0.fs.stdin.drop d0.offset
    have hrem_def : rem = s0.fs.stdin.drop d0.offset := rfl
    let want := wantBytes 1048576 len
    have hwant_def : want = wantBytes 1048576 len := rfl
    have hcap1048 : cliIoStdinCap = 1048576 := rfl
    have hlen_max : len ≤ cliIoStdinCap := Nat.le_trans hlen_le (Nat.min_le_right _ _)
    have hlen_rem : len ≤ rem.length := Nat.le_trans hlen_le (Nat.min_le_left _ _)
    have hwant_pos : 0 < want := wantBytes_pos (by omega : len ≤ 1048576)
    have hwant_le : want ≤ 4096 := wantBytes_le_4096 1048576 len
    let R_fr : SepProp :=
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 cap) ptr (rem.take len) ∗ StdErrnoCell s0.tpidrEl0
    refine SepWP.weaken_pre (by dsimp only [R_fr]; sep_entail)
      (cliIoReadStdin_do_read A hext0 hread (R_frame := R_fr) (by omega) hhi hsp_lo hsp_va hwant_le hkind hcanr hfs_sl
        hcl hpc hrun hsp0 hsp_eq hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hvregs
        fun sr oldBuf hold_len hpc_sr hrun_sr hsp_sr hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr
            hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr hcl_sr hfs_sr htr_sr hsig_sr
            htp_sr hbs_sr => ?_)
    dsimp only [R_fr]
    let chunk := (rem.drop len).take want
    have hchunk_def : chunk = (rem.drop len).take want := rfl
    have hn_min : chunk.length = min (rem.length - len) want := by
      rw [hchunk_def, List.length_take, List.length_drop, Nat.min_comm]
    have hn_le_want : chunk.length ≤ want := by rw [hn_min]; exact Nat.min_le_right _ _
    have hn_le_rem : len + chunk.length ≤ rem.length := by rw [hn_min]; omega
    rcases Nat.eq_zero_or_pos chunk.length with hn0 | hn_pos
    · -- EOF (`chunk.length = 0`, so `len = rem.length ≤ cliIoStdinCap`)
      have hlen_eq_rem : len = rem.length := by omega
      have hrem_le_cap : rem.length ≤ cliIoStdinCap := by omega
      have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
      have htake_rem : rem.take len = rem := by rw [hlen_eq_rem, List.take_length]
      have hx0_0 : sr.readReg64 .x0 = 0#64 := by rw [hx0_sr, ← hchunk_def, hn0]
      have hx25_rem : sr.readReg64 (.gpr 25#5) = BitVec.ofNat 64 rem.length := by
        rw [hx25_sr, hlen_eq_rem]
      refine SepWP.weaken_pre ?_
        (cliIoReadStdin_after_read_eof A hext0
          (v0 := v0) (v1 := v1) (v2 := v2)
          (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
          (lb_cur := lb_cur) (lk_cur := lk_cur)
          (by omega) hhi hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
          hx0_0 hx19_sr hx20_sr hx21_sr hx25_rem hvregs_sr
          fun sf hpc_f hrun_f hsp_f hcs_f _ hmid_srf Pre_f hent =>
            hpost sf hpc_f hrun_f hsp_f hcs_f
              (hmid_srf.2.1.trans (htr_sr.trans htr_sl))
              (hmid_srf.2.2.1.trans (hsig_sr.trans hsig_sl))
              (hmid_srf.2.2.2.1.trans (htp_sr.trans htp_sl))
              (hmid_srf.2.2.2.2.trans (hbs_sr.trans hbs_sl))
              (Entails.trans hent ?_))
      · rw [htake_rem]
        let Rest : SepProp :=
          stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
            ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
            ioVecBuf A (BitVec.ofNat 64 cap) ptr rem ∗ A.pool lb_cur lk_cur sr ∗ StdErrnoCell s0.tpidrEl0
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
        rw [← hrem_def, ← hchunk_def,
          pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
        dsimp only [Rest]; sep_entail
      · unfold cliIoStdinLoopResult
        rw [← hrem_def]
        simp only [hrem_le_cap, ↓reduceIte]
        have hfs_f : sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + rem.length }) := by
          rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn0, Nat.add_zero, hlen_eq_rem]
        rw [hcap_eq, hlb_eq, hlk_eq, hlen_eq_rem, pure_sepConj_of_true hfs_f]
        have hex_ok : ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 8 rem.length)) ptr rem ⊢
            (∃∗ ptr' : BitVec 64,
              ioResultVecOk A sret (BitVec.ofNat 64 (cliIoFinalCap 8 rem.length)) ptr' rem) :=
          Entails.sepExists_right ptr (Entails.refl _)
        let RestOk : SepProp :=
          stackAt s0.sp stackBytes ∗
            A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 8 rem.length)).1
              (allocSeqPool A 1 lb lk (cliIoReadCaps 8 rem.length)).2 sf ∗
            StdErrnoCell s0.tpidrEl0
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := RestOk) hex_ok) (by dsimp only [RestOk]; sep_entail))
        dsimp only [RestOk]; sep_entail
    · -- `0 < chunk.length`
      by_cases hover : cliIoStdinCap < len + chunk.length
      · -- Over-cap (`len = cliIoStdinCap = cliIoCap 8`, `chunk.length = 1`, `cliIoStdinCap < rem.length`)
        have ⟨hlen_eq, hn_eq1, hrem_gt⟩ :=
          overCap_forces_eq_max (K := 8) hlen_le hdvd hn_min hn_pos hover
        have hwant_eq1 : want = 1 := by
          rw [hwant_def, hlen_eq]; rfl
        have hidx8 : cliIoCapIdx 8 len = 8 := by rw [hlen_eq]; exact cliIoCapIdx_cap_self 8
        have hcap8 : cap = cliIoCap 8 := by
          rw [hcap_eq, cliIoFinalCap_pos (by omega), hidx8]
        have hpool8 : allocSeqPool A 1 lb lk (cliIoReadCaps 8 len) =
            (lb + A.cost (cliIoCap 8) 1, lk + 1) := by
          rw [allocSeqPool_cliIoReadCaps_pos A (by omega), hidx8]
        have hlb8 : lb_cur = lb + A.cost (cliIoCap 8) 1 := by rw [hlb_eq, hpool8]
        have hlk8 : lk_cur = lk + 1 := by rw [hlk_eq, hpool8]
        have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
        refine SepWP.weaken_pre ?_
          (cliIoReadStdin_after_read_overcap A hext0 hdealloc
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (bs := rem.take len) (lb := lb) (lk := lk)
            (by omega) hhi hcl_sr hpc_sr hrun_sr
            hsp0 hsp_sr
            (by rw [hx0_sr, ← hchunk_def, hn_eq1]) hx19_sr hx20_sr
            (by rw [hx21_sr, hcap8]) (by rw [hx23_sr, hwant_eq1])
            (by rw [hx25_sr, hlen_eq]; rfl) hx26_sr
            (htp_sr.trans htp_sl) hvregs_sr
            fun sf hpc_f hrun_f hsp_f hcs_f _ hmid_srf Pre_f hent =>
              hpost sf hpc_f hrun_f hsp_f hcs_f
                (hmid_srf.2.1.trans (htr_sr.trans htr_sl))
                (hmid_srf.2.2.1.trans (hsig_sr.trans hsig_sl))
                (hmid_srf.2.2.2.1.trans (htp_sr.trans htp_sl))
                (hmid_srf.2.2.2.2.trans (hbs_sr.trans hbs_sl))
                (Entails.trans hent ?_))
        · rw [hcap8, hlb8, hlk8]
          let Rest : SepProp :=
            stackAt (s0.sp - 4224#64) (stackBytes - 4224) ∗ vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
              ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              ioVecBuf A (BitVec.ofNat 64 (cliIoCap 8)) ptr (rem.take len) ∗
              A.pool (lb + A.cost (cliIoCap 8) 1) (lk + 1) sr ∗ StdErrnoCell s0.tpidrEl0
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := Rest) hbuf_back) (by dsimp only [Rest]; sep_entail))
          rw [← hrem_def, ← hchunk_def,
            pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
          dsimp only [Rest]; sep_entail
        · unfold cliIoStdinLoopResult
          have hnot_le : ¬ rem.length ≤ cliIoStdinCap := by omega
          rw [← hrem_def]
          simp only [hnot_le, ↓reduceIte]
          have hfs_f : sf.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) := by
            rw [hmid_srf.1, hfs_sr, ← hchunk_def, hn_eq1, hlen_eq]; rfl
          rw [pure_sepConj_of_true hfs_f]
          sep_entail
      · -- In-cap (`len + chunk.length ≤ cliIoStdinCap`)
        have hlen'_max : len + chunk.length ≤ cliIoStdinCap := by omega
        have hlen'_le : len + chunk.length ≤ min rem.length cliIoStdinCap :=
          Nat.le_min.mpr ⟨hn_le_rem, hlen'_max⟩
        have hdvd' : len + chunk.length < rem.length → 4096 ∣ (len + chunk.length) :=
          dvd_4096_preserved (K := 8) hlen_le hdvd hn_min hn_pos hlen'_max
        have hm_lt : cliIoStdinCap + 1 - (len + chunk.length) < fuel := by omega
        by_cases hnogrow : len + chunk.length ≤ cap
        · -- No grow (`0 < len`, `cap = cliIoCap j`)
          have hlen_pos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with rfl | hp
            · rw [cliIoFinalCap_zero] at hcap_eq; omega
            · exact hp
          let j := cliIoCapIdx 8 len
          have hj : j ≤ 8 := cliIoCapIdx_le 8 len
          have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
          have hcap_le_max : cap ≤ 1048576 := by
            rw [hcap_j]; exact cliIoCap_mono hj
          have hidx_eq : cliIoCapIdx 8 (len + chunk.length) = j :=
            no_grow_capIdx_eq hlen_pos (by omega) (by rwa [← hcap_j])
          have hcap'_eq : cap = cliIoFinalCap 8 (len + chunk.length) := by
            rw [cliIoFinalCap_pos (by omega), hidx_eq, hcap_j]
          have hpool_eq_idx :
              allocSeqPool A 1 lb lk (cliIoReadCaps 8 (len + chunk.length)) =
                allocSeqPool A 1 lb lk (cliIoReadCaps 8 len) := by
            rw [allocSeqPool_cliIoReadCaps_pos A (by omega), allocSeqPool_cliIoReadCaps_pos A hlen_pos, hidx_eq]
          refine cliIoReadStdin_after_read_nogrow hext0 hn_pos hn_le_want hwant_le
            hnogrow hcap_le_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sc hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc hx25_sc
                hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_srsc hpp_srsc => ?_
          have hpool_srsc : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur sc :=
            (A.pool_transport _ _ sr sc hpp_srsc).symm
          refine SepWP.weaken_pre (by rw [hpool_srsc]; sep_entail)
            (cliIoReadStdin_memcpy_backedge A hext0 hmemcpy
              (by rw [hcap_j]; exact cliIoCap_pos j) (by rw [hcap_j]; exact cliIoCap_lt_pow63 (by omega))
              hn_le_rem hnogrow hlen'_max hwant_le hold_len hn_le_want rfl
              hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
              hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
              fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn ptr st0 st1 st2 st3
                  cap (len + chunk.length) lb_cur lk_cur (Nat.le_refl _)
                  hlen'_le hdvd' hcap'_eq
                  (by rw [hpool_eq_idx]; exact hlb_eq) (by rw [hpool_eq_idx]; exact hlk_eq)
                  hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                  hx26_sn hx27_sn hx29_sn hvregs_sn
                  (hmid_scsn.1.trans (hacp_srsc.1.trans hfs_sr))
                  (hmid_scsn.2.1.trans (hacp_srsc.2.1.trans (htr_sr.trans htr_sl)))
                  (hmid_scsn.2.2.1.trans (hacp_srsc.2.2.1.trans (hsig_sr.trans hsig_sl)))
                  (hmid_scsn.2.2.2.1.trans (hacp_srsc.2.2.2.1.trans (htp_sr.trans htp_sl)))
                  (hmid_scsn.2.2.2.2.trans (hacp_srsc.2.2.2.2.1.trans (hbs_sr.trans hbs_sl))))
        · -- Grow (`cap < len + chunk.length ≤ cliIoStdinCap`)
          have hgt_cap : cap < len + chunk.length := by omega
          refine cliIoReadStdin_after_read_grow hext0 hn_pos hn_le_want hwant_le
            hgt_cap hlen'_max hcl_sr hpc_sr hrun_sr hsp0 hsp_sr
            hx0_sr hx19_sr hx20_sr hx21_sr hx23_sr hx24_sr hx25_sr hx26_sr hx27_sr hx29_sr hvregs_sr
            fun sg hpc_sg hrun_sg hsp_sg hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg hvregs_sg hcl_sg hacp_srsg hpp_srsg => ?_
          have hpool_srsg : A.pool lb_cur lk_cur sr = A.pool lb_cur lk_cur sg :=
            (A.pool_transport _ _ sr sg hpp_srsg).symm
          have hfs_sg : sg.fs = s0.fs.setFd 0#64
              (some { d0 with offset := d0.offset + (len + chunk.length) }) :=
            hacp_srsg.1.trans hfs_sr
          have htr_sg : sg.trace = s0.trace := hacp_srsg.2.1.trans (htr_sr.trans htr_sl)
          have hsig_sg : sg.sigActions = s0.sigActions := hacp_srsg.2.2.1.trans (hsig_sr.trans hsig_sl)
          have htp_sg : sg.tpidrEl0 = s0.tpidrEl0 := hacp_srsg.2.2.2.1.trans (htp_sr.trans htp_sl)
          have hbs_sg : sg.brkStart = s0.brkStart := hacp_srsg.2.2.2.2.1.trans (hbs_sr.trans hbs_sl)
          have hoom_sg : ∀ (sm sf_oom : State),
              IoFrame sg sm → sm.fs = sg.fs → oom sm sf_oom → emp ⊢ cliIoStdinOom oom d0 s0 sf_oom := by
            intro sm sf_oom hif hfs_m hoom_m
            unfold cliIoStdinOom
            exact Entails.pure_right_only ⟨len + chunk.length, sm, hlen'_le,
              ⟨hif.1.trans htr_sg, hif.2.trans hsig_sg⟩, hfs_m.trans hfs_sg, hoom_m⟩ (Entails.refl _)
          rcases Nat.eq_zero_or_pos len with rfl | hlen_pos
          · -- `len = 0`, `cap = 0 → cliIoCap 0 = 4096`
            have hcap0 : cap = 0 := hcap_eq
            subst hcap0
            have hlb0 : lb_cur = lb := hlb_eq
            have hlk0 : lk_cur = lk := hlk_eq
            have hcan0 : A.CanAlloc lb lk 4096 1 :=
              AllocSeqFits_canAlloc_zero (K := 8) (by omega : 0 < rem.length) hfits
            have hidx0 : cliIoCapIdx 8 chunk.length = 0 :=
              cliIoCapIdx_eq_of_bounds (Nat.zero_le 8) (Or.inl rfl) (Nat.le_trans hn_le_want hwant_le)
            have hpool0 : allocSeqPool A 1 lb lk (cliIoReadCaps 8 chunk.length) =
                (lb + A.cost (cliIoCap 0) 1, lk + 1) := by
              rw [allocSeqPool_cliIoReadCaps_pos A hn_pos, hidx0]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hlb0, hlk0]; sep_entail)
              (cliIoReadStdin_grow_from_zero A hext0 hfg hlo hhi hn_pos
                (Nat.le_trans hn_le_want hwant_le) hcan0 hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg hx21_sg hx24_sg hx25_sg hx26_sg hx27_sg
                (by rw [Nat.zero_add] at hx28_sg; exact hx28_sg) hx29_sg htp_sg hvregs_sg hoom_sg
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge A hext0 hmemcpy
                    (cliIoCap_pos 0) (cliIoCap_lt_pow63 (by decide))
                    hn_le_rem (Nat.le_trans (by rw [Nat.zero_add]; exact hn_le_want) hwant_le)
                    hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc (by rw [Nat.zero_add]; exact hx28_sc) hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (0 + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap 0) (0 + chunk.length) (lb + A.cost (cliIoCap 0) 1) (lk + 1)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by simp [cliIoFinalCap_pos hn_pos, hidx0])
                        (by simp [hpool0]) (by simp [hpool0])
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                        (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                        (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg)))
          · -- `0 < len`, `cap = cliIoCap j → cliIoCap (j + 1)`
            let j := cliIoCapIdx 8 len
            have hj : j ≤ 8 := cliIoCapIdx_le 8 len
            have hcap_j : cap = cliIoCap j := by rw [hcap_eq, cliIoFinalCap_pos hlen_pos]
            have hlen_le_j : len ≤ cliIoCap j := le_cliIoCap_cliIoCapIdx hlen_max
            have ⟨hj1, hj1_r, hidx_j1, hle_j1, _⟩ :=
              grow_step_bounds (K := 8) (by decide) hj hlen_le_j
                (Nat.le_trans hn_le_want hwant_le) hn_le_rem hlen'_max (by rwa [← hcap_j])
            have hcan_succ : A.CanAlloc (lb + A.cost (cliIoCap j) 1) (lk + 1) (cliIoCap (j + 1)) 1 :=
              AllocSeqFits_canAlloc_succ (K := 8) (by omega : 0 < rem.length) hj1_r hfits
            have hpool_j : allocSeqPool A 1 lb lk (cliIoReadCaps 8 len) =
                (lb + A.cost (cliIoCap j) 1, lk + 1) :=
              allocSeqPool_cliIoReadCaps_pos A hlen_pos lb lk
            have hlb_j : lb_cur = lb + A.cost (cliIoCap j) 1 := by rw [hlb_eq, hpool_j]
            have hlk_j : lk_cur = lk + 1 := by rw [hlk_eq, hpool_j]
            have hpool_j1 : allocSeqPool A 1 lb lk (cliIoReadCaps 8 (len + chunk.length)) =
                (lb + A.cost (cliIoCap (j + 1)) 1, lk + 1) := by
              rw [allocSeqPool_cliIoReadCaps_pos A (by omega), hidx_j1]
            refine SepWP.weaken_pre (by rw [hpool_srsg, hcap_j, hlb_j, hlk_j]; sep_entail)
              (cliIoReadStdin_grow_from_pos A hext0 hfg hlo hhi hj1 hlen_le_j
                (List.length_take_of_le hlen_rem) (by rwa [← hcap_j]) hle_j1 hcan_succ
                hcl_sg hpc_sg hrun_sg hsp0 hsp_sg
                hx0_sg hx19_sg hx20_sg (by rw [hx21_sg, hcap_j]) hx24_sg hx25_sg
                hx26_sg hx27_sg hx28_sg hx29_sg htp_sg hvregs_sg hoom_sg
                fun sc newPtr st1' st2' hpc_sc hrun_sc hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc
                    hx24_sc hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc hcl_sc hacp_sgsc =>
                  cliIoReadStdin_memcpy_backedge A hext0 hmemcpy
                    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 (by omega))
                    hn_le_rem hle_j1 hlen'_max hwant_le hold_len hn_le_want rfl
                    hcl_sc hpc_sc hrun_sc hsp0 hsp_sc hx19_sc hx20_sc hx22_sc hx23_sc hx24_sc
                    hx25_sc hx26_sc hx27_sc hx28_sc hx29_sc hvregs_sc
                    fun sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn hx25_sn
                        hx26_sn hx27_sn hx29_sn hvregs_sn hcl_sn hmid_scsn =>
                      ih (cliIoStdinCap + 1 - (len + chunk.length)) hm_lt sn newPtr 0#64 st1' st2' st3
                        (cliIoCap (j + 1)) (len + chunk.length)
                        (lb + A.cost (cliIoCap (j + 1)) 1) (lk + 1)
                        (Nat.le_refl _) hlen'_le hdvd'
                        (by rw [cliIoFinalCap_pos (by omega), hidx_j1])
                        (by rw [hpool_j1]) (by rw [hpool_j1])
                        hcl_sn hpc_sn hrun_sn hsp_sn hx19_sn hx20_sn hx21_sn hx23_sn hx24_sn
                        hx25_sn hx26_sn hx27_sn hx29_sn hvregs_sn
                        (hmid_scsn.1.trans (hacp_sgsc.1.trans hfs_sg))
                        (hmid_scsn.2.1.trans (hacp_sgsc.2.1.trans htr_sg))
                        (hmid_scsn.2.2.1.trans (hacp_sgsc.2.2.1.trans hsig_sg))
                        (hmid_scsn.2.2.2.1.trans (hacp_sgsc.2.2.2.1.trans htp_sg))
                        (hmid_scsn.2.2.2.2.trans (hacp_sgsc.2.2.2.2.1.trans hbs_sg)))

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinLoop
