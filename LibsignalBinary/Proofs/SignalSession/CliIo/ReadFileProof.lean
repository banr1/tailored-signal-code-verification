/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileLoop
public import LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow

/-!
# Placement-Generic Proof of `signal_session_io::read_file`

Proves `cliIoReadFileGen_ok`, `cliIoReadFile_ok`, and `cliIoReadFileRo_ok` for
`signalSessionIoMultiLib` block `3` (`572` B, `8320`-B stack frame):
- Rejects `4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes` with `Err(())` before `open`.
- Returns `Ok([])` on `ENOENT`, and `Err(())` on `ENOTDIR`, `EMFILE`, or `.localDir`.
- On `.localFile`, reads up to `2 MiB` (`2,097,152` B) via `cliIoReadCaps 9 bs.length`, closes `fd`
  (`sf.fs = s0.fs`), returns `Ok(bs)` in cap or frees and returns `Err(())` over cap, and propagates
  allocator OOM via `cliIoReadFileOom`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.SignalSession (PathOk pathComps)
open VerifiedLibraries.Musl (memcpySrc muslErrnoLocationSpec)
open VerifiedLibraries.RustStd (
  RustStdAlloc StdErrnoCell stdErrnoAddr
  AllocCallPreserved
  vecHeader ioVecBuf ioResultVecOk cPathOf
  allocAllocShimSpec rustStdAllocSpec rustStdReallocSpec rustStdDeallocSpec
  allocFinishGrowSpec AllocSeqFits allocSeqPool
)
open VerifiedLibraries.RustStd.Io (allocCallPreserved_of_seg allocCallPreserved_trans)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoResolve_eq_base cliIoReadFile_lookup
  sepWP_seg_cliIo_block_pure
  cliIoReadFileSym cliIoOpenSym cliIoErrnoLocationSym
  cliIoReadSym cliIoCloseSym cliIoMemcpySym cliIoFinishGrowSym
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  ExternPreservesOracleSymtab cliIo_sepWP_carry_oracle_symtab
  poolPreserved_of_syscall poolPreserved_of_stdState
  cliIoFileCap cliIoReadCaps
  allocSeqPool_cliIoReadCaps_zero
  wantBytes
  cliIoSavedRegs12 ioVecBuf_zero_intro vecHeader_to_err_sret
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslClose48LocalSpec muslReadDir32Spec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  OpenRdonlyDetResult classifyOpenRdonly
  classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec
  setFd_none_setFd_of_fds_none muslOpenRdonlyDetSpec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (muslReadFileOrStdio32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.FinishGrow (cliIoFinishGrow_ok_withCodeLoaded)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_errno1_pc cliIoReadFile_errno2_pc
  readReg32_of_readReg64_eq cliIoReadFile_ret_epilogue
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir (
  muslErrnoAddr_eq_stdErrnoAddr cliIoReadFile_dir_loop
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileLoop (
  cliIoFileLoopResult cliIoFileOom cliIoReadFile_file_loop
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof (CliIoCallPreserved)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps (
  toList_cPathOf_length mem_toList_cPathOf_lt_256
  cstrBytes_cPathOf_length fdBytes_open_localFile
  cliIoReadFile_pre_open
)

/-- Descriptor installed by `open(cstr, O_CLOEXEC_W32)` at offset `0`. -/
abbrev cliIoOpenEntry (pathBytes : List (BitVec 8)) (kind : FdKind) : FdEntry :=
  { path := cPathOf pathBytes, accMode := .rdonly, append := false,
    cloexec := true, offset := 0, kind := kind }

/-- Spatial + `fs` postcondition of `signal_session_io::read_file`. -/
def cliIoReadFileResult {oom : State → State → Prop} (A : RustStdAlloc oom)
    (sret : BitVec 64) (pathBytes : List (BitVec 8)) (lb lk : Nat) (s0 sf : State) : SepProp :=
  if 4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes then
    ⌜sf.fs = s0.fs⌝ ∗
      ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
      A.pool lb lk sf
  else
    match classifyOpenRdonly s0.fs (cPathOf pathBytes) with
    | .err 2 =>
      ⌜sf.fs = s0.fs⌝ ∗
        (∃∗ ptr : BitVec 64, ioResultVecOk A sret 0#64 ptr []) ∗
        A.pool lb lk sf
    | .ok _ .localFile =>
      cliIoFileLoopResult A sret (cliIoOpenEntry pathBytes .localFile) lb lk s0 sf
    | _ =>
      ⌜sf.fs = s0.fs⌝ ∗
        ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
        A.pool lb lk sf

/-- OOM postcondition of `signal_session_io::read_file` (reachable only on `.ok fd .localFile`). -/
def cliIoReadFileOom (oom : State → State → Prop) (pathBytes : List (BitVec 8))
    (s0 sf : State) : SepProp :=
  ⌜pathBytes.length < 4096 ∧ 0#8 ∉ pathBytes ∧
    ∃ fd, classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd .localFile ∧
      ∃ k sm, k ≤ min ((s0.fs.fdBytes (cliIoOpenEntry pathBytes .localFile)).drop 0).length cliIoFileCap ∧
        VerifiedLibraries.RustStd.IoFrame s0 sm ∧
        sm.fs = s0.fs.setFd fd (some { cliIoOpenEntry pathBytes .localFile with offset := k }) ∧
        oom sm sf⌝

/-- Permission-parametric Hoare contract for `signal_session_io::read_file(path: &str)`
    (`ro = false` for read-write `↦ₛ`, `ro = true` for read-only `↦ᵣ`).
    Ghost argument: `(sret, pathPtr, pathBytes, lb, lk)`. -/
def cliIoReadFileGenSpec (ro : Bool) {oom : State → State → Prop} (A : RustStdAlloc oom)
    (stackBytes : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (sret, pathPtr, pathBytes, lb, lk) s0 =>
    ⌜8432 + Rust.hookStack ≤ stackBytes ∧
      stackBytes ≤ 2 ^ 64 ∧
      stackBytes ≤ s0.sp.toNat ∧
      s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s0.readReg64 .x0 = pathPtr ∧
      (s0.readReg64 .x1).toNat = pathBytes.length ∧
      s0.readReg64 .x8 = sret ∧
      (pathBytes.length < 4096 → 0#8 ∉ pathBytes →
        PathOk (cPathOf pathBytes) = true ∧
          ((pathComps (cPathOf pathBytes)).all fun c => decide (c.length ≤ NAME_MAX)) = true) ∧
      (∀ fd bs, pathBytes.length < 4096 → 0#8 ∉ pathBytes →
        classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd .localFile →
        s0.fs.files (cPathOf pathBytes) = some (.file bs) →
        AllocSeqFits A 1 lb lk (cliIoReadCaps 9 bs.length))⌝ ∗
    (stackAt s0.sp stackBytes ∗
      memcpySrc ro pathPtr pathBytes ∗
      memRegion sret 24 ∗
      StdErrnoCell s0.tpidrEl0 ∗
      A.pool lb lk s0)
  post := fun (sret, pathPtr, pathBytes, lb, lk) s0 sf =>
    ⌜CliIoCallPreserved s0 sf⌝ ∗
      (stackAt s0.sp stackBytes ∗
        memcpySrc ro pathPtr pathBytes ∗
        cliIoReadFileResult A sret pathBytes lb lk s0 sf ∗
        StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, _, pathBytes, _, _) s0 sf => cliIoReadFileOom oom pathBytes s0 sf

/-- Read-write (`↦ₛ`) specialization of `cliIoReadFileGenSpec`. -/
abbrev cliIoReadFileSpec {oom : State → State → Prop} (A : RustStdAlloc oom) (stackBytes : Nat) :=
  cliIoReadFileGenSpec false A stackBytes

/-- Read-only (`↦ᵣ`) specialization of `cliIoReadFileGenSpec`. -/
abbrev cliIoReadFileRoSpec {oom : State → State → Prop} (A : RustStdAlloc oom) (stackBytes : Nat) :=
  cliIoReadFileGenSpec true A stackBytes

section
arm64_proof_prelude

private theorem sepWP_frame_right {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P (fun sf Pf => post sf (Pf ∗ F)) oom) :
    SepWP prog target_pc s (P ∗ F) post oom := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_mono (h (F ∗ R) hm) ?_ (fun _ _ ho => Satisfies.drop_mid ho)
  rintro sf _ _ ⟨Pf, hmf, hpost⟩
  exact ⟨Pf ∗ F, by rw [sepConj_assoc]; exact hmf, hpost⟩

private theorem sepWP_mono_oom {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom1 oom2 : State → SepProp}
    (hoom : ∀ sf, oom1 sf ⊢ oom2 sf)
    (h : SepWP prog target_pc s P post oom1) :
    SepWP prog target_pc s P post oom2 := by
  unfold SepWP at h ⊢
  intro R hm
  exact reaches_pc_mono (h R hm) (fun _ _ _ hp => hp)
    (fun sf _ ho => Satisfies.mono (sepConj_mono_left (hoom sf)) ho)

private theorem getLsbD_31_of_readReg32_eq {s : State} {r : Reg} {w : BitVec 32}
    (h : s.readReg32 r = w) :
    (s.readReg64 r).getLsbD 31 = w.getLsbD 31 := by
  have ht : (s.readReg64 r).truncate 32 = w := h
  rw [← ht]
  simp

private theorem getLsbD_31_of_fd_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  have hlt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd (by decide)
  have htr : (fd.truncate 32).toNat = fd.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt32]
  have hd : fd.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt hfd
  simp only [BitVec.getLsbD, htr, Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem readReg32_zeroExtend_of_truncate {w : BitVec 32} {fd : BitVec 64}
    (hw : w = fd.truncate 32) (hfd : fd.toNat < 2 ^ 32) :
    w.zeroExtend 64 = fd := by
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hfd, Nat.mod_eq_of_lt (Nat.lt_trans hfd (by decide))]

private theorem calleeSaved_x24 {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 24#5) = s1.readReg64 (.gpr 24#5) :=
  h.2.2.2.2.2.1

private theorem calleeSaved_fp {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 (.gpr 29#5) = s1.readReg64 (.gpr 29#5) :=
  h.2.2.2.2.2.2.2.2.2.2.1

private theorem calleeSaved_vregs {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    calleeSavedVRegs s2 = calleeSavedVRegs s1 :=
  h.2.2.2.2.2.2.2.2.2.2.2

private theorem refold_cstr_buf4096 (base : BitVec 64) (pathBytes : List (BitVec 8))
    (hlt : pathBytes.length < 4096) :
    (base ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
      memRegion (base + BitVec.ofNat 64 (pathBytes.length + 1)) (4095 - pathBytes.length) ⊢
      memRegion base 4096 := by
  have hlen := cstrBytes_cPathOf_length pathBytes
  have hsub : 4096 - (cstrBytes (cPathOf pathBytes)).length = 4095 - pathBytes.length := by
    rw [hlen]; omega
  rw [← hlen, ← hsub]
  exact pointsToBytes_memRegion_entails base (cstrBytes (cPathOf pathBytes)) 4096
    (by rw [hlen]; omega) (by decide)

private theorem ioResultVecOk_empty_intro {oom : State → State → Prop} (A : RustStdAlloc oom)
    (sret : BitVec 64) :
    (sret ↦₆₄ 0#64) ∗ ((sret + 8#64) ↦₆₄ 1#64) ∗ ((sret + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptr : BitVec 64, ioResultVecOk A sret 0#64 ptr [] := by
  refine Entails.sepExists_right 1#64 ?_
  dsimp only [ioResultVecOk]
  have hvec0 : emp ⊢ ioVecBuf A 0#64 1#64 [] := ioVecBuf_zero_intro A (ptr := 1#64) (by decide)
  have hhdr :
      (sret ↦₆₄ 0#64) ∗ ((sret + 8#64) ↦₆₄ 1#64) ∗ ((sret + 16#64) ↦₆₄ 0#64) ⊢
        vecHeader sret 0#64 1#64 0#64 := Entails.refl _
  exact Entails.trans (by rw [sepConj_emp]; exact Entails.refl _) (sepConj_mono hhdr hvec0)

/-- Post-`open` `.err errno` branch (`+0x88 .. +0xb8` / `+0x200 .. +0x208`):
    checks `errno ≠ 4` (`EINTR`), checks `errno == 2` (`ENOENT` → `Ok([])` vs `Err(())`),
    and runs the shared return epilogue. -/
private theorem cliIoReadFile_open_err [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    {s0 so : State} {sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {errno stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) (hsp0 : s0.spAligned = true)
    (herr_cases : errno = 2 ∨ errno = 20 ∨ errno = 24)
    (hcl_o : signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = 0xffffffff#32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs) (htr_o : so.trace = s0.trace)
    (hsig_o : so.sigActions = s0.sigActions) (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          ((if errno = 2 then
              (∃∗ ptr : BitVec 64, ioResultVecOk A sret 0#64 ptr [])
            else
              (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
            StdErrnoCell s0.tpidrEl0) ∗
          A.pool lb lk sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ A.pool lb lk so)
      post oomProp := by
  let ev := BitVec.ofNat 32 errno
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = true := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]; decide
  wp_sym_steps
  refine SepWP.done cliIoReadFile_errno1_pc (by simpa [arm64_norm] using hrun_o')
    fun sm1 hcpu_10 hcl_1 hnsp_1 hsym_1 => ?_
  have hcpu_1 := hcpu_10.1
  have ⟨hacp_o1, hpool_o1⟩ :=
    allocCallPreserved_of_seg hcpu_o0 hcpu_10 hnsp_1 hsym_1
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_o1 : A.pool lb lk so = A.pool lb lk sm1 :=
    (A.pool_transport _ _ so sm1 hpool_o1).symm
  have hpc_1 : sm1.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
    hcpu_1.pc_eq.trans cliIoReadFile_errno1_pc
  have hrun_1 : sm1.status = .Running := hcpu_1.status_eq.trans hrun_o'
  have hsp_1_eq : sm1.sp = s0.sp - 8320#64 :=
    hcpu_1.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hsp_1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_1_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_1 : sm1.readReg64 .lr = cliIoPl03.base + 144#64 := by
    rw [hcpu_1.readReg64 .lr]; simp [arm64_norm]
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_1.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have htp_1 : sm1.tpidrEl0 = s0.tpidrEl0 := hacp_o1.2.2.2.1.trans htp_o
  have hvregs_1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
    hcpu_1.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  let T_el1 : SepProp :=
    stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
      memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
      vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
      cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
      (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ A.pool lb lk sm1
  apply seqCodeLoaded hcl_1 (mid := cliIoPl03.base + 144#64)
  apply (SepWP.call_subroutine_frame herrno (F := T_el1) (x := ())
    hpc_1 hrun_1 hsp_1 hlr_1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslErrnoLocationSpec, T_el1]; rw [emp_sepConj]
    rw [hpool_eq_o1] at hm'
    exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
  · intro se1 hpc_se1 hrun_se1 hsp_se1 hcs_1
    refine SepWP.done hpc_se1 hrun_se1 fun hcl_se1 => ?_
    wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el1]
    apply SepWP.pure_elim; rintro ⟨hx0_se1, _, hstd_1⟩
    have hpool_eq_1 : A.pool lb lk sm1 = A.pool lb lk se1 :=
      (A.pool_transport _ _ sm1 se1 (poolPreserved_of_stdState hstd_1)).symm
    have hsp_se1_eq : se1.sp = s0.sp - 8320#64 := hsp_se1.trans hsp_1_eq
    have hx0_se1' : se1.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
      rw [hx0_se1, muslErrnoAddr_eq_stdErrnoAddr, htp_1]
    have hx24_se1 : se1.readReg64 (.gpr 24#5) = sret := (calleeSaved_x24 hcs_1).trans hx24_1
    have htp_se1 : se1.tpidrEl0 = s0.tpidrEl0 := hstd_1.2.2.1.trans htp_1
    have hvregs_se1 : calleeSavedVRegs se1 = calleeSavedVRegs s0 :=
      (calleeSaved_vregs hcs_1).trans hvregs_1
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se1
      (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
    intro se1' hcpu_e10; have hcpu_e1 := hcpu_e10.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_e1' : se1'.pc = cliIoPl03.base + 144#64 := hcpu_e1.pc_eq.trans hpc_se1
    have hrun_e1' : se1'.status = .Running := hcpu_e1.status_eq.trans hrun_se1
    have hsp_e1' : se1'.spAligned = true := by
      rw [hcpu_e1.spAligned]; simp only [State.spAligned]; rw [hsp_se1_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx0_e1' : se1'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
      (hcpu_e1.readReg64 _).trans hx0_se1'
    have hev_ne4 : (BitVec.setWidth 64 ev - 4#64 == 0#64) = false := by
      dsimp only [ev]; rcases herr_cases with rfl | rfl | rfl <;> decide
    wp_sym_steps
    refine SepWP.done cliIoReadFile_errno2_pc (by simpa [arm64_norm] using hrun_e1')
      fun sm2 hcpu_20 hcl_2 hnsp_2 hsym_2 => ?_
    have hcpu_2 := hcpu_20.1
    have ⟨hacp_12, hpool_12⟩ :=
      allocCallPreserved_of_seg hcpu_e10 hcpu_20 hnsp_2 hsym_2
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_12 : A.pool lb lk se1 = A.pool lb lk sm2 :=
      (A.pool_transport _ _ se1 sm2 hpool_12).symm
    have hpc_2 : sm2.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
      hcpu_2.pc_eq.trans cliIoReadFile_errno2_pc
    have hrun_2 : sm2.status = .Running := hcpu_2.status_eq.trans hrun_e1'
    have hsp_2_eq : sm2.sp = s0.sp - 8320#64 :=
      hcpu_2.sp_eq.trans ((by simp [arm64_norm] : _ = se1'.sp).trans (hcpu_e1.sp_eq.trans hsp_se1_eq))
    have hsp_2 : sm2.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_2_eq]; exact s0.spAligned_sub 8320#64 hsp0
    have hlr_2 : sm2.readReg64 .lr = cliIoPl03.base + 160#64 := by
      rw [hcpu_2.readReg64 .lr]; simp [arm64_norm]
    have hx24_2 : sm2.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_2.readReg64]; simp only [arm64_norm]; exact (hcpu_e1.readReg64 _).trans hx24_se1
    have htp_2 : sm2.tpidrEl0 = s0.tpidrEl0 := hacp_12.2.2.2.1.trans htp_se1
    have hvregs_2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 :=
      hcpu_2.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se1').trans
        (hcpu_e1.calleeSavedVRegs.trans hvregs_se1))
    let T_el2 : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ∗ A.pool lb lk sm2
    apply seqCodeLoaded hcl_2 (mid := cliIoPl03.base + 160#64)
    apply (SepWP.call_subroutine_frame herrno (F := T_el2) (x := ())
      hpc_2 hrun_2 hsp_2 hlr_2
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslErrnoLocationSpec, T_el2]; rw [emp_sepConj]
      rw [hpool_eq_1, hpool_eq_12] at hm'
      exact Satisfies.mono (by dsimp only [ev]; sep_frame) hm'
    · intro se2 hpc_se2 hrun_se2 hsp_se2 hcs_2
      refine SepWP.done hpc_se2 hrun_se2 fun hcl_se2 => ?_
      wp_conv_pre =>
        dsimp only [muslErrnoLocationSpec, T_el2]
        rw [show vecHeader sret v0 v1 v2 =
          (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
        simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_se2, _, hstd_2⟩
      have hpool_eq_2 : A.pool lb lk sm2 = A.pool lb lk se2 :=
        (A.pool_transport _ _ sm2 se2 (poolPreserved_of_stdState hstd_2)).symm
      have hsp_se2_eq : se2.sp = s0.sp - 8320#64 := hsp_se2.trans hsp_2_eq
      have hx0_se2' : se2.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
        rw [hx0_se2, muslErrnoAddr_eq_stdErrnoAddr, htp_2]
      have hx24_se2 : se2.readReg64 (.gpr 24#5) = sret := hcs_2.2.2.2.2.2.1.trans hx24_2
      have htp_se2 : se2.tpidrEl0 = s0.tpidrEl0 := hstd_2.2.2.1.trans htp_2
      have hvregs_se2 : calleeSavedVRegs se2 = calleeSavedVRegs s0 :=
        (calleeSaved_vregs hcs_2).trans hvregs_2
      have hfs_se2 : se2.fs = s0.fs :=
        hstd_2.1.trans (hacp_12.1.trans (hstd_1.1.trans (hacp_o1.1.trans hfs_o)))
      have htr_se2 : se2.trace = s0.trace :=
        hstd_2.2.1.trans (hacp_12.2.1.trans (hstd_1.2.1.trans (hacp_o1.2.1.trans htr_o)))
      have hsig_se2 : se2.sigActions = s0.sigActions :=
        hstd_2.2.2.2.1.trans (hacp_12.2.2.1.trans (hstd_1.2.2.2.1.trans (hacp_o1.2.2.1.trans hsig_o)))
      have hbs_se2 : se2.brkStart = s0.brkStart :=
        hstd_2.2.2.2.2.2.1.trans (hacp_12.2.2.2.2.1.trans (hstd_1.2.2.2.2.2.1.trans (hacp_o1.2.2.2.2.1.trans hbs_o)))
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_se2
        (mid := cliIoPl03.base + 520#64)
      intro se2' hcpu_e20; have hcpu_e2 := hcpu_e20.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_e2' : se2'.pc = cliIoPl03.base + 160#64 := hcpu_e2.pc_eq.trans hpc_se2
      have hrun_e2' : se2'.status = .Running := hcpu_e2.status_eq.trans hrun_se2
      have hsp_e2' : se2'.spAligned = true := by
        rw [hcpu_e2.spAligned]; simp only [State.spAligned]; rw [hsp_se2_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx0_e2' : se2'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
        (hcpu_e2.readReg64 _).trans hx0_se2'
      have hx24_e2' : se2'.readReg64 (.gpr 24#5) = sret :=
        (hcpu_e2.readReg64 _).trans hx24_se2
      by_cases he2 : errno = 2
      · subst he2
        dsimp only [ev]
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hpool_2r⟩ :=
          allocCallPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : A.pool lb lk se2 = A.pool lb lk se_ret :=
          (A.pool_transport _ _ se2 se_ret hpool_2r).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue A hext3 (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := (if (2 : Nat) = 2 then
                (∃∗ ptr : BitVec 64, ioResultVecOk A sret 0#64 ptr [])
              else
                (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
              StdErrnoCell s0.tpidrEl0)
            (lb_f := lb) (lk_f := lk)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf _ hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ 2#32) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right 2#32 (Entails.refl _)
        have hok_sret := ioResultVecOk_empty_intro A sret
        let KeepE2 : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ A.pool lb lk se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hok_sret (sepConj_mono_left (Q := KeepE2) hev_cell))
            (by dsimp only [KeepE2]; sep_entail))
        dsimp only [KeepE2]; sep_entail
      · have hev_ne2 : (BitVec.setWidth 64 ev - 2#64 == 0#64) = false := by
          dsimp only [ev]
          rcases herr_cases with rfl | rfl | rfl
          · exact absurd rfl he2
          · decide
          · decide
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e2')
          fun se_ret hcpu_r0 hcl_r hnsp_r hsym_r => ?_
        have hcpu_r := hcpu_r0.1
        have ⟨hacp_2r, hpool_2r⟩ :=
          allocCallPreserved_of_seg hcpu_e20 hcpu_r0 hnsp_r hsym_r
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_2r : A.pool lb lk se2 = A.pool lb lk se_ret :=
          (A.pool_transport _ _ se2 se_ret hpool_2r).symm
        have hsp_r_eq : se_ret.sp = s0.sp - 8320#64 :=
          hcpu_r.sp_eq.trans ((by simp [arm64_norm] : _ = se2'.sp).trans (hcpu_e2.sp_eq.trans hsp_se2_eq))
        have hvregs_r : calleeSavedVRegs se_ret = calleeSavedVRegs s0 :=
          hcpu_r.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se2').trans
            (hcpu_e2.calleeSavedVRegs.trans hvregs_se2))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue A hext3 (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := (if errno = 2 then
                (∃∗ ptr : BitVec 64, ioResultVecOk A sret 0#64 ptr [])
              else
                (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
              StdErrnoCell s0.tpidrEl0)
            (lb_f := lb) (lk_f := lk)
            hlo hhi hcl_r (hcpu_r.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_r.status_eq.trans hrun_e2') hsp0 hsp_r_eq hvregs_r
            fun sf hpc_f hrun_f hsp_f hcs_f _ hacp_rf _ hent =>
              hcont sf hpc_f hrun_f hsp_f hcs_f
                (hacp_rf.1.trans (hacp_2r.1.trans hfs_se2))
                (hacp_rf.2.1.trans (hacp_2r.2.1.trans htr_se2))
                (hacp_rf.2.2.1.trans (hacp_2r.2.2.1.trans hsig_se2))
                (hacp_rf.2.2.2.1.trans (hacp_2r.2.2.2.1.trans htp_se2))
                (hacp_rf.2.2.2.2.1.trans (hacp_2r.2.2.2.2.1.trans hbs_se2)) hent)
        simp only [he2, ↓reduceIte]; rw [hpool_eq_2, hpool_eq_2r]
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right ev (Entails.refl _)
        have herr_sret :
            (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) ⊢
              (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 :=
          vecHeader_to_err_sret sret v1 v2
        let KeepEn : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗ A.pool lb lk se_ret
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono herr_sret (sepConj_mono_left (Q := KeepEn) hev_cell))
            (by dsimp only [KeepEn]; sep_entail))
        dsimp only [KeepEn]; sep_entail

/-- Post-`open` `.ok fd kind` branch (`+0x88 → +0xbc .. +0xd8` + `.localDir` / `.localFile` loop). -/
private theorem cliIoReadFile_open_ok [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
      stdMemcpySpec)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 so : State} {fd sret v0 v1 v2 st0 st1 st2 st3 : BitVec 64}
    {ev0 : BitVec 32} {pathBytes : List (BitVec 8)} {kind : FdKind}
    {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop}
    (hlo : 8368 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hsp_lo : stackBytes ≤ s0.sp.toNat) (hsp_va : s0.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (hlt : pathBytes.length < 4096) (hnul : 0#8 ∉ pathBytes)
    (hcl_ok : classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd kind)
    (hfits : ∀ fd' bs, pathBytes.length < 4096 → 0#8 ∉ pathBytes →
      classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd' .localFile →
      s0.fs.files (cPathOf pathBytes) = some (.file bs) →
      AllocSeqFits A 1 lb lk (cliIoReadCaps 9 bs.length))
    (hcl_o : signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem)
    (hpc_o : so.pc = cliIoPl03.base + 136#64) (hrun_o : so.status = .Running)
    (hsp_o : so.sp = s0.sp - 8320#64)
    (hw0_o : so.readReg32 .x0 = fd.truncate 32)
    (hx24_o : so.readReg64 (.gpr 24#5) = sret)
    (hx29_o : so.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp_o : so.tpidrEl0 = s0.tpidrEl0)
    (hvregs_o : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_o : so.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)))
    (htr_o : so.trace = s0.trace) (hsig_o : so.sigActions = s0.sigActions)
    (hbs_o : so.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.trace = s0.trace → sf.sigActions = s0.sigActions →
      sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗
          cliIoReadFileResult A sret pathBytes lb lk s0 sf ∗
          StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk so)
      post (cliIoReadFileOom oom pathBytes s0) := by
  obtain ⟨_, _, _, hfd_max, hfds_none, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl_ok
  have hfd_lt31 : fd.toNat < 2 ^ 31 := Nat.lt_trans hfd_max (by decide)
  have hfd_lt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd_lt31 (by decide)
  have hnot_bad : ¬(4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes) := by
    rintro (hge | hm)
    · omega
    · exact hnul hm
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_o
    (mid := cliIoPl03.base + 216#64)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl03.base + 136#64 := hcpu_o.pc_eq.trans hpc_o
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_o
  have hsp_o' : so'.spAligned = true := by
    rw [hcpu_o.spAligned]; simp only [State.spAligned]; rw [hsp_o]
    exact s0.spAligned_sub 8320#64 hsp0
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = false := by
    rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_o]
    exact getLsbD_31_of_fd_lt hfd_lt31
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_o')
    fun sl hcpu_l0 hcl_l hnsp_l hsym_l => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨hacp_ol, hpool_ol⟩ :=
    allocCallPreserved_of_seg hcpu_o0 hcpu_l0 hnsp_l hsym_l
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ol : A.pool lb lk so = A.pool lb lk sl :=
    (A.pool_transport _ _ so sl hpool_ol).symm
  have hpc_l : sl.pc = cliIoPl03.base + 216#64 := hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl.status = .Running := hcpu_l.status_eq.trans hrun_o'
  have hsp_l : sl.sp = s0.sp - 8320#64 :=
    hcpu_l.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_o))
  have hw19_l : (sl.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    apply readReg32_zeroExtend_of_truncate ?_ hfd_lt32
    rw [readReg32_of_readReg64_eq (hcpu_l.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_o.readReg64 .x0]
    exact hw0_o
  have hx24_l : sl.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx24_o
  have hx29_l : sl.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_l.readReg64]; simp only [arm64_norm]; exact (hcpu_o.readReg64 _).trans hx29_o
  have hvregs_l : calleeSavedVRegs sl = calleeSavedVRegs s0 :=
    hcpu_l.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_o))
  have hfs_l : sl.fs = s0.fs.setFd fd (some (cliIoOpenEntry pathBytes kind)) :=
    hacp_ol.1.trans hfs_o
  have htr_l : sl.trace = s0.trace := hacp_ol.2.1.trans htr_o
  have hsig_l : sl.sigActions = s0.sigActions := hacp_ol.2.2.1.trans hsig_o
  have htp_l : sl.tpidrEl0 = s0.tpidrEl0 := hacp_ol.2.2.2.1.trans htp_o
  have hbs_l : sl.brkStart = s0.brkStart := hacp_ol.2.2.2.2.1.trans hbs_o
  have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
    Entails.sepExists_right ev0 (Entails.refl _)
  rcases hkind_cases with ⟨rfl, _⟩ | ⟨rfl, bs, hbs_file⟩
  · have hfds_l : sl.fs.fds fd = some (cliIoOpenEntry pathBytes .localDir) := by
      rw [hfs_l]; simp [FsState.setFd]
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_dir_loop A hext3 hread_dir herrno hclose
        (lb := lb) (lk := lk)
        (count := 4096#64) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (by omega) hhi hfd_lt31 hfds_l rfl rfl
        hcl_l hpc_l hrun_l hsp0 hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx24_l htp_l hvregs_l
        fun sf hpc_f hrun_f hsp_f hcs_f _ hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent => ?_)
    · rw [hpool_eq_ol]
      let KeepDir : SepProp :=
        stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk sl
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepDir) hev_cell)
          (by dsimp only [KeepDir]; sep_entail))
      dsimp only [KeepDir]; sep_entail
    · have hfs_f' : sf.fs = s0.fs := by
        rw [hfs_f, hfs_l]; exact setFd_none_setFd_of_fds_none hfds_none
      refine hcont sf hpc_f hrun_f hsp_f hcs_f
        (htr_f.trans htr_l) (hsig_f.trans hsig_l) (htp_f.trans htp_l) (hbs_f.trans hbs_l) ?_
      refine Entails.trans hent ?_
      simp only [cliIoReadFileResult, hnot_bad, ↓reduceIte, hcl_ok]
      rw [pure_sepConj_of_true hfs_f']
      sep_entail
  · let d0 := cliIoOpenEntry pathBytes .localFile
    have hrem_bs : (s0.fs.fdBytes d0).drop d0.offset = bs := by
      dsimp only [d0, cliIoOpenEntry]; rw [fdBytes_open_localFile hbs_file]; rfl
    have hfits_d0 : AllocSeqFits A 1 lb lk (cliIoReadCaps 9 ((s0.fs.fdBytes d0).drop d0.offset).length) := by
      rw [hrem_bs]; exact hfits fd bs hlt hnul hcl_ok hbs_file
    have hpool0 : allocSeqPool A 1 lb lk (cliIoReadCaps 9 0) = (lb, lk) :=
      allocSeqPool_cliIoReadCaps_zero A 9 lb lk
    apply sepWP_mono_oom (oom1 := cliIoFileOom oom fd d0 s0)
      (fun sf => by
        dsimp only [cliIoFileOom, cliIoReadFileOom]
        exact Entails.pure_mono fun ⟨k, sm_o, hk, hfr, hfs_sm, hoom_sm⟩ =>
          ⟨hlt, hnul, fd, hcl_ok, k, sm_o, hk, hfr,
            by simpa only [d0, cliIoOpenEntry, Nat.zero_add] using hfs_sm, hoom_sm⟩)
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_file_loop A hext3 hread_file hmemcpy hfg hdealloc hclose
        (d0 := d0) (fd := fd) (sret := sret) (v0 := v0) (v1 := v1) (v2 := v2)
        hlo hhi hsp_lo hsp_va hsp0 hfd_lt31 hfds_none rfl rfl rfl hfits_d0
        (fun sf hpc_f hrun_f hsp_f hcs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent =>
          hcont sf hpc_f hrun_f hsp_f hcs_f htr_f hsig_f htp_f hbs_f
            (by simpa only [cliIoReadFileResult, hnot_bad, ↓reduceIte, hcl_ok] using hent))
        (cliIoFileCap + 1) sl 1#64 st0 st1 st2 st3 0 0 lb lk
        (Nat.le_refl _) (Nat.zero_le _) (fun _ => Nat.dvd_zero 4096) rfl
        (by rw [hpool0]) (by rw [hpool0])
        hcl_l hpc_l hrun_l hsp_l hw19_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm, wantBytes])
        hx24_l
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        (by rw [hcpu_l.readReg64]; simp [arm64_norm])
        hx29_l hvregs_l
        (by simpa only [d0, cliIoOpenEntry, Nat.zero_add] using hfs_l)
        htr_l hsig_l htp_l hbs_l)
    rw [hpool_eq_ol]
    have hvec0 : emp ⊢ ioVecBuf A (BitVec.ofNat 64 0) 1#64 (((s0.fs.fdBytes d0).drop d0.offset).take 0) :=
      ioVecBuf_zero_intro A (ptr := 1#64) (by decide)
    let KeepFile : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        memRegion (s0.sp - 8320#64) 4096 ∗ memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk sl
    have hwith_vec :
        KeepFile ⊢ KeepFile ∗
          ioVecBuf A (BitVec.ofNat 64 0) 1#64 (((s0.fs.fdBytes d0).drop d0.offset).take 0) := by
      simpa only [sepConj_emp] using sepConj_mono_right (P := KeepFile) hvec0
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hwith_vec hev_cell)
        (by dsimp only [KeepFile]; sep_entail))
    dsimp only [KeepFile]; sep_entail

/-- Placement-generic, permission-parametric proof of `signal_session_io::read_file` (`block[3]`). -/
theorem cliIoReadFileGen_ok (ro : Bool) {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustStdReallocSpec A))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoReadFileGenSpec ro A stackBytes)) := by
  have hfg := cliIoFinishGrow_ok_withCodeLoaded A hpl hext4 hshim halloc hrealloc
  let _ : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 3 cliIoReadFileSym cliIo3_lt cliIoReadFile_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨sret, pathPtr, pathBytes, lb, lk⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx0, hx1, hx8, hpathOk, hfits⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  apply cliIo_sepWP_carry_oracle_symtab hsvc hext_os
  refine SepWP.weaken_pre (Entails.refl _)
    (cliIoReadFile_pre_open A hext3 (by omega) hhi hcl0 hpc hrun hsp0 hx0 hx1 hx8
      (fun hbad sf _hpc_f _hrun_f hsp_f hcs_f _hcl_f hacp_0f {_Pre_f} hent horc_f hsym_f => ?_)
      (fun hlt hnul sm ev0 v0 v1 v2 st0 st1 st2 st3
          hcl_m hpc_m hrun_m hsp_m_eq hsp_m hlr_m hx0_m hw1_m hx24_m hx29_m hvregs_m hacp_0m => ?_))
  · have hpres : CliIoCallPreserved s0 sf :=
      ⟨hacp_0f.2.1, hacp_0f.2.2.1, hacp_0f.2.2.2.1, hacp_0f.2.2.2.2.1, horc_f, hsym_f⟩
    refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
    rw [pure_sepConj_of_true hpres]
    refine Satisfies.mono (sepConj_mono_left (Entails.trans hent ?_)) hm_out
    simp only [cliIoReadFileResult, hbad, ↓reduceIte]
    rw [pure_sepConj_of_true hacp_0f.1]
    sep_entail
  · have h112_le : 112 ≤ stackBytes - 8320 := by omega
    have hsb_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
    have hnot_bad : ¬(4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes) := by
      rintro (hge | hm)
      · omega
      · exact hnul hm
    let PreOpenRest : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
        memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
          (4095 - pathBytes.length) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
        ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗
        vecHeader sret v0 v1 v2 ∗
        (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
        A.pool lb lk sm
    refine SepWP.weaken_pre
      (P' := PreOpenRest ∗ memcpySrc ro pathPtr pathBytes)
      (by dsimp only [PreOpenRest]; sep_entail) ?_
    apply sepWP_frame_right
    dsimp only [PreOpenRest]
    wp_conv_pre =>
      rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 112 h112_le hsb_hi]
      simp only [sepConj_assoc]
    have hpath_len : (cPathOf pathBytes).toList.length < PATH_MAX := by
      rw [toList_cPathOf_length]; exact hlt
    have hpath_ascii : ∀ c ∈ (cPathOf pathBytes).toList, c.toNat < 256 :=
      fun _ hc => mem_toList_cPathOf_lt_256 hc
    let T_open : SepProp :=
      memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320)) (stackBytes - 8320 - 112) ∗
        memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
          (4095 - pathBytes.length) ∗
        memRegion (s0.sp - 4224#64) 4096 ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ A.pool lb lk sm
    apply seqCodeLoaded hcl_m (mid := cliIoPl03.base + 136#64)
    apply (SepWP.call_subroutine_frame hopen (F := T_open)
      (x := (s0.sp - 8320#64, cPathOf pathBytes, ev0))
      hpc_m hrun_m hsp_m hlr_m
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [muslOpenRdonlyDetSpec, T_open]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_m, hw1_m, (hpathOk hlt hnul).1, (hpathOk hlt hnul).2, hpath_len, hpath_ascii⟩, ?_⟩
      rw [hsp_m_eq, muslErrnoAddr_eq_stdErrnoAddr, hacp_0m.2.2.2.1]
      exact Satisfies.mono (by sep_frame) hm'
    · intro so hpc_so hrun_so hsp_so hcs_mo
      refine SepWP.done hpc_so hrun_so fun hcl_so => ?_
      have hsp_so_eq : so.sp = s0.sp - 8320#64 := hsp_so.trans hsp_m_eq
      have hx24_so : so.readReg64 (.gpr 24#5) = sret := (calleeSaved_x24 hcs_mo).trans hx24_m
      have hx29_so : so.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        (calleeSaved_fp hcs_mo).trans hx29_m
      have hvregs_so : calleeSavedVRegs so = calleeSavedVRegs s0 :=
        (calleeSaved_vregs hcs_mo).trans hvregs_m
      have hstk_back :
          stackAt sm.sp 112 ∗
            memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
              (stackBytes - 8320 - 112) ⊢
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) := by
        rw [hsp_m_eq, stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) 112 h112_le hsb_hi]
        sep_entail
      have hcstr_back := refold_cstr_buf4096 (s0.sp - 8320#64) pathBytes hlt
      wp_conv_pre => dsimp only [muslOpenRdonlyDetSpec, T_open]
      rw [hacp_0m.1]
      cases hcl_res : classifyOpenRdonly s0.fs (cPathOf pathBytes) with
      | err errno =>
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
        have hpool_eq_mo : A.pool lb lk sm = A.pool lb lk so :=
          (A.pool_transport _ _ sm so (poolPreserved_of_syscall hsys_so)).symm
        have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_open_err A hext3 herrno
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (lb := lb) (lk := lk)
            (by omega) hhi hsp0
            (classifyOpenRdonly_err_cases hcl_res)
            hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so htp_so hvregs_so
            hfs_so (htr_so.trans hacp_0m.2.1)
            (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
            fun sf _hpc_f _hrun_f hsp_f hcs_f hfs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
                horc_f hsym_f => ?_)
        · rw [hpool_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
          let KeepErr0 : SepProp :=
            memRegion (s0.sp - 4224#64) 4096 ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              (stdErrnoAddr s0.tpidrEl0 ↦₃₂ BitVec.ofNat 32 errno) ∗ A.pool lb lk so
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepErr0) hcstr_back))
              (by dsimp only [KeepErr0]; sep_entail))
          dsimp only [KeepErr0]; sep_entail
        · have hpres : CliIoCallPreserved s0 sf := ⟨htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
          refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
          rw [pure_sepConj_of_true hpres]
          refine Satisfies.mono (sepConj_mono_left ?_) hm_out
          have hent' : _Pre_f ⊢
              stackAt s0.sp stackBytes ∗
                cliIoReadFileResult A sret pathBytes lb lk s0 sf ∗
                StdErrnoCell s0.tpidrEl0 := by
            refine Entails.trans hent ?_
            by_cases he2 : errno = 2
            · subst he2
              simp only [cliIoReadFileResult, hnot_bad, ↓reduceIte, hcl_res]
              rw [pure_sepConj_of_true hfs_f]
              sep_entail
            · have hres_err : cliIoReadFileResult A sret pathBytes lb lk s0 sf =
                  ⌜sf.fs = s0.fs⌝ ∗
                    ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
                    A.pool lb lk sf := by
                rcases classifyOpenRdonly_err_cases hcl_res with rfl | rfl | rfl
                · exact absurd rfl he2
                · simp [cliIoReadFileResult, hnot_bad, hcl_res]
                · simp [cliIoReadFileResult, hnot_bad, hcl_res]
              simp only [he2, ↓reduceIte, hres_err]
              rw [pure_sepConj_of_true hfs_f]
              sep_entail
          exact Entails.trans (sepConj_mono_left hent') (by sep_entail)
      | ok fd kind =>
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hw0_so, hfs_so, htr_so, hsys_so⟩
        have hpool_eq_mo : A.pool lb lk sm = A.pool lb lk so :=
          (A.pool_transport _ _ sm so (poolPreserved_of_syscall hsys_so)).symm
        have htp_so : so.tpidrEl0 = s0.tpidrEl0 := hsys_so.1.trans hacp_0m.2.2.2.1
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_open_ok A hext3 herrno hread_dir hread_file hmemcpy hfg hdealloc hclose
            (v0 := v0) (v1 := v1) (v2 := v2)
            (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3) (ev0 := ev0)
            (by omega) hhi hsp_lo hsp_va hsp0 hlt hnul hcl_res hfits
            hcl_so hpc_so hrun_so hsp_so_eq hw0_so hx24_so hx29_so htp_so hvregs_so
            hfs_so (htr_so.trans hacp_0m.2.1)
            (hsys_so.2.1.trans hacp_0m.2.2.1) (hsys_so.2.2.brkStart_eq.trans hacp_0m.2.2.2.2.1)
            fun sf _hpc_f _hrun_f hsp_f hcs_f htr_f hsig_f htp_f hbs_f {_Pre_f} hent
                horc_f hsym_f => ?_)
        · rw [hpool_eq_mo, muslErrnoAddr_eq_stdErrnoAddr, htp_so]
          let KeepOkOpen : SepProp :=
            memRegion (s0.sp - 4224#64) 4096 ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
              (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk so
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hstk_back (sepConj_mono_left (Q := KeepOkOpen) hcstr_back))
              (by dsimp only [KeepOkOpen]; sep_entail))
          dsimp only [KeepOkOpen]; sep_entail
        · have hpres : CliIoCallPreserved s0 sf := ⟨htr_f, hsig_f, htp_f, hbs_f, horc_f, hsym_f⟩
          refine ⟨fun hm_out => ?_, hsp_f, hcs_f⟩
          rw [pure_sepConj_of_true hpres]
          refine Satisfies.mono (sepConj_mono_left ?_) hm_out
          exact Entails.trans (sepConj_mono_left hent) (by sep_entail)

/-- Read-write (`↦ₛ`) specialization of `cliIoReadFileGen_ok`. -/
theorem cliIoReadFile_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustStdReallocSpec A))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoReadFileSpec A stackBytes)) :=
  cliIoReadFileGen_ok false A hpl hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc

/-- Read-only (`↦ᵣ`) specialization of `cliIoReadFileGen_ok`. -/
theorem cliIoReadFileRo_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustStdReallocSpec A))
    (hdealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym)
      (rustStdDeallocSpec A)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoReadFileRoSpec A stackBytes)) :=
  cliIoReadFileGen_ok true A hpl hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim halloc hrealloc hdealloc

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof
