/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import ProofLib.SepLogic.WP.Syscalls
public import ProofLib.SepLogic.WPFrozen

/-!
# Placement-Generic `read`, `write`, and `Stderr::write_all` Contracts

Proves placement-generic `subroutine_ok` and framed `SepWP` call contracts over `C : HbCliLayout`
for the `musl` `read` and `write` syscall wrappers and Rust `<Stderr as std::io::Write>::write_all`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## `STDIN` descriptor invariant (`HbStdinOpen`) and non-VM heap transport -/

/-- Descriptor `0` (`STDIN_FILENO`) is open for `.stdio` reading in `fs` with remaining unread
    input byte stream `rem`. -/
def HbStdinOpen (rem : List (BitVec 8)) (fs : FsState) : Prop :=
  ∃ desc : FdEntry,
    fs.fds 0#64 = some desc ∧
    desc.kind = .stdio ∧
    desc.accMode.canRead = true ∧
    (fs.fdBytes desc).drop desc.offset = rem

theorem hbStdinOpen_initFsState (inputs : ProcessInputs) :
    HbStdinOpen inputs.stdin (initFsState inputs) :=
  ⟨{ path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio },
   rfl, rfl, rfl, rfl⟩

theorem HbStdinOpen.of_fs_eq {rem : List (BitVec 8)} {fs1 fs2 : FsState}
    (h : fs2 = fs1) (ho : HbStdinOpen rem fs1) : HbStdinOpen rem fs2 :=
  h ▸ ho

/-- Non-allocator machine-state preservation across CPU helpers and non-VM syscalls (`read`,
    `write`): preserves `tpidrEl0`, `sigActions`, `VmFieldsPreserved` (`brk`, `brkStart`,
    `physMemAvail`, `mem.perm`), and `KeepsFrozen`, transporting `M.Heap` directly via
    `M.heap_transport`. -/
structure HbNonVmPreserved (s0 sf : State) : Prop where
  tpidrEl0_eq   : sf.tpidrEl0 = s0.tpidrEl0
  sigActions_eq : sf.sigActions = s0.sigActions
  vm            : VmFieldsPreserved s0 sf
  keepsFrozen   : s0.mem.KeepsFrozen sf.mem

theorem HbNonVmPreserved.refl (s : State) : HbNonVmPreserved s s :=
  ⟨rfl, rfl, VmFieldsPreserved.refl s, Memory.KeepsFrozen.refl s.mem⟩

theorem HbNonVmPreserved.trans {s0 s1 s2 : State}
    (h01 : HbNonVmPreserved s0 s1) (h12 : HbNonVmPreserved s1 s2) :
    HbNonVmPreserved s0 s2 :=
  ⟨h12.tpidrEl0_eq.trans h01.tpidrEl0_eq,
   h12.sigActions_eq.trans h01.sigActions_eq,
   h01.vm.trans h12.vm,
   Memory.KeepsFrozen.trans h01.keepsFrozen h12.keepsFrozen⟩

theorem HbNonVmPreserved.heap_transport {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s0 sf : State}
    (h : HbNonVmPreserved s0 sf) :
    M.Heap γ lc blk s0 ⊢ M.Heap γ lc blk sf :=
  M.heap_transport h.vm.brk_eq h.vm.brkStart_eq h.vm.physMemAvail_eq h.vm.perm_eq

/-! ## Code bundle (`HbSyscallsAndStderrCode`) and `WordTree` validator -/

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))

def sccpWords : List (BitVec 32) :=
  [0xaa0003e8#32, 0xaa0103e0#32, 0xaa0203e1#32, 0xaa0303e2#32,
   0xaa0403e3#32, 0xaa0503e4#32, 0xaa0603e5#32, 0xd4000001#32,
   0xd65f03c0#32]

def syscallRetFastWords : List (BitVec 32) :=
  [0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32,
   0xaa0003f3#32, 0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32,
   0xd65f03c0#32]

def muslReadEntryWords : List (BitVec 32) :=
  [0xa9bf7bfd#32, 0xaa0103e4#32, 0xaa0203e3#32, 0x910003fd#32,
   0x93407c01#32, 0xaa0403e2#32, 0xd2800006#32, 0xd2800005#32,
   0xd2800004#32, 0xd28007e0#32]

def muslWriteEntryWords : List (BitVec 32) :=
  [0xa9bf7bfd#32, 0xaa0103e4#32, 0xaa0203e3#32, 0x910003fd#32,
   0x93407c01#32, 0xaa0403e2#32, 0xd2800006#32, 0xd2800005#32,
   0xd2800004#32, 0xd2800800#32]

def hbSyscallIoChunks (C : HbCliLayout) : List CodeChunk :=
  [ .words C.std.sccpAddr sccpWords,
    .instrs0 C.std.syscallCpAddr [iB C.std.syscallCpAddr C.std.sccpAddr],
    .words C.std.syscallRetAddr syscallRetFastWords,
    .words C.readAddr muslReadEntryWords,
    .instrs C.readAddr 0x28 [iBl (C.readAddr + 0x28#64) C.std.syscallCpAddr],
    .words (C.readAddr + 0x2c#64) [0xa8c17bfd#32],
    .instrs C.readAddr 0x30 [iB (C.readAddr + 0x30#64) C.std.syscallRetAddr],
    .words C.writeAddr muslWriteEntryWords,
    .instrs C.writeAddr 0x28 [iBl (C.writeAddr + 0x28#64) C.std.syscallCpAddr],
    .words (C.writeAddr + 0x2c#64) [0xa8c17bfd#32],
    .instrs C.writeAddr 0x30 [iB (C.writeAddr + 0x30#64) C.std.syscallRetAddr] ]

def hbStderrWriteAllChunks (C : HbCliLayout) : List CodeChunk :=
  let w := C.stderrWriteAllAddr
  let r := C.refStderrWriteAllAddr
  let u := C.unixStderrWriteAllAddr
  let ctr := C.std.threadIdCounterAddr
  [ .words w
      [0xd10083ff#32, 0xa9017bfd#32, 0x910043fd#32, 0xf90007e0#32, 0x910023e0#32],
    .instrs w 0x14 [iBl (w + 0x14#64) r],
    .words (w + 0x18#64)
      [0xa9417bfd#32, 0x910083ff#32, 0xd65f03c0#32],
    .words r
      [0xa9bb7bfd#32, 0xa90167fa#32, 0xa9025ff8#32, 0xa90357f6#32,
       0xa9044ff4#32, 0x910003fd#32, 0xf9400008#32, 0xaa0203f4#32,
       0xaa0103f5#32, 0xf9400113#32, 0xd2a00000#32, 0xf2800b00#32,
       0xd503201f#32, 0xd503201f#32, 0xd53bd05a#32, 0xf8606b59#32,
       0xb4000159#32, 0xf9400268#32, 0xeb08033f#32, 0x54000341#32],
    .instrs r 0x68 [iAdrp .x8 (r + 0x68#64) ctr],
    .words (r + 0x6c#64) [0xaa0003f6#32],
    .instrs r 0x70
      [iAdrp .x23 (r + 0x70#64) ctr,
       iAddLo12 .x23 .x23 ctr,
       iLdr64Lo12 .x24 .x8 ctr],
    .words (r + 0x7c#64)
      [0xb100071f#32, 0x540008e0#32, 0x91000701#32, 0xaa1803e0#32,
       0xaa1703e2#32, 0x91000719#32],
    .instrs r 0x94 [iBl (r + 0x94#64) C.std.cas8RelaxAddr],
    .words (r + 0x98#64)
      [0xeb18001f#32, 0xaa0003f8#32, 0x54fffee1#32, 0xf8366b59#32,
       0xf9400268#32, 0xeb08033f#32, 0x54fffd00#32, 0x91002262#32,
       0x2a1f03e0#32, 0x52800021#32, 0x52800036#32],
    .instrs r 0xc4 [iBl (r + 0xc4#64) C.std.cas4AcqAddr],
    .words (r + 0xc8#64)
      [0x7100001f#32, 0x540007e1#32, 0xf9000279#32, 0xb9000e76#32,
       0xf9400a68#32, 0xb5000628#32, 0x92800008#32, 0xf9000a68#32,
       0xaa1503e1#32, 0xaa1403e2#32],
    .instrs r 0xf0 [iBl (r + 0xf0#64) u],
    .words (r + 0xf4#64) [0xb4000100#32],
    .words (r + 0x114#64)
      [0xf9400a68#32, 0xb9400e69#32, 0x91000508#32, 0x71000529#32,
       0xf9000a68#32, 0xb9000e69#32, 0x540000e0#32, 0xa9444ff4#32,
       0xa94357f6#32, 0xa9425ff8#32, 0xa94167fa#32, 0xa8c57bfd#32,
       0xd65f03c0#32, 0x91002261#32, 0xaa0003f4#32, 0x2a1f03e0#32,
       0xf900027f#32],
    .instrs r 0x158 [iBl (r + 0x158#64) C.std.swp4RelAddr],
    .words (r + 0x15c#64)
      [0x2a0003e8#32, 0xaa1403e0#32, 0x7100091f#32, 0x54fffe41#32],
    .words u
      [0xd101c3ff#32, 0xa9017bfd#32, 0xa9026ffc#32, 0xa90367fa#32,
       0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910043fd#32,
       0xb4000542#32],
    .instrs u 0x24 [iAdrp .x26 (u + 0x24#64) C.osFunctionsGotAddr],
    .words (u + 0x28#64) [0xaa0203f4#32, 0xaa0103f5#32],
    .instrs u 0x30 [iLdr64Lo12 .x26 .x26 C.osFunctionsGotAddr],
    .words (u + 0x34#64) [0x910003f8#32, 0xd503201f#32],
    .instrs u 0x3c [iAdr .x19 (u + 0x3c#64) C.writeZeroErrAddr],
    .words (u + 0x40#64) [0x52800059#32, 0xd503201f#32],
    .instrs u 0x48 [iAdr .x22 (u + 0x48#64) C.defaultOsFunctionsAddr],
    .words (u + 0x4c#64)
      [0x5280003b#32, 0x14000002#32, 0xb40003b4#32, 0x52800040#32,
       0xaa1503e1#32, 0xaa1403e2#32],
    .instrs u 0x64 [iBl (u + 0x64#64) C.writeAddr],
    .words (u + 0x68#64)
      [0xb100041f#32, 0x540000e0#32, 0xb40002e0#32, 0xeb000288#32,
       0x54000403#32, 0x8b0002b5#32, 0xaa0803f4#32, 0x17fffff4#32],
    .words (u + 0xc8#64)
      [0xaa1f03f3#32, 0xaa1303e0#32, 0xa9464ff4#32, 0xa94557f6#32,
       0xa9445ff8#32, 0xa94367fa#32, 0xa9426ffc#32, 0xa9417bfd#32,
       0x9101c3ff#32, 0xd65f03c0#32] ]

structure HbSyscallsAndStderrCode (P : Program) (C : HbCliLayout) : Prop where
  io     : CodeChunks P (hbSyscallIoChunks C)
  stderr : CodeChunks P (hbStderrWriteAllChunks C)

section WordTreeCheck
open ProofLib.ProgramReflection

private theorem codeChunk_holds_withSvc {P : Program} {svc : State → State} :
    ∀ {c : CodeChunk}, c.holds P → c.holds (P.withSvc svc)
  | .words _ _, h => h
  | .instrs0 _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi
  | .instrs _ _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi

private theorem codeChunks_withSvc {P : Program} {svc : State → State} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeChunks (P.withSvc svc) cs
  | [], _ => trivial
  | [_], h => codeChunk_holds_withSvc h
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨codeChunk_holds_withSvc h1, codeChunks_withSvc h2⟩

theorem HbSyscallsAndStderrCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbSyscallsAndStderrCode P C) :
    HbSyscallsAndStderrCode (P.withSvc svc) C :=
  ⟨codeChunks_withSvc h.io, codeChunks_withSvc h.stderr⟩

private theorem codeChunks_of_check {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, codeChunks_of_check hc h.2⟩

def checkHbSyscallsAndStderrCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbSyscallIoChunks C).all (checkCodeChunk base t) &&
  (hbStderrWriteAllChunks C).all (checkCodeChunk base t)

theorem hbSyscallsAndStderrCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbSyscallsAndStderrCode C P.base t = true) :
    HbSyscallsAndStderrCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkHbSyscallsAndStderrCode at hok
  rw [Bool.and_eq_true] at hok
  exact ⟨codeChunks_of_check hc hok.1, codeChunks_of_check hc hok.2⟩

end WordTreeCheck

/-! ## Internal code unpacking and non-VM preservation helpers -/

private def fetchAtAcc (P : Program) (base : BitVec 64) : Nat → List Instr → Prop → Prop
  | _, [], acc => acc
  | off, x :: xs, acc => P.fetch (base + BitVec.ofNat 64 off) = some x ∧ fetchAtAcc P base (off + 4) xs acc

private theorem fetchAtAcc_of_fn {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr),
      (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) →
      fetchAtAcc P base off is acc
  | _, [], _ => hacc
  | off, _ :: xs, h =>
    ⟨by simpa using h 0 (Nat.zero_lt_succ _),
     fetchAtAcc_of_fn hacc (off + 4) xs fun i hi => by
       simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩

private def chunkStepAcc (P : Program) (acc : Prop) : CodeChunk → Prop
  | .words a ws => P.hasCode a ws ∧ acc
  | .instrs0 b is => fetchAtAcc P b 0 is acc
  | .instrs b o is => fetchAtAcc P b o is acc

private def chunksStepFacts (P : Program) : List CodeChunk → Prop
  | [] => True
  | c :: cs => chunkStepAcc P (chunksStepFacts P cs) c

private theorem chunkToStepAcc {P : Program} {acc : Prop} (hacc : acc) :
    ∀ {c : CodeChunk}, c.holds P → chunkStepAcc P acc c
  | .words _ _, h => ⟨h, hacc⟩
  | .instrs0 _ _, h => fetchAtAcc_of_fn hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => fetchAtAcc_of_fn hacc o _ fun i hi => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi

private theorem chunksToStepFacts {P : Program} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → chunksStepFacts P cs
  | [], _ => trivial
  | [_], h => chunkToStepAcc trivial h
  | _ :: _ :: _, ⟨h1, h2⟩ => chunkToStepAcc (chunksToStepFacts h2) h1

local macro "unpack_hb_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := chunksToStepFacts $h
  simp only [$chunks:ident, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

private theorem bv64_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_lin
local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))
local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))
local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)

private def projTidSig (s : State) := (s.tpidrEl0, s.sigActions)

local macro "close_tid_sig" : tactic =>
  `(tactic| simp +zetaDelta [projTidSig, wp_norm, arm64_norm])

private theorem hbNonVmPreserved_of_parts {s0 sf : State}
    (htid : projTidSig sf = projTidSig s0)
    (hvm : VmFieldsPreserved s0 sf)
    (hkf : s0.mem.KeepsFrozen sf.mem) :
    HbNonVmPreserved s0 sf := by
  unfold projTidSig at htid
  simp only [Prod.mk.injEq] at htid
  exact ⟨htid.1, htid.2, hvm, hkf⟩

theorem HbNonVmPreserved.of_stdState {s0 sf : State}
    (h : StdStatePreserved s0 sf) (hkf : s0.mem.KeepsFrozen sf.mem) :
    HbNonVmPreserved s0 sf :=
  ⟨h.2.2.1, h.2.2.2.1, ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩, hkf⟩

private theorem subroutine_ok_of_sepWP_frozen {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWP prog (s0.readReg64 Reg.lr) s0 P_init (fun sf P_f =>
          (s0.mem.KeepsFrozen sf.mem → sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P_init, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P_init, R, hm, ?_⟩
  exact SepWP.mono_frozen (Φ := s0.mem.KeepsFrozen) (fun _ _ => Memory.KeepsFrozen.trans)
    (Memory.KeepsFrozen.refl s0.mem) hwp
    (fun sf P_f _ _ hkf ⟨hpost, hsp_f, hcs_f⟩ => ⟨hpost hkf, hsp_f, hcs_f⟩)

private theorem subroutine_ok_of_sepWP_nonVm {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWP (prog.withSvc nonVmSvc) (s0.readReg64 Reg.lr) s0 P_init (fun sf P_f =>
          (VmFieldsPreserved s0 sf → s0.mem.KeepsFrozen sf.mem →
            sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  refine subroutine_ok_of_sepWP_frozen fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨P_init, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P_init, hm, SepWP.of_nonVm hext hsvc ?_⟩
  exact SepWP.mono hwp fun sf P_f _ _ ⟨hpost, hsp_f, hcs_f⟩ hvm => ⟨hpost hvm, hsp_f, hcs_f⟩

set_option linter.literalFetch false in
private theorem fetch_sccp_svc {P : Program} {C : HbCliLayout} (hio : CodeChunks P (hbSyscallIoChunks C)) :
    P.fetch (C.std.sccpAddr + 0x1c#64) = some (.system false 0#16) := by
  unpack_hb_code hbSyscallIoChunks hio
  exact Program.fetch_of_hasCode_decodeAt 7 (hex := sccpWords)
    (by with_reducible assumption) (by simp only [wp_norm]) (by decide)

/-! ### `__syscall_ret` Non-Error Fast Path (`ret.toNat < 2 ^ 63`) -/

private theorem syscallRetFast_wp {P : Program} {C : HbCliLayout} {target_pc ret_pc ret : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : P.hasCode C.std.syscallRetAddr syscallRetFastWords)
    (hpc : s.pc = C.std.syscallRetAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ret) (hret_lt : ret.toNat < 2 ^ 63)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → sf.readReg64 .x0 = ret →
      sf.fs = s.fs → sf.trace = s.trace → projTidSig sf = projTidSig s →
      SepWP P target_pc sf (stackAt s.sp 32 ∗ F) post oom) :
    SepWP P target_pc s (stackAt s.sp 32 ∗ F) post oom := by
  have hhi : ConditionHolds CondCode.HI (addsPState64 ret 4096#64) = false := by
    rw [conditionHolds_hi_addsPState64]
    have hult : BitVec.ult (ret + 4096#64) ret = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hult, Bool.false_and]
  rw [stackAt_eq_cells s.sp 4]; unpack_cells 4
  wp_steps
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 32 ∗ F)
    (fun _ _ => by rw [show (32 : Nat) = 8 * 4 from rfl, stackAt_eq_cells s.sp 4]; repack_cells) ?_
  exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
    (by simp [wp_norm, arm64_norm, hx0]) rfl rfl (by close_tid_sig)

/-! ## `musl` `read` (`STDIN_FILENO = 0`) and `write` (`stdout` / `stderr`) contracts -/

/-- Total-correctness contract for `ssize_t read(0, bufPtr, count)` (`count.toNat < 2 ^ 63`) on an
    open `STDIN` descriptor (`HbStdinOpen rem s0.fs`). -/
def hbReadSpec : Spec (List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (rem, bufPtr, count) s0 =>
    ⌜s0.readReg32 .x0 = 0#32 ∧
      s0.readReg64 .x1 = bufPtr ∧
      s0.readReg64 .x2 = count ∧
      count.toNat < 2 ^ 63 ∧
      bufPtr.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      HbStdinOpen rem s0.fs⌝ ∗
    (memRegion bufPtr count.toNat ∗ stackAt s0.sp 32)
  post := fun (rem, bufPtr, count) s0 sf =>
    let chunk := rem.take (min count.toNat Arm64.MAX_RW_COUNT)
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      HbStdinOpen (rem.drop chunk.length) sf.fs ∧
      sf.trace = s0.trace ∧
      HbNonVmPreserved s0 sf⌝ ∗
    ((bufPtr ↦ₛ chunk) ∗
      memRegion (bufPtr + BitVec.ofNat 64 chunk.length) (count.toNat - chunk.length) ∗
      stackAt s0.sp 32)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbRead_ok {P : Program} {C : HbCliLayout}
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.readAddr hbReadSpec := by
  have hc' := hc.withSvc (svc := nonVmSvc)
  have hsvc_fn := fetch_sccp_svc hc'.io
  unpack_hb_code hbSyscallIoChunks hc'.io
  refine subroutine_ok_of_sepWP_nonVm hext hsvc fun ⟨rem, bufPtr, count⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [hbReadSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcnt_lt, hbuf_va, ⟨desc, hopen, hkind, hrd, hrem⟩⟩, hm⟩
  refine ⟨stackAt s0.sp 32 ∗ memRegion bufPtr count.toNat, by sep_entail, ?_⟩
  rw [memRegion_eq_exists_bytes bufPtr count.toNat (Nat.le_of_lt count.isLt), sepExists_sepConj_right]
  refine SepWP.exists_elim fun bs₀ => ?_
  rw [← sepConj_assoc, sepConj_comm (stackAt s0.sp 32) ⌜bs₀.length = count.toNat⌝, sepConj_assoc]
  refine SepWP.pure_elim fun hlen_bs => ?_
  rw [stackAt_eq_cells s0.sp 4]; unpack_cells 4
  wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps 7
  let chunk := (s0.fs.fdBytes desc |>.drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)
  have hchunk_eq : chunk = rem.take (min count.toNat Arm64.MAX_RW_COUNT) := by dsimp only [chunk]; rw [hrem]
  have hchunk_eq' : chunk = rem.take (min count.toNat 2147479552) := hchunk_eq
  have hchunk_le : chunk.length ≤ count.toNat :=
    Nat.le_trans (List.length_take_le _ _) (Nat.min_le_left _ _)
  have hchunk_lt : (BitVec.ofNat 64 chunk.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  refine SepWP.weaken_pre (P' := (bufPtr ↦ₛ bs₀) ∗ ?F_svc) (by sep_frame) ?_
  refine SepWP.step_svc_read_clamped (fd := 0#64) (buf := bufPtr) (count := count) (desc := desc)
    wp_a (by simp [wp_norm, arm64_norm, hrun]) hsvc_fn wp_a
    (by simp only [wp_norm, arm64_norm] at hx0 ⊢; bv_bits) (by decide)
    wp_a wp_a hlen_bs hopen (by rw [hkind]; rfl) hrd ?_
    (by simp [Program.evalInst, Program.withSvc, execInstWithSvc, wp_norm, arm64_norm])
    (hva := hbuf_va) (hlfs := fun hk => by rw [hkind] at hk; cases hk)
  dsimp only
  conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]
  wp_steps; wp_steps; norm_jmp
  refine SepWP.weaken_pre_frame (P' := stackAt s0.sp 32 ∗
      ((bufPtr ↦ₛ (chunk ++ bs₀.drop chunk.length))))
    (fun _ _ => by rw [show (32 : Nat) = 8 * 4 from rfl, stackAt_eq_cells s0.sp 4]; repack_cells) ?_
  refine syscallRetFast_wp (C := C) (ret_pc := s0.readReg64 Reg.lr) (ret := BitVec.ofNat 64 chunk.length)
    (by with_reducible assumption) wp_a (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    wp_a wp_a hchunk_lt fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f htid_f => ?_
  apply SepWP.done hpc_f hrun_f
  have hsp_sf : sf.sp = s0.sp := by simpa [wp_norm, arm64_norm] using hsp_f
  have hcs_sf : CalleeSavedPreserved s0 sf := by unpack_cs hcs_f; close_cs
  refine ⟨fun hvm hkf hmf => ?_, hsp_sf, hcs_sf⟩
  have hfs_eq : sf.fs = s0.fs.setFd 0#64 (some { desc with offset := desc.offset + chunk.length }) := by
    simp only [wp_norm, arm64_norm] at hfs_f
    rw [← hchunk_eq', ← hkind] at hfs_f
    exact hfs_f
  have hopen_f : HbStdinOpen (rem.drop (rem.take (min count.toNat Arm64.MAX_RW_COUNT)).length) sf.fs := by
    rw [hfs_eq]
    refine ⟨{ desc with offset := desc.offset + chunk.length }, ?_, hkind, hrd, ?_⟩
    · simp [FsState.setFd]
    · have hfb : (s0.fs.setFd 0#64 (some { desc with offset := desc.offset + chunk.length })).fdBytes
          { desc with offset := desc.offset + chunk.length } = s0.fs.fdBytes desc := by
        cases desc with
        | mk p am ap off k =>
          simp only at hkind; subst hkind
          cases s0.fs; rfl
      rw [hfb, ← List.drop_drop, hrem, hchunk_eq]
  have htr_sf : sf.trace = s0.trace := by simpa [wp_norm, arm64_norm] using htr_f
  have htid_sf : projTidSig sf = projTidSig s0 := htid_f.trans (by close_tid_sig)
  dsimp only [hbReadSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by rw [← hchunk_eq]; exact hx0_f, hopen_f, htr_sf,
    hbNonVmPreserved_of_parts htid_sf hvm hkf⟩, ?_⟩
  rw [← hchunk_eq]
  simp only [wp_norm, arm64_norm] at hmf
  have hslice : (bufPtr ↦ₛ (chunk ++ bs₀.drop chunk.length)) ⊢
      (bufPtr ↦ₛ chunk) ∗ memRegion (bufPtr + BitVec.ofNat 64 chunk.length) (count.toNat - chunk.length) := by
    rw [pointsToBytes_append]
    refine sepConj_mono (Entails.refl _) ?_
    have hdl : (bs₀.drop chunk.length).length = count.toNat - chunk.length := by
      rw [List.length_drop, hlen_bs]
    rw [← hdl]
    exact pointsToBytes_entails_memRegion _ _
  refine Satisfies.mono ?_ hmf
  refine Entails.trans (Q := ((bufPtr ↦ₛ (chunk ++ bs₀.drop chunk.length)) ∗ stackAt s0.sp 32) ∗ R)
    (by sep_frame) ?_
  exact Entails.trans (sepConj_mono (sepConj_mono hslice (Entails.refl _)) (Entails.refl _)) (by sep_frame)

theorem call_hbRead {P : Program} {C : HbCliLayout} {target_pc ret_pc : BitVec 64}
    (hc : HbSyscallsAndStderrCode P C)
    {rem : List (BitVec 8)} {bufPtr count : BitVec 64}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hcnt_lt : count.toNat < 2 ^ 63)
    (hbuf_va : bufPtr.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT)
    (hopen : HbStdinOpen rem s.fs)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (memRegion bufPtr count.toNat ∗ stackAt s.sp 32) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      let chunk := rem.take (min count.toNat Arm64.MAX_RW_COUNT)
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length →
      HbStdinOpen (rem.drop chunk.length) sf.fs →
      sf.trace = s.trace → HbNonVmPreserved s sf →
      SepWP P target_pc sf
        (((bufPtr ↦ₛ chunk) ∗
          memRegion (bufPtr + BitVec.ofNat 64 chunk.length) (count.toNat - chunk.length) ∗
          stackAt s.sp 32) ∗ F) post oom)
    (hpc : s.pc = C.readAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg32 .x0 = 0#32 := by simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx1 : s.readReg64 .x1 = bufPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = count := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ hbReadSpec.onOom (rem, bufPtr, count) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame (hbRead_ok hc hsvc hext) (x := (rem, bufPtr, count)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [hbReadSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hcnt_lt, hbuf_va, hopen⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbReadSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hopen_f, htr_f, hnv_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hopen_f htr_f hnv_f

/-! ### `write` (`stdout` / `stderr`) over Read-Only (`↦ᵣ`) or Read-Write (`↦ₛ`) Slices -/

/-- Byte-slice assertion parameterized by `ro : Bool` (`ptr ↦ᵣ bs` when `ro = true`,
    `ptr ↦ₛ bs` when `ro = false`). -/
def hbBytesSlice : Bool → BitVec 64 → List (BitVec 8) → SepProp
  | true, ptr, bs => ptr ↦ᵣ bs
  | false, ptr, bs => ptr ↦ₛ bs

private theorem readBytes_canRead_of_pointsToBytesRO {m : Memory} {ptr : BitVec 64} {R : SepProp}
    (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) (hm : m ⊨ (ptr ↦ᵣ bs) ∗ R) :
    m.canRead ptr bs.length = true ∧ m.readBytes ptr bs.length = bs := by
  induction bs generalizing ptr R with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    rw [pointsToBytesRO_cons, sepConj_assoc] at hm
    have hld : SepLoad8 ptr ((ptr ↦₈ᵣ b) ∗ (((ptr + 1#64) ↦ᵣ bs) ∗ R)) b :=
      SepLoad8.of_ro_eq_addr rfl rfl
    have hm_emp : m ⊨ ((ptr ↦₈ᵣ b) ∗ (((ptr + 1#64) ↦ᵣ bs) ∗ R)) ∗ emp := by
      simpa [sepConj_emp] using hm
    have hcr1 : m.canRead ptr 1 = true := hld.readable hm_emp
    have hr1 : m.read8 ptr = b := hld.load hm_emp
    have hm_tail : m ⊨ ((ptr + 1#64) ↦ᵣ bs) ∗ ((ptr ↦₈ᵣ b) ∗ R) := by
      rw [sepConj_left_comm] at hm; exact hm
    obtain ⟨hcr_tl, hr_tl⟩ := ih (by simp at hlen; omega) hm_tail
    refine ⟨?_, ?_⟩
    · rw [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff] at hcr1 hcr_tl ⊢
      have hshift : ∀ i : Nat, i > 0 → ptr + 1#64 + BitVec.ofNat 64 (i - 1) = ptr + BitVec.ofNat 64 i := by
        intro i hpos
        rw [BitVec.add_assoc, show 1#64 + BitVec.ofNat 64 (i - 1) = BitVec.ofNat 64 i by
          change BitVec.ofNat 64 1 + BitVec.ofNat 64 (i - 1) = BitVec.ofNat 64 i
          rw [← BitVec.ofNat_add]; congr 1; omega]
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exact hcr1.1 0 (by omega)
        · have h := hcr_tl.1 (i - 1) (by simp at hi; omega)
          rwa [hshift i hpos] at h
      · rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exact hcr1.2 0 (by omega)
        · have h := hcr_tl.2 (i - 1) (by simp at hi; omega)
          rwa [hshift i hpos] at h
    · simp only [List.length_cons, Memory.readBytes, hr1, hr_tl]

private theorem step_svc_write_stdio_ro {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (isOut : Bool) {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hfd : s.readReg64 .x0 = (if isOut then 1#64 else 2#64))
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs.length = count.toNat)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 count).setPC (pc + 4#64))
      ((buf ↦ᵣ bs) ∗ F) post oom)
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega) :
    SepWP prog target_pc s ((buf ↦ᵣ bs) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm' : s.mem ⊨ (buf ↦ᵣ bs) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hlen64 : bs.length ≤ 2 ^ 64 := by rw [hlen]; exact Nat.le_of_lt count.isLt
  obtain ⟨hcr, hrd⟩ := readBytes_canRead_of_pointsToBytesRO bs hlen64 hm'
  rw [hlen] at hcr hrd
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have hmin : min count.toNat Arm64.MAX_RW_COUNT = count.toNat := Nat.min_eq_left hmax
  have hcnt_eq : BitVec.ofNat 64 count.toNat = count := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hexec : execWrite s =
      ((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 count).advancePC := by
    by_cases h0 : count = 0#64
    · subst h0
      have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hbs0
      have hnotva : ¬ (Arm64.USER_VA_LIMIT < buf.toNat) := by simpa using Nat.not_lt.mpr hva
      cases isOut
      · rw [execWrite_stderr s (by simpa using hfd)]
        simp [hbuf, hcnt, hnotva, TraceEvent.ofBytes, State.appendTrace]
      · rw [execWrite_stdout s (by simpa using hfd)]
        simp [hbuf, hcnt, hnotva, TraceEvent.ofBytes, State.appendTrace]
    · have h0_f : (count == 0#64) = false := beq_false_of_ne h0
      cases isOut
      · rw [execWrite_stderr s (by simpa using hfd)]
        simp only [hbuf, hcnt, hva_f, h0_f, hmin, hcnt_eq, hcr, hrd, Bool.false_eq_true, ↓reduceIte]
      · rw [execWrite_stdout s (by simpa using hfd)]
        simp only [hbuf, hcnt, hva_f, h0_f, hmin, hcnt_eq, hcr, hrd, Bool.false_eq_true, ↓reduceIte]
  have hadv : (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
      .x0 count).advancePC) =
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
      .x0 count).setPC (pc + 4#64)) := by
    subst hpc; rfl
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, hadv]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

/-- Total-correctness contract for `ssize_t write(isOut ? 1 : 2, bufPtr, bs.length)`
    (`bs.length ≤ MAX_RW_COUNT`), parameterized by `ro : Bool` (`↦ᵣ` vs `↦ₛ`). -/
def hbWriteStdioSpec (ro : Bool) : Spec (Bool × BitVec 64 × List (BitVec 8)) where
  pre := fun (isOut, bufPtr, bs) s0 =>
    ⌜s0.readReg32 .x0 = (if isOut then 1#32 else 2#32) ∧
      s0.readReg64 .x1 = bufPtr ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length ≤ Arm64.MAX_RW_COUNT ∧
      bufPtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (hbBytesSlice ro bufPtr bs ∗ stackAt s0.sp 32)
  post := fun (isOut, bufPtr, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs ∧
      HbNonVmPreserved s0 sf⌝ ∗
    (hbBytesSlice ro bufPtr bs ∗ stackAt s0.sp 32)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbWrite_stdio_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.writeAddr (hbWriteStdioSpec ro) := by
  have hc' := hc.withSvc (svc := nonVmSvc)
  have hsvc_fn := fetch_sccp_svc hc'.io
  unpack_hb_code hbSyscallIoChunks hc'.io
  refine subroutine_ok_of_sepWP_nonVm hext hsvc fun ⟨isOut, bufPtr, bs⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [hbWriteStdioSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen_max, hbuf_va⟩, hm⟩
  refine ⟨stackAt s0.sp 32 ∗ hbBytesSlice ro bufPtr bs, by sep_entail, ?_⟩
  rw [stackAt_eq_cells s0.sp 4]; unpack_cells 4
  wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps 7
  have hcnt_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [Arm64.MAX_RW_COUNT] at hlen_max
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcnt_lt : (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 := by
    simp only [Arm64.MAX_RW_COUNT] at hlen_max; omega
  have hsvc_eval : ∀ st : State, st.readReg64 .x8 = 64#64 →
      (P.withSvc nonVmSvc).evalInst (.system false 0#16) st = execWrite st := fun st hx8 => by
    simp [Program.evalInst, Program.withSvc, execInstWithSvc, wp_norm, arm64_norm, hx8]
  cases ro
  · dsimp only [hbBytesSlice]
    refine SepWP.weaken_pre (P' := (bufPtr ↦ₛ bs) ∗ ?F_rw) (by sep_frame) ?_
    apply (SepWP.step_svc_write_stdio isOut (pc := C.std.sccpAddr + 0x1c#64)
      (buf := bufPtr) (count := BitVec.ofNat 64 bs.length))
    · exact wp_a
    · simp [wp_norm, arm64_norm, hrun]
    · exact hsvc_fn
    · cases isOut <;> (simp only [wp_norm, arm64_norm, Bool.false_eq_true, ↓reduceIte] at hx0 ⊢; bv_bits)
    · exact wp_a
    · exact wp_a
    · exact hcnt_toNat.symm
    · exact hsvc_eval _ wp_a
    conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]
    wp_steps; wp_steps; norm_jmp
    refine SepWP.weaken_pre_frame (P' := stackAt s0.sp 32 ∗ (bufPtr ↦ₛ bs))
      (fun _ _ => by rw [show (32 : Nat) = 8 * 4 from rfl, stackAt_eq_cells s0.sp 4]; repack_cells) ?_
    refine syscallRetFast_wp (C := C) (ret_pc := s0.readReg64 Reg.lr) (ret := BitVec.ofNat 64 bs.length)
      (by with_reducible assumption) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
      wp_a wp_a hcnt_lt fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f htid_f => ?_
    apply SepWP.done hpc_f hrun_f
    have hsp_sf : sf.sp = s0.sp := by simpa [wp_norm, arm64_norm] using hsp_f
    have hcs_sf : CalleeSavedPreserved s0 sf := by unpack_cs hcs_f; close_cs
    refine ⟨fun hvm hkf hmf => ?_, hsp_sf, hcs_sf⟩
    have htid_sf : projTidSig sf = projTidSig s0 := htid_f.trans (by close_tid_sig)
    dsimp only [hbWriteStdioSpec, hbBytesSlice]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, by simpa [wp_norm, arm64_norm] using hfs_f,
      by simpa [wp_norm, arm64_norm] using htr_f,
      hbNonVmPreserved_of_parts htid_sf hvm hkf⟩, by sep_entail⟩
  · dsimp only [hbBytesSlice]
    refine SepWP.weaken_pre (P' := (bufPtr ↦ᵣ bs) ∗ ?F_ro) (by sep_frame) ?_
    apply (step_svc_write_stdio_ro isOut (pc := C.std.sccpAddr + 0x1c#64)
      (buf := bufPtr) (count := BitVec.ofNat 64 bs.length))
    · exact wp_a
    · simp [wp_norm, arm64_norm, hrun]
    · exact hsvc_fn
    · cases isOut <;> (simp only [wp_norm, arm64_norm, Bool.false_eq_true, ↓reduceIte] at hx0 ⊢; bv_bits)
    · exact wp_a
    · exact wp_a
    · exact hcnt_toNat.symm
    · exact hsvc_eval _ wp_a
    conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]
    wp_steps; wp_steps; norm_jmp
    refine SepWP.weaken_pre_frame (P' := stackAt s0.sp 32 ∗ (bufPtr ↦ᵣ bs))
      (fun _ _ => by rw [show (32 : Nat) = 8 * 4 from rfl, stackAt_eq_cells s0.sp 4]; repack_cells) ?_
    refine syscallRetFast_wp (C := C) (ret_pc := s0.readReg64 Reg.lr) (ret := BitVec.ofNat 64 bs.length)
      (by with_reducible assumption) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
      wp_a wp_a hcnt_lt fun sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f htid_f => ?_
    apply SepWP.done hpc_f hrun_f
    have hsp_sf : sf.sp = s0.sp := by simpa [wp_norm, arm64_norm] using hsp_f
    have hcs_sf : CalleeSavedPreserved s0 sf := by unpack_cs hcs_f; close_cs
    refine ⟨fun hvm hkf hmf => ?_, hsp_sf, hcs_sf⟩
    have htid_sf : projTidSig sf = projTidSig s0 := htid_f.trans (by close_tid_sig)
    dsimp only [hbWriteStdioSpec, hbBytesSlice]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, by simpa [wp_norm, arm64_norm] using hfs_f,
      by simpa [wp_norm, arm64_norm] using htr_f,
      hbNonVmPreserved_of_parts htid_sf hvm hkf⟩, by sep_entail⟩

abbrev hbWrite_stdio_ro_ok {P : Program} {C : HbCliLayout}
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.writeAddr (hbWriteStdioSpec true) :=
  hbWrite_stdio_ok true hc hsvc hext

abbrev hbWrite_stdio_rw_ok {P : Program} {C : HbCliLayout}
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.writeAddr (hbWriteStdioSpec false) :=
  hbWrite_stdio_ok false hc hsvc hext

theorem call_hbWrite_stdio {P : Program} {C : HbCliLayout} {target_pc ret_pc : BitVec 64}
    (ro : Bool) (hc : HbSyscallsAndStderrCode P C)
    {isOut : Bool} {bufPtr : BitVec 64} {bs : List (BitVec 8)}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hlen_max : bs.length ≤ Arm64.MAX_RW_COUNT)
    (hbuf_va : bufPtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBytesSlice ro bufPtr bs ∗ stackAt s.sp 32) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = BitVec.ofNat 64 bs.length →
      sf.fs = s.fs →
      sf.trace = s.trace ++ TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs →
      HbNonVmPreserved s sf →
      SepWP P target_pc sf ((hbBytesSlice ro bufPtr bs ∗ stackAt s.sp 32) ∗ F) post oom)
    (hpc : s.pc = C.writeAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg32 .x0 = (if isOut then 1#32 else 2#32) := by
      simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx1 : s.readReg64 .x1 = bufPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (hbWriteStdioSpec ro).onOom (isOut, bufPtr, bs) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame (hbWrite_stdio_ok ro hc hsvc hext) (x := (isOut, bufPtr, bs)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [hbWriteStdioSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen_max, hbuf_va⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbWriteStdioSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hfs_f, htr_f, hnv_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f hnv_f

/-! ## `<Stderr as Write>::write_all` (`C.stderrWriteAllAddr`) -/

private theorem stderrGlobal_split (g : BitVec 64) :
    (g ↦ₛ List.replicate 24 0#8) =
      (g ↦₆₄ 0#64) ∗ ((g + 0x08#64) ↦₃₂ 0#32) ∗
      ((g + 0x0c#64) ↦₃₂ 0#32) ∗ ((g + 0x10#64) ↦₆₄ 0#64) := by
  have hbs : List.replicate 24 (0#8) =
      unpack64 0#64 ++ (unpack32 0#32 ++ (unpack32 0#32 ++ unpack64 0#64)) := by decide
  rw [hbs]
  simp only [pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp (config := { decide := true }) only [unpack64, unpack32,
    List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]

private theorem isAligned32_add8_of_mod8 {a : BitVec 64} (ha : a.toNat % 8 = 0) :
    MemWidth.isAligned .W32 (a + 0x08#64) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_add]
  change ((a.toNat + 8) % 2 ^ 64 &&& (2 ^ 2 - 1)) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem isAligned64_of_mod8 {a : BitVec 64} (ha : a.toNat % 8 = 0) :
    MemWidth.isAligned .W64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (a.toNat &&& (2 ^ 3 - 1)) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact ha

/-- Specification for `<std::sys::stdio::unix::Stderr as std::io::Write>::write_all`
    (`C.unixStderrWriteAllAddr`) over a non-empty byte slice (`0 < msgBytes.length < 2 ^ 63`). -/
def hbUnixStderrWriteAllSpec (ro : Bool) (C : HbCliLayout) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (msgPtr, msgBytes) s0 =>
    ⌜s0.readReg64 .x1 = msgPtr ∧
     s0.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length ∧
     0 < msgBytes.length ∧
     msgBytes.length ≤ Arm64.MAX_RW_COUNT ∧
     msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (hbBytesSlice ro msgPtr msgBytes ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     stackAt s0.sp 144)
  post := fun (msgPtr, msgBytes) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
     sf.fs = s0.fs ∧
     sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr msgBytes ∧
     HbNonVmPreserved s0 sf⌝ ∗
    (hbBytesSlice ro msgPtr msgBytes ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     stackAt s0.sp 144)

theorem hbUnixStderrWriteAll_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.unixStderrWriteAllAddr (hbUnixStderrWriteAllSpec ro C) := by
  apply subroutine_ok_of_sepWP_frozen
  rintro ⟨msgPtr, msgBytes⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbUnixStderrWriteAllSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hmem⟩
  have hlen_lt : msgBytes.length < 2 ^ 63 := by simp only [Arm64.MAX_RW_COUNT] at hlen_max; omega
  have hlen_toNat : (BitVec.ofNat 64 msgBytes.length).toNat = msgBytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn_ne_zero : BitVec.ofNat 64 msgBytes.length ≠ 0#64 := by
    intro heq; have h := congrArg BitVec.toNat heq
    rw [hlen_toNat] at h; change msgBytes.length = 0 at h; omega
  have hne0 : (BitVec.ofNat 64 msgBytes.length == 0#64) = false := beq_false_of_ne hn_ne_zero
  have hn_add1_ne : BitVec.ofNat 64 msgBytes.length + 1#64 ≠ 0#64 := by
    intro heq; have h := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, hlen_toNat, show (1#64).toNat = 1 from rfl,
        show (0#64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at h
    omega
  have hcmn : (BitVec.ofNat 64 msgBytes.length + 1#64 == 0#64) = false := beq_false_of_ne hn_add1_ne
  have hult_self : (BitVec.ofNat 64 msgBytes.length).ult (BitVec.ofNat 64 msgBytes.length) = false := by
    simp [BitVec.ult]
  refine ⟨stackAt s0.sp 144 ∗ hbBytesSlice ro msgPtr msgBytes ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr),
    by sep_frame, ?_⟩
  conv =>
    arg 4
    rw [show (144 : Nat) = 32 + 8 * 14 from rfl, stackAt_split_cells s0.sp 32 14 (by decide)]
  unpack_cells 14
  refine SepWP.seq_nonVm (mid := C.writeAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv1
  iterate 10 (wp_steps; (try norm_jmp))
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine call_hbWrite_stdio ro hc hsvc hext hlen_max hmsg_va
    (ret_pc := C.unixStderrWriteAllAddr + 0x68#64) (isOut := false)
    (bufPtr := msgPtr) (bs := msgBytes) (F := ?_)
    (by simp only [wp_norm, arm64_norm]; sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hfs2 htr2 hnv2 => ?_)
    (hsp_align := by
      simp only [State.spAligned, wp_norm, arm64_norm]
      simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x70#64 hsp_align)
    (hx0 := by simp [wp_norm, arm64_norm])
    (hx1 := by simp [wp_norm, arm64_norm])
    (hx2 := by simp [wp_norm, arm64_norm])
  have hx0_2' : s2.readReg64 (.gpr 0#5) = BitVec.ofNat 64 msgBytes.length := hx0_2
  have hx20_2 : s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 msgBytes.length := by
    rw [← Reg.x20, hcs2.readReg64_x20]; simp [wp_norm, arm64_norm]
  have hx21_2 : s2.readReg64 (.gpr 21#5) = msgPtr := by
    rw [← Reg.x21, hcs2.readReg64_x21]; simp [wp_norm, arm64_norm]
  have hsp2_eq : s2.sp = s0.sp - 0x70#64 := by rw [hsp2]; exact wp_a
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]
    simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x70#64 hsp_align
  refine SepWP.of_nonVm hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv2
  wp_steps; wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := stackAt s0.sp 144 ∗ hbBytesSlice ro msgPtr msgBytes ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr))
    (fun _ hm' => by
      rw [show (144 : Nat) = 32 + 8 * 14 from rfl, stackAt_split_cells s0.sp 32 14 (by decide)]
      simp only [wp_norm, arm64_norm] at hm' ⊢
      cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail) ?_
  apply SepWP.done
    (by unpack_cs hcs2; simp [wp_norm, arm64_norm, *]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun2])
  intro hvm2
  refine ⟨fun hkf hmf => ?_, by simp [wp_norm, arm64_norm],
    by unpack_cs hcs2; close_cs⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hvm_sf := (hvm1.trans hnv2.vm).trans hvm2
  refine ⟨⟨by simp [wp_norm, arm64_norm], ?_, ?_, hbNonVmPreserved_of_parts ?_ hvm_sf hkf⟩, by sep_frame⟩
  · simp only [wp_norm, arm64_norm]; rw [hfs2]; simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]; rw [htr2]; simp only [↓reduceIte, Bool.false_eq_true, wp_norm, arm64_norm]
  · simp only [projTidSig, wp_norm, arm64_norm]
    rw [hnv2.tpidrEl0_eq, hnv2.sigActions_eq]; simp only [wp_norm, arm64_norm]

theorem call_hbUnixStderrWriteAll {P : Program} {C : HbCliLayout} {target_pc ret_pc : BitVec 64}
    (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    {msgPtr : BitVec 64} {msgBytes : List (BitVec 8)}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_pos : 0 < msgBytes.length)
    (hlen_max : msgBytes.length ≤ Arm64.MAX_RW_COUNT)
    (hmsg_va : msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBytesSlice ro msgPtr msgBytes ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        stackAt s.sp 144) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stderr msgBytes →
      HbNonVmPreserved s sf →
      SepWP P target_pc sf ((hbBytesSlice ro msgPtr msgBytes ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        stackAt s.sp 144) ∗ F) post oom)
    (hpc : s.pc = C.unixStderrWriteAllAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = msgPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (hbUnixStderrWriteAllSpec ro C).onOom (msgPtr, msgBytes) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbUnixStderrWriteAll_ok ro hc hsvc hext)
    (x := (msgPtr, msgBytes)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [hbUnixStderrWriteAllSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbUnixStderrWriteAllSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hfs_f, htr_f, hnv_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f hnv_f

private theorem vmFieldsPreserved_of_stdState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    VmFieldsPreserved s0 sf :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem projTidSig_of_stdState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    projTidSig sf = projTidSig s0 := by
  simp only [projTidSig, h.2.2.1, h.2.2.2.1]

private def HbRefStderrHiSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem HbRefStderrHiSaved.refl (s0 : State) : HbRefStderrHiSaved s0 s0 :=
  ⟨rfl, rfl, rfl⟩

private theorem HbRefStderrHiSaved.trans_cs {s0 s1 s2 : State}
    (h1 : HbRefStderrHiSaved s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    HbRefStderrHiSaved s0 s2 := by
  rcases h1 with ⟨h27, h28, hv⟩
  unpack_cs hcs
  exact ⟨by simp_all, by simp_all, by simp_all⟩

private def hbRefStderrSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem hbThreadIdInv_of_one (C : HbCliLayout) (tp : BitVec 64) :
    ((tp + 0x58#64) ↦₆₄ 1#64) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64) ⊢
      HbThreadIdInv C tp := by
  dsimp only [HbThreadIdInv]
  refine Entails.sepExists_right 1#64 ?_
  rw [pure_sepConj_of_true (Or.inr rfl)]
  sep_entail

/-- Specification for `<&std::io::stdio::Stderr as std::io::Write>::write_all`
    (`C.refStderrWriteAllAddr`) over a non-empty byte slice (`0 < msgBytes.length < 2 ^ 63`). -/
def hbRefStderrWriteAllSpec (ro : Bool) (C : HbCliLayout) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 8) where
  pre := fun (refPtr, selfPtr, msgPtr, msgBytes, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = refPtr ∧
     s0.readReg64 .x1 = msgPtr ∧
     s0.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length ∧
     0 < msgBytes.length ∧
     msgBytes.length ≤ Arm64.MAX_RW_COUNT ∧
     msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    ((refPtr ↦₆₄ selfPtr) ∗
     (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
     (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
     hbBytesSlice ro msgPtr msgBytes ∗
     HbThreadIdInv C s0.tpidrEl0 ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
     stackAt s0.sp 224)
  post := fun (refPtr, selfPtr, msgPtr, msgBytes, haveLse) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
     sf.fs = s0.fs ∧
     sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr msgBytes ∧
     HbNonVmPreserved s0 sf⌝ ∗
    ((refPtr ↦₆₄ selfPtr) ∗
     (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
     (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
     hbBytesSlice ro msgPtr msgBytes ∗
     HbThreadIdInv C s0.tpidrEl0 ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
     stackAt s0.sp 224)

private theorem hbRefStderrWriteAll_fromCas4_wp {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hal_stderr : C.stderrGlobalAddr.toNat % 8 = 0)
    (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none)
    {refPtr selfPtr msgPtr : BitVec 64} {msgBytes : List (BitVec 8)} {haveLse : BitVec 8}
    {R : SepProp} {s0 s1 : State}
    (hlen_pos : 0 < msgBytes.length) (hlen_max : msgBytes.length ≤ Arm64.MAX_RW_COUNT)
    (hmsg_va : msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT)
    (hpc1 : s1.pc = C.std.cas4AcqAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 80#64) (hsp1_al : s1.spAligned = true)
    (hlr1 : s1.readReg64 Reg.lr = C.refStderrWriteAllAddr + 0xc8#64)
    (hx0_1 : s1.readReg32 .x0 = 0#32) (hx1_1 : s1.readReg32 .x1 = 1#32)
    (hx2_1 : s1.readReg64 .x2 = C.stderrGlobalAddr + 0x08#64)
    (hx19_1 : s1.readReg64 (.gpr 19#5) = C.stderrGlobalAddr)
    (hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 msgBytes.length)
    (hx21_1 : s1.readReg64 (.gpr 21#5) = msgPtr)
    (hx22_1 : s1.readReg64 (.gpr 22#5) = 1#64)
    (hx25_1 : s1.readReg64 (.gpr 25#5) = 1#64)
    (hhi1 : HbRefStderrHiSaved s0 s1)
    (hfs1 : s1.fs = s0.fs) (htr1 : s1.trace = s0.trace)
    (htid1 : projTidSig s1 = projTidSig s0) (hvm1 : VmFieldsPreserved s0 s1) :
    SepWP P (s0.readReg64 Reg.lr) s1
      ((refPtr ↦₆₄ selfPtr) ∗
       (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
       (C.stderrGlobalAddr ↦₆₄ 0#64) ∗
       ((C.stderrGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
       ((C.stderrGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
       ((C.stderrGlobalAddr + 0x10#64) ↦₆₄ 0#64) ∗
       hbBytesSlice ro msgPtr msgBytes ∗
       ((s0.tpidrEl0 + 0x58#64) ↦₆₄ 1#64) ∗
       (C.std.threadIdCounterAddr ↦₆₄ 1#64) ∗
       (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
       stackAt (s0.sp - 80#64) 144 ∗
       hbRefStderrSavedRegs s0)
      (fun sf P_f =>
        (s0.mem.KeepsFrozen sf.mem → sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (hbRefStderrWriteAllSpec ro C).post (refPtr, selfPtr, msgPtr, msgBytes, haveLse) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hal_g8 : MemWidth.isAligned .W32 (C.stderrGlobalAddr + 0x08#64) = true :=
    isAligned32_add8_of_mod8 hal_stderr
  refine call_stdCas4 hatom.cas4Acq_ok
    (haveLse := haveLse) (ptr := C.stderrGlobalAddr + 0x08#64)
    (v0 := 0#32) (exp := 0#32) (new := 1#32)
    (ret_pc := C.refStderrWriteAllAddr + 0xc8#64) (F := ?_) (by sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hstd2 => ?_)
    (hpc := hpc1) (hrun := hrun1) (hsp_align := hsp1_al) (hlr := hlr1)
    (hx0 := hx0_1) (hx1 := hx1_1) (hx2 := hx2_1) (halign := hal_g8)
  simp only [beq_self_eq_true, ↓reduceIte]
  have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = C.stderrGlobalAddr := by
    rw [← Reg.x19, hcs2.readReg64_x19]; exact hx19_1
  have hx20_2 : s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 msgBytes.length := by
    rw [← Reg.x20, hcs2.readReg64_x20]; exact hx20_1
  have hx21_2 : s2.readReg64 (.gpr 21#5) = msgPtr := by
    rw [← Reg.x21, hcs2.readReg64_x21]; exact hx21_1
  have hx22_2 : s2.readReg64 (.gpr 22#5) = 1#64 := by
    rw [← Reg.x22, hcs2.readReg64_x22]; exact hx22_1
  have hx25_2 : s2.readReg64 (.gpr 25#5) = 1#64 := by
    rw [← Reg.x25, hcs2.readReg64_x25]; exact hx25_1
  have hsp2_eq : s2.sp = s0.sp - 80#64 := hsp2.trans hsp1
  have hsp2_al : s2.spAligned = true := by
    simpa only [State.spAligned, hsp2_eq, ← hsp1] using hsp1_al
  have hhi2 : HbRefStderrHiSaved s0 s2 := hhi1.trans_cs hcs2
  refine SepWP.seq_nonVm (mid := C.unixStderrWriteAllAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv1
  wp_steps; wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
  intro hvm_seg1
  refine call_hbUnixStderrWriteAll ro hc hsvc hext hlen_pos hlen_max hmsg_va
    (ret_pc := C.refStderrWriteAllAddr + 0xf4#64)
    (msgPtr := msgPtr) (msgBytes := msgBytes) (F := ?_)
    (by simp only [wp_norm, arm64_norm, hsp2_eq]; sep_frame)
    (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hfs3 htr3 hnv3 => ?_)
    (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
    (hx1 := by simp [wp_norm, arm64_norm])
    (hx2 := by simp [wp_norm, arm64_norm])
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
  have hx19_3 : s3.readReg64 (.gpr 19#5) = C.stderrGlobalAddr := by
    rw [← Reg.x19, hcs3.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_2]
  have hsp3_eq : s3.sp = s0.sp - 80#64 := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by
    simpa only [State.spAligned, hsp3_eq, ← hsp1] using hsp1_al
  have hhi3 : HbRefStderrHiSaved s0 s3 := by
    rcases hhi2 with ⟨h27, h28, hv⟩; unpack_cs hcs3
    exact ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm]⟩
  refine SepWP.seq_nonVm (mid := C.std.swp4RelAddr) hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv2
  wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun3])
  intro hvm_seg2
  refine call_stdSwp4 hatom.swp4Rel_ok
    (haveLse := haveLse) (ptr := C.stderrGlobalAddr + 0x08#64)
    (v0 := 1#32) (new := 0#32)
    (ret_pc := C.refStderrWriteAllAddr + 0x15c#64) (F := ?_)
    (by simp only [wp_norm, arm64_norm]; sep_frame)
    (fun s4 hpc4 hrun4 hsp4 hcs4 hx0_4 hstd4 => ?_)
    (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp3_al)
    (halign := hal_g8)
  have hx0_4' : s4.readReg64 (.gpr 0#5) = 1#64 := hx0_4
  have hx20_4 : s4.readReg64 (.gpr 20#5) = 0#64 := by
    rw [← Reg.x20, hcs4.readReg64_x20]; simp [wp_norm, arm64_norm]
  have hsp4_eq : s4.sp = s0.sp - 80#64 := by rw [hsp4]; simp [wp_norm, arm64_norm, hsp3_eq]
  have hsp4_al : s4.spAligned = true := by
    simpa only [State.spAligned, hsp4_eq, ← hsp1] using hsp1_al
  have hhi4 : HbRefStderrHiSaved s0 s4 := by
    rcases hhi3 with ⟨h27, h28, hv⟩; unpack_cs hcs4
    exact ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm]⟩
  dsimp only [hbRefStderrSavedRegs]
  refine SepWP.of_nonVm hext hsvc ?_
  have hc_nv3 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv3
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := (refPtr ↦₆₄ selfPtr) ∗
      (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
      hbBytesSlice ro msgPtr msgBytes ∗
      HbThreadIdInv C s0.tpidrEl0 ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      stackAt s0.sp 224)
    (fun R' hm' => by
      rw [stderrGlobal_split C.stderrGlobalAddr,
          show (224 : Nat) = 144 + 8 * 10 from rfl,
          stackAt_split_cells s0.sp 144 10 (by decide)]
      simp only [wp_norm, arm64_norm] at hm' ⊢
      have hm1 : _ ⊨ (((s0.tpidrEl0 + 0x58#64) ↦₆₄ 1#64) ∗
          (C.std.threadIdCounterAddr ↦₆₄ 1#64)) ∗ _ := (by sep_frame : _ → _) hm'
      clear hm'
      replace hm1 := Satisfies.mono (sepConj_mono_left (hbThreadIdInv_of_one C s0.tpidrEl0)) hm1
      cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail) ?_
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun4])
  intro hvm_seg3
  refine ⟨fun hkf hmf => ?_, by simp [wp_norm, arm64_norm],
    by rcases hhi4 with ⟨_, _, _⟩; close_cs⟩
  dsimp only [hbRefStderrWriteAllSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hvm_sf :=
    ((((hvm1.trans (vmFieldsPreserved_of_stdState hstd2)).trans hvm_seg1).trans hnv3.vm).trans
      hvm_seg2).trans ((vmFieldsPreserved_of_stdState hstd4).trans hvm_seg3)
  refine ⟨⟨by simp [wp_norm, arm64_norm], ?_, ?_, hbNonVmPreserved_of_parts ?_ hvm_sf hkf⟩, hmf⟩
  · simp only [wp_norm, arm64_norm]
    rw [hstd4.1]; simp only [wp_norm, arm64_norm]
    rw [hfs3]; simp only [wp_norm, arm64_norm]
    rw [hstd2.1, hfs1]
  · simp only [wp_norm, arm64_norm]
    rw [hstd4.2.1]; simp only [wp_norm, arm64_norm]
    rw [htr3]; simp only [wp_norm, arm64_norm]
    rw [hstd2.2.1, htr1]
  · simp only [projTidSig, wp_norm, arm64_norm]
    rw [hstd4.2.2.1, hstd4.2.2.2.1]; simp only [wp_norm, arm64_norm]
    rw [hnv3.tpidrEl0_eq, hnv3.sigActions_eq]; simp only [wp_norm, arm64_norm]
    rw [hstd2.2.2.1, hstd2.2.2.2.1]
    exact htid1

theorem hbRefStderrWriteAll_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hal_stderr : C.stderrGlobalAddr.toNat % 8 = 0)
    (hal_ctr : C.std.threadIdCounterAddr.toNat % 8 = 0)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.refStderrWriteAllAddr (hbRefStderrWriteAllSpec ro C) := by
  apply subroutine_ok_of_sepWP_frozen
  rintro ⟨refPtr, selfPtr, msgPtr, msgBytes, haveLse⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbRefStderrWriteAllSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hmem⟩
  have hsp1_al : (s0.sp - 80#64) &&& 15#64 == 0#64 := by
    simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x50#64 hsp_align
  refine ⟨stackAt s0.sp 224 ∗ HbThreadIdInv C s0.tpidrEl0 ∗
      (refPtr ↦₆₄ selfPtr) ∗ (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
      hbBytesSlice ro msgPtr msgBytes ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse),
    by sep_frame, ?_⟩
  dsimp only [HbThreadIdInv]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro tid
  rw [sepConj_left_comm (stackAt s0.sp 224), sepConj_assoc]
  apply SepWP.pure_elim; intro htid_or
  conv =>
    arg 4
    rw [stderrGlobal_split C.stderrGlobalAddr,
        show (224 : Nat) = 144 + 8 * 10 from rfl,
        stackAt_split_cells s0.sp 144 10 (by decide)]
  unpack_cells 10
  rcases htid_or with rfl | rfl
  ·
    have hal_c : MemWidth.isAligned .X64 C.std.threadIdCounterAddr = true :=
      isAligned64_of_mod8 hal_ctr
    refine SepWP.seq_nonVm (mid := C.std.cas8RelaxAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).stderr
    unpack_hb_code hbStderrWriteAllChunks hc_nv1
    iterate 8 (wp_steps; (try norm_jmp))
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm_a
    refine call_stdCas8 hatom.cas8Relax_ok
      (haveLse := haveLse) (ptr := C.std.threadIdCounterAddr)
      (v0 := 0#64) (exp := 0#64) (new := 1#64)
      (ret_pc := C.refStderrWriteAllAddr + 0x98#64) (F := ?_)
      (by simp only [wp_norm, arm64_norm]; sep_frame)
      (fun sa hpc_a hrun_a hsp_a hcs_a hx0_a hstd_a => ?_)
      (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      (halign := hal_c)
    simp only [beq_self_eq_true, ↓reduceIte]
    have hx0_a' : sa.readReg64 (.gpr 0#5) = 0#64 := hx0_a
    have hx19_a : sa.readReg64 (.gpr 19#5) = C.stderrGlobalAddr := by
      rw [← Reg.x19, hcs_a.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx20_a : sa.readReg64 (.gpr 20#5) = BitVec.ofNat 64 msgBytes.length := by
      rw [← Reg.x20, hcs_a.readReg64_x20]; simp [wp_norm, arm64_norm]
    have hx21_a : sa.readReg64 (.gpr 21#5) = msgPtr := by
      rw [← Reg.x21, hcs_a.readReg64_x21]; simp [wp_norm, arm64_norm]
    have hx22_a : sa.readReg64 (.gpr 22#5) = 0x58#64 := by
      rw [← Reg.x22, hcs_a.readReg64_x22]; simp [wp_norm, arm64_norm]
    have hx24_a : sa.readReg64 (.gpr 24#5) = 0#64 := by
      rw [← Reg.x24, hcs_a.readReg64_x24]; simp [wp_norm, arm64_norm]
    have hx25_a : sa.readReg64 (.gpr 25#5) = 1#64 := by
      rw [← Reg.x25, hcs_a.readReg64_x25]; simp [wp_norm, arm64_norm]
    have hx26_a : sa.readReg64 (.gpr 26#5) = s0.tpidrEl0 := by
      rw [← Reg.x26, hcs_a.readReg64_x26]; simp [wp_norm, arm64_norm]
    have hsp_a_eq : sa.sp = s0.sp - 80#64 := by rw [hsp_a]; exact wp_a
    have hsp_a_al : sa.spAligned = true := by
      simpa only [State.spAligned, hsp_a_eq] using hsp1_al
    have hhi_a : HbRefStderrHiSaved s0 sa := by
      unpack_cs hcs_a
      exact ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm]⟩
    refine SepWP.seq_nonVm (mid := C.std.cas4AcqAddr) hext hsvc ?_
    have hc_nv2 := (hc.withSvc nonVmSvc).stderr
    unpack_hb_code hbStderrWriteAllChunks hc_nv2
    wp_steps; wp_steps; norm_jmp
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun_a])
    intro hvm_b
    refine SepWP.weaken_pre ?_
      (hbRefStderrWriteAll_fromCas4_wp (refPtr := refPtr) (selfPtr := selfPtr) (msgPtr := msgPtr)
        (haveLse := haveLse) (R := R) (s0 := s0)
        ro hc hatom hal_stderr hsvc hext hlen_pos hlen_max hmsg_va
        wp_a (by simp [wp_norm, arm64_norm, hrun_a])
        (by simp [wp_norm, arm64_norm, hsp_a_eq])
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_a_al)
        wp_a wp_a wp_a wp_a wp_a wp_a wp_a wp_a wp_a
        (by rcases hhi_a with ⟨_, _, _⟩; refine ⟨by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩)
        (by simp [wp_norm, arm64_norm, hstd_a.1])
        (by simp [wp_norm, arm64_norm, hstd_a.2.1])
        (by simp [projTidSig, wp_norm, arm64_norm, hstd_a.2.2.1, hstd_a.2.2.2.1])
        ((hvm_a.trans (vmFieldsPreserved_of_stdState hstd_a)).trans hvm_b))
    dsimp only [hbRefStderrSavedRegs]; simp only [wp_norm, arm64_norm]; sep_entail
  ·
    refine SepWP.seq_nonVm (mid := C.std.cas4AcqAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).stderr
    unpack_hb_code hbStderrWriteAllChunks hc_nv1
    wp_steps; wp_steps; wp_steps; norm_jmp
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm_a
    refine SepWP.weaken_pre ?_
      (hbRefStderrWriteAll_fromCas4_wp (refPtr := refPtr) (selfPtr := selfPtr) (msgPtr := msgPtr)
        (haveLse := haveLse) (R := R) (s0 := s0)
        ro hc hatom hal_stderr hsvc hext hlen_pos hlen_max hmsg_va
        wp_a (by simp [wp_norm, arm64_norm, hrun])
        wp_a (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
        wp_a wp_a wp_a wp_a wp_a wp_a wp_a wp_a wp_a
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [projTidSig, wp_norm, arm64_norm])
        hvm_a)
    dsimp only [hbRefStderrSavedRegs]; simp only [wp_norm, arm64_norm]; sep_entail

theorem call_hbRefStderrWriteAll {P : Program} {C : HbCliLayout} {target_pc ret_pc : BitVec 64}
    (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hal_stderr : C.stderrGlobalAddr.toNat % 8 = 0)
    (hal_ctr : C.std.threadIdCounterAddr.toNat % 8 = 0)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    {refPtr selfPtr msgPtr : BitVec 64} {msgBytes : List (BitVec 8)} {haveLse : BitVec 8}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_pos : 0 < msgBytes.length)
    (hlen_max : msgBytes.length ≤ Arm64.MAX_RW_COUNT)
    (hmsg_va : msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((refPtr ↦₆₄ selfPtr) ∗
        (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        hbBytesSlice ro msgPtr msgBytes ∗
        HbThreadIdInv C s.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        stackAt s.sp 224) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stderr msgBytes →
      HbNonVmPreserved s sf →
      SepWP P target_pc sf (((refPtr ↦₆₄ selfPtr) ∗
        (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        hbBytesSlice ro msgPtr msgBytes ∗
        HbThreadIdInv C s.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        stackAt s.sp 224) ∗ F) post oom)
    (hpc : s.pc = C.refStderrWriteAllAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = refPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = msgPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (hbRefStderrWriteAllSpec ro C).onOom (refPtr, selfPtr, msgPtr, msgBytes, haveLse) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbRefStderrWriteAll_ok ro hc hatom hal_stderr hal_ctr hsvc hext)
    (x := (refPtr, selfPtr, msgPtr, msgBytes, haveLse)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [hbRefStderrWriteAllSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbRefStderrWriteAllSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hfs_f, htr_f, hnv_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f hnv_f

/-- Specification for `<std::io::stdio::Stderr as std::io::Write>::write_all`
    (`C.stderrWriteAllAddr`) over a non-empty byte slice (`0 < msgBytes.length ≤ MAX_RW_COUNT`). -/
def hbStderrWriteAllSpec (ro : Bool) (C : HbCliLayout) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 8) where
  pre := fun (selfPtr, msgPtr, msgBytes, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = selfPtr ∧
     s0.readReg64 .x1 = msgPtr ∧
     s0.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length ∧
     0 < msgBytes.length ∧
     msgBytes.length ≤ Arm64.MAX_RW_COUNT ∧
     msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    ((selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
     (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
     hbBytesSlice ro msgPtr msgBytes ∗
     HbThreadIdInv C s0.tpidrEl0 ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
     stackAt s0.sp 256)
  post := fun (selfPtr, msgPtr, msgBytes, haveLse) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
     sf.fs = s0.fs ∧
     sf.trace = s0.trace ++ TraceEvent.ofBytes .stderr msgBytes ∧
     HbNonVmPreserved s0 sf⌝ ∗
    ((selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
     (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
     hbBytesSlice ro msgPtr msgBytes ∗
     HbThreadIdInv C s0.tpidrEl0 ∗
     (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
     (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
     stackAt s0.sp 256)

theorem hbStderrWriteAll_ok {P : Program} {C : HbCliLayout} (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hal_stderr : C.stderrGlobalAddr.toNat % 8 = 0)
    (hal_ctr : C.std.threadIdCounterAddr.toNat % 8 = 0)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stderrWriteAllAddr (hbStderrWriteAllSpec ro C) := by
  apply subroutine_ok_of_sepWP_frozen
  rintro ⟨selfPtr, msgPtr, msgBytes, haveLse⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbStderrWriteAllSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hmem⟩
  have hx0' : s0.readReg64 (.gpr 0#5) = selfPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = msgPtr := hx1
  have hx2' : s0.readReg64 (.gpr 2#5) = BitVec.ofNat 64 msgBytes.length := hx2
  have hsp1_al : (s0.sp - 32#64) &&& 15#64 == 0#64 := by
    simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x20#64 hsp_align
  refine ⟨stackAt s0.sp 256 ∗
      (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
      hbBytesSlice ro msgPtr msgBytes ∗
      HbThreadIdInv C s0.tpidrEl0 ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse),
    by sep_frame, ?_⟩
  conv =>
    arg 4
    rw [show (256 : Nat) = 224 + 8 * 4 from rfl,
        stackAt_split_cells s0.sp 224 4 (by decide)]
  unpack_cells 4
  refine SepWP.seq_nonVm (mid := C.refStderrWriteAllAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv1
  wp_steps; wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine call_hbRefStderrWriteAll ro hc hatom hal_stderr hal_ctr hsvc hext hlen_pos hlen_max hmsg_va
    (ret_pc := C.stderrWriteAllAddr + 0x18#64)
    (refPtr := s0.sp - 24#64) (selfPtr := selfPtr)
    (msgPtr := msgPtr) (msgBytes := msgBytes) (haveLse := haveLse) (F := ?_)
    (by simp only [wp_norm, arm64_norm]; sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hfs2 htr2 hnv2 => ?_)
    (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
    (hx0 := by simp [wp_norm, arm64_norm])
    (hx1 := by simp [wp_norm, arm64_norm, hx1'])
    (hx2 := by simp [wp_norm, arm64_norm, hx2'])
  have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
  have hsp2_eq : s2.sp = s0.sp - 32#64 := by rw [hsp2]; exact wp_a
  have hsp2_al : s2.spAligned = true := by
    simpa only [State.spAligned, hsp2_eq] using hsp1_al
  refine SepWP.of_nonVm hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).stderr
  unpack_hb_code hbStderrWriteAllChunks hc_nv2
  wp_steps
  refine SepWP.weaken_pre_frame
    (P' := (selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
      hbBytesSlice ro msgPtr msgBytes ∗
      HbThreadIdInv C s0.tpidrEl0 ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      stackAt s0.sp 256)
    (fun _ hm' => by
      rw [show (256 : Nat) = 224 + 8 * 4 from rfl,
          stackAt_split_cells s0.sp 224 4 (by decide)]
      simp only [wp_norm, arm64_norm] at hm' ⊢
      cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail) ?_
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
  intro hvm2
  refine ⟨fun hkf hmf => ?_, by simp [wp_norm, arm64_norm],
    by unpack_cs hcs2; close_cs⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hvm_sf := (hvm1.trans hnv2.vm).trans hvm2
  refine ⟨⟨by simp [wp_norm, arm64_norm, hx0_2'], ?_, ?_, hbNonVmPreserved_of_parts ?_ hvm_sf hkf⟩, hmf⟩
  · simp only [wp_norm, arm64_norm]; rw [hfs2]; simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm]; rw [htr2]; simp only [wp_norm, arm64_norm]
  · simp only [projTidSig, wp_norm, arm64_norm]
    rw [hnv2.tpidrEl0_eq, hnv2.sigActions_eq]; simp only [wp_norm, arm64_norm]

theorem call_hbStderrWriteAll {P : Program} {C : HbCliLayout} {target_pc ret_pc : BitVec 64}
    (ro : Bool)
    (hc : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hal_stderr : C.stderrGlobalAddr.toNat % 8 = 0)
    (hal_ctr : C.std.threadIdCounterAddr.toNat % 8 = 0)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    {selfPtr msgPtr : BitVec 64} {msgBytes : List (BitVec 8)} {haveLse : BitVec 8}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_pos : 0 < msgBytes.length)
    (hlen_max : msgBytes.length ≤ Arm64.MAX_RW_COUNT)
    (hmsg_va : msgPtr.toNat + msgBytes.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        hbBytesSlice ro msgPtr msgBytes ∗
        HbThreadIdInv C s.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        stackAt s.sp 256) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stderr msgBytes →
      HbNonVmPreserved s sf →
      SepWP P target_pc sf (((selfPtr ↦₆₄ C.stderrGlobalAddr) ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        hbBytesSlice ro msgPtr msgBytes ∗
        HbThreadIdInv C s.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        stackAt s.sp 256) ∗ F) post oom)
    (hpc : s.pc = C.stderrWriteAllAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = selfPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = msgPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 msgBytes.length := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (hbStderrWriteAllSpec ro C).onOom (selfPtr, msgPtr, msgBytes, haveLse) s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbStderrWriteAll_ok ro hc hatom hal_stderr hal_ctr hsvc hext)
    (x := (selfPtr, msgPtr, msgBytes, haveLse)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm; dsimp only [hbStderrWriteAllSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen_pos, hlen_max, hmsg_va⟩, hpre R hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbStderrWriteAllSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hfs_f, htr_f, hnv_f⟩
    exact hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hfs_f htr_f hnv_f

end CaseStudies.Hashbrown.Proofs.StdCli
