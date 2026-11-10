/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.StdStartup.NonVmSteps
public import ProofLib.StdStartup.MemOps

/-!
# Process File-System Lemmas and Syscall `SepWP` Rules

Algebraic simplification lemmas for `FsState`, `SepWP` symbolic-execution rules for `openat`,
`fcntl`, `fstat`, and `write`, and pure characterizations of relative-path `execOpenat` calls.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib

open Arm64 Arm64.Process ProofLib.StdStartup

/-! ## File-System State and Trace Lemmas -/

@[simp]
theorem _root_.Arm64.Process.FsState.setEntry_setEntry_same
    (fs : FsState) (p : FsPath) (e1 e2 : Option FsEntry) :
    (fs.setEntry p e1).setEntry p e2 = fs.setEntry p e2 := by
  cases fs
  simp only [FsState.setEntry, FsState.mk.injEq, and_true]
  funext q
  by_cases h : (q == p) = true <;> simp [h]

@[simp]
theorem _root_.Arm64.Process.FsState.setFile_setFile_same
    (fs : FsState) (p : String) (e1 e2 : Option FsEntry) :
    (fs.setFile p e1).setFile p e2 = fs.setFile p e2 :=
  FsState.setEntry_setEntry_same fs (normalizePath p) e1 e2

theorem _root_.Arm64.Process.FsState.setFd_setEntry_comm
    (fs : FsState) (fd : BitVec 64) (d : Option FdEntry) (p : FsPath) (e : Option FsEntry) :
    (fs.setFd fd d).setEntry p e = (fs.setEntry p e).setFd fd d := by
  cases fs; rfl

theorem _root_.Arm64.Process.FsState.setFd_setFile_comm
    (fs : FsState) (fd : BitVec 64) (d : Option FdEntry) (p : String) (e : Option FsEntry) :
    (fs.setFd fd d).setFile p e = (fs.setFile p e).setFd fd d := by
  cases fs; rfl

theorem _root_.Arm64.Process.FsState.setFd_eq_self
    {fs : FsState} {fd : BitVec 64} {d : Option FdEntry} (h : fs.fds fd = d) :
    fs.setFd fd d = fs := by
  cases fs
  simp only [FsState.setFd, FsState.mk.injEq, true_and]
  funext k
  by_cases hk : k = fd
  · subst hk; simp only [beq_self_eq_true, ↓reduceIte]; exact h.symm
  · simp [hk]

theorem _root_.Arm64.Process.FsState.setFd_none_of_eq_none
    {fs : FsState} {fd : BitVec 64} (h : fs.fds fd = none) :
    fs.setFd fd none = fs :=
  FsState.setFd_eq_self h

theorem _root_.Arm64.Process.FsState.setEntry_self_of_nonEmpty
    {fs : FsState} {segs : FsPath} {e : Option FsEntry}
    (hne : segs ≠ []) (h : fs.getEntry segs = e) :
    fs.setEntry segs e = fs := by
  cases fs with
  | mk entries stdin fds =>
    simp only [FsState.getEntry] at h
    have hemp : segs.isEmpty = false := by cases segs with | nil => contradiction | cons _ _ => rfl
    rw [hemp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    simp only [FsState.setEntry, FsState.mk.injEq, and_true]
    funext q
    by_cases hq : (q == segs) = true
    · rw [eq_of_beq hq]; simp [h]
    · simp [hq]

private theorem foldl_setEntry_fds {α : Type} (f : FsState → α → FsState)
    (hf : ∀ fs x, (f fs x).fds = fs.fds) :
    ∀ (l : List α) (fs : FsState), (l.foldl f fs).fds = fs.fds
  | [], _ => rfl
  | x :: xs, fs => (foldl_setEntry_fds f hf xs (f fs x)).trans (hf fs x)

theorem initFsState_fds_ge3 (inputs : ProcessInputs) {fd : BitVec 64} (hge : 3 ≤ fd.toNat) :
    (initFsState inputs).fds fd = none := by
  unfold initFsState
  have hne0 : (fd == 0#64) = false := beq_false_of_ne (fun h => by subst h; simp at hge)
  have hne1 : (fd == 1#64) = false := beq_false_of_ne (fun h => by subst h; simp at hge)
  have hne2 : (fd == 2#64) = false := beq_false_of_ne (fun h => by subst h; simp at hge)
  simp only [FsState.setFd, hne2, hne1, hne0, Bool.false_eq_true, ↓reduceIte]
  have hf_dirs : ∀ (fs : FsState) (_d : String),
      ((FsPath.nonEmptyPrefixes (normalizePath _d)).foldl
        (fun (acc : FsState) pref => acc.setEntry pref (some .dir)) fs).fds = fs.fds :=
    fun fs _d => foldl_setEntry_fds (fun (acc : FsState) pref => acc.setEntry pref (some .dir))
      (fun _ _ => rfl) _ fs
  have hf_files : ∀ (fs : FsState) (pb : String × List (BitVec 8)),
      (let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath pb.1)).dropLast).foldl
        (fun (acc : FsState) pref => acc.setEntry pref (some .dir)) fs
       withAnc.setFile pb.1 (some (.file pb.2))).fds = fs.fds := by
    intro fs ⟨p, bs⟩
    dsimp only [FsState.setFile, FsState.setEntry]
    exact foldl_setEntry_fds (fun (acc : FsState) pref => acc.setEntry pref (some .dir))
      (fun _ _ => rfl) _ fs
  rw [foldl_setEntry_fds _ hf_files inputs.files _,
      foldl_setEntry_fds _ hf_dirs inputs.dirs _]

theorem initFsState_allocFd (inputs : ProcessInputs) :
    (initFsState inputs).allocFd = some 3#64 := by
  unfold FsState.allocFd
  have hr : List.range (FsState.maxOpenFds - 3) = 0 :: (List.range 1020).map (· + 1) := by
    change List.range 1021 = 0 :: (List.range 1020).map (· + 1)
    exact List.range_succ_eq_map (n := 1020)
  rw [hr, List.find?_cons]
  have h3 : (initFsState inputs).fds 3#64 = none := initFsState_fds_ge3 inputs (by decide)
  simp [h3]

private theorem foldl_dir_no_file :
    ∀ (prefs : List FsPath) (fs : FsState) {q : FsPath} {bs : List (BitVec 8)},
      (prefs.foldl (fun (acc : FsState) pref => acc.setEntry pref (some .dir)) fs).getEntry q =
        some (.file bs) →
      fs.getEntry q = some (.file bs)
  | [], _, _, _, h => h
  | pref :: rest, fs, q, _bs, h => by
    have h' := foldl_dir_no_file rest (fs.setEntry pref (some .dir)) h
    simp only [FsState.getEntry, FsState.setEntry] at h' ⊢
    by_cases hemp : q.isEmpty = true
    · simp [hemp] at h'
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at h' ⊢
      by_cases hqp : (q == pref) = true
      · simp [hqp] at h'
      · simpa [hqp] using h'

private theorem withDirs_no_file :
    ∀ (ds : List String) (fs : FsState) {q : FsPath} {bs : List (BitVec 8)},
      (ds.foldl (fun (acc : FsState) d =>
        (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun (a : FsState) pref => a.setEntry pref (some .dir)) acc) fs).getEntry q =
        some (.file bs) →
      fs.getEntry q = some (.file bs)
  | [], _, _, _, h => h
  | _d :: ds, fs, _q, _bs, h =>
    foldl_dir_no_file _ fs (withDirs_no_file ds _ h)

private theorem withFiles_file_mem :
    ∀ (fls : List (String × List (BitVec 8))) (fs : FsState) {q : FsPath} {bs : List (BitVec 8)},
      (fls.foldl (fun (acc : FsState) (p, b) =>
        let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
          (fun (a : FsState) pref => a.setEntry pref (some .dir)) acc
        withAnc.setFile p (some (.file b))) fs).getEntry q = some (.file bs) →
      fs.getEntry q = some (.file bs) ∨ ∃ p, (p, bs) ∈ fls
  | [], _, _, _, h => Or.inl h
  | (p, b) :: fls, fs, q, bs, h => by
    rcases withFiles_file_mem fls _ h with hstep | ⟨p', hp'⟩
    · simp only [FsState.setFile, FsState.getEntry, FsState.setEntry] at hstep
      by_cases hemp : q.isEmpty = true
      · simp [hemp] at hstep
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases hqp : (q == normalizePath p) = true
        · simp only [hqp, ↓reduceIte, Option.some.injEq, FsEntry.file.injEq] at hstep
          subst hstep
          exact Or.inr ⟨p, List.mem_cons_self ..⟩
        · simp only [hqp, Bool.false_eq_true, ↓reduceIte] at hstep
          have hanc :
              (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
                (fun (a : FsState) pref => a.setEntry pref (some .dir)) fs).getEntry q =
                some (.file bs) := by
            simp only [FsState.getEntry, FsState.setEntry, hemp, Bool.false_eq_true, ↓reduceIte]
            exact hstep
          exact Or.inl (foldl_dir_no_file _ fs hanc)
    · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp'⟩

theorem initFsState_files_file_mem {inputs : ProcessInputs} {q : String} {bs : List (BitVec 8)}
    (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, (p, bs) ∈ inputs.files := by
  have hwf :
      (inputs.files.foldl (fun (fs : FsState) (p, bs) =>
        let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
          (fun (acc : FsState) pref => acc.setEntry pref (some .dir)) fs
        withAnc.setFile p (some (.file bs)))
        (inputs.dirs.foldl (fun (fs : FsState) d =>
          (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
            (fun (acc : FsState) pref => acc.setEntry pref (some .dir)) fs) ({} : FsState))).getEntry
        (normalizePath q) = some (.file bs) := by
    unfold initFsState FsState.files at h
    simpa [FsState.setFd, FsState.getEntry] using h
  rcases withFiles_file_mem inputs.files _ hwf with hdirs | hmem
  · have hempty := withDirs_no_file inputs.dirs ({} : FsState) hdirs
    unfold FsState.getEntry at hempty
    cases hq : (normalizePath q).isEmpty <;> simp [hq] at hempty
  · exact hmem

theorem initFsState_filesLeMaxLfs {inputs : ProcessInputs}
    (hfiles : (inputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE))) = false) :
    (initFsState inputs).FilesLeMaxLfs := by
  intro q bs hq
  obtain ⟨p, hmem⟩ := initFsState_files_file_mem hq
  refine Classical.byContradiction fun hgt => ?_
  have htrue : (inputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE))) = true :=
    List.any_eq_true.mpr ⟨(p, bs), hmem, by simp [decide_eq_false hgt]⟩
  rw [hfiles] at htrue; cases htrue

theorem loadState_filesLeMaxLfs {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hload : img.loadState inputs = .ok s0) :
    s0.fs.FilesLeMaxLfs := by
  unfold ElfImage.loadState at hload
  by_cases hwf : (!img.WellFormed) = true
  · simp [Bind.bind, Except.bind, hwf] at hload
  · by_cases hdirs : (inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d)) = true
    · simp [Bind.bind, Except.bind, hwf, hdirs] at hload
    · by_cases hfiles : (inputs.files.any (fun (p, bs) =>
          hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE))) = true
      · simp [Bind.bind, Except.bind, hwf, hdirs, hfiles] at hload
      · simp only [Bool.not_eq_true] at hwf hdirs hfiles
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
          hwf, hdirs, hfiles, Bool.false_eq_true, ↓reduceIte] at hload
        cases hbuild : buildInitialStack img inputs with
        | error e => rw [hbuild] at hload; cases hload
        | ok pair =>
          rw [hbuild] at hload
          injection hload with hs0
          subst hs0
          exact initFsState_filesLeMaxLfs hfiles

private theorem foldl_max_ge :
    ∀ (fls : List (String × List (BitVec 8))) (acc : Nat),
      acc ≤ fls.foldl (fun a (_, b) => max a b.length) acc ∧
      (∀ p bs, (p, bs) ∈ fls → bs.length ≤ fls.foldl (fun a (_, b) => max a b.length) acc)
  | [], acc => ⟨Nat.le_refl _, by nofun⟩
  | (_p0, b0) :: fls, acc => by
    obtain ⟨hle, hmem⟩ := foldl_max_ge fls (max acc b0.length)
    refine ⟨Nat.le_trans (Nat.le_max_left ..) hle, fun p bs hm => ?_⟩
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq; exact Nat.le_trans (Nat.le_max_right ..) hle
    · exact hmem p bs htl

theorem foldl_max_file_bytes_ge {fls : List (String × List (BitVec 8))} {p : String}
    {bs : List (BitVec 8)} (h : (p, bs) ∈ fls) :
    bs.length ≤ fls.foldl (fun acc (_, b) => max acc b.length) 0 :=
  (foldl_max_ge fls 0).2 p bs h

@[simp]
theorem writeFileBytes_nil_zero (bs : List (BitVec 8)) :
    writeFileBytes [] 0 bs = bs := by
  unfold writeFileBytes; simp

theorem writeFileBytes_append_at_end (old chunk : List (BitVec 8)) :
    writeFileBytes old old.length chunk = old ++ chunk := by
  unfold writeFileBytes
  simp [List.take_length, List.drop_eq_nil_of_le (Nat.le_add_right old.length chunk.length)]

@[simp]
theorem traceStreamBytes_fileChanged (stream : OutputStream) (p : String) :
    ProcessOutcome.traceStreamBytes stream [.fileChanged p] = [] := rfl

theorem traceStreamBytes_stdout_fd_ofBytes (fd : BitVec 64)
    (h1 : fd ≠ 1#64) (h2 : fd ≠ 2#64) (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes (OutputStream.ofFd fd) bs) = [] := by
  have hof : OutputStream.ofFd fd = .fd fd := by
    unfold OutputStream.ofFd; simp [beq_false_of_ne h1, beq_false_of_ne h2]
  rw [hof]; induction bs with | nil => rfl | cons _ _ ih => exact ih

theorem traceStreamBytes_stderr_fd_ofBytes (fd : BitVec 64)
    (h1 : fd ≠ 1#64) (h2 : fd ≠ 2#64) (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes (OutputStream.ofFd fd) bs) = [] := by
  have hof : OutputStream.ofFd fd = .fd fd := by
    unfold OutputStream.ofFd; simp [beq_false_of_ne h1, beq_false_of_ne h2]
  rw [hof]; induction bs with | nil => rfl | cons _ _ ih => exact ih

/-! ## Syscall `SepWP` Step Rules -/

theorem cstrBytes_eq_bytesOfString (path : String) :
    cstrBytes path = bytesOfString path ++ [0#8] := rfl

private theorem readCStringAux_of_bytesRW {m : Memory} {ptr : BitVec 64} {R : SepProp} :
    ∀ (cs : List Char) (fuel : Nat) (acc : List Char),
      cs.length < fuel →
      (∀ c ∈ cs, c.toNat < 256 ∧ c.toNat ≠ 0) →
      m ⊨ (ptr ↦ₛ (cs.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])) ∗ R →
      readCStringAux m ptr fuel acc = .ok (String.ofList (acc.reverse ++ cs))
  | [], _ + 1, acc, _, _, hm => by
    simp only [List.map_nil, List.nil_append, pointsToBytes_singleton] at hm
    have hc : m.canRead ptr 1 = true := (IsBlock.pointsTo8 ptr 0#8).canRead (by decide) hm
    have hp : (m.perm ptr).r = true := by
      simpa [Memory.allPerm] using Memory.allPerm_r_of_canRead hc
    have hr : m.read8 ptr = 0#8 := (IsBlock.pointsTo8 ptr 0#8).read hm
    simp [readCStringAux, hp, hc, hr]
  | c :: cs, fuel + 1, acc, hfuel, hcs, hm => by
    have ⟨hc_lt, hc_ne⟩ := hcs c (List.mem_cons_self ..)
    have hbv_ne : BitVec.ofNat 8 c.toNat ≠ 0#8 := by
      intro h
      exact hc_ne (by
        have := congrArg BitVec.toNat h
        simpa [Nat.mod_eq_of_lt hc_lt] using this)
    have hbv_eq : (BitVec.ofNat 8 c.toNat == 0#8) = false := beq_false_of_ne hbv_ne
    simp only [List.map_cons, List.cons_append, pointsToBytes_cons, sepConj_assoc] at hm
    have hc : m.canRead ptr 1 = true := (IsBlock.pointsTo8 ptr _).canRead (by decide) hm
    have hp : (m.perm ptr).r = true := by
      simpa [Memory.allPerm] using Memory.allPerm_r_of_canRead hc
    have hr : m.read8 ptr = BitVec.ofNat 8 c.toNat := (IsBlock.pointsTo8 ptr _).read hm
    have hm_tail : m ⊨ ((ptr + 1#64) ↦ₛ (cs.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])) ∗
        ((ptr ↦₈ BitVec.ofNat 8 c.toNat) ∗ R) := by
      rw [sepConj_left_comm] at hm; exact hm
    have hchr : Char.ofNat (BitVec.ofNat 8 c.toNat).toNat = c := by
      simp [Nat.mod_eq_of_lt hc_lt]
    rw [readCStringAux]
    simp only [hp, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr, hbv_eq, hchr]
    rw [readCStringAux_of_bytesRW cs fuel (c :: acc) (by simp at hfuel; omega)
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hm_tail]
    simp [List.reverse_cons, List.append_assoc]

/-- Reading a NUL-terminated string from an RW byte slice `(ptr ↦ₛ cstrBytes path) ∗ R`. -/
theorem readCString_of_pointsToBytes {m : Memory} {ptr : BitVec 64} {path : String} {R : SepProp}
    (hlen : path.toList.length < PATH_MAX)
    (hvalid : ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0)
    (hm : m ⊨ (ptr ↦ₛ cstrBytes path) ∗ R) :
    readCString m ptr = .ok path := by
  unfold readCString cstrBytes at *
  simpa using readCStringAux_of_bytesRW path.toList PATH_MAX [] hlen hvalid hm

private theorem state_setPC_eq_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.setPC pc = s := by
  cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm

private theorem state_advancePC_eq_setPC {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.advancePC = s.setPC (pc + 4#64) := by
  subst hpc; rfl

private theorem readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    simpa [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by omega : 2 ^ 32 < 2 ^ 64))] using hlt
  unfold BitVec.slt BitVec.toInt
  simp; omega

private theorem mem_execOpenat_rw (s : State) : (execOpenat s).mem = s.mem := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;> (cases s; rfl)

/-- `SVC #0` rule for `openat` (`X8 = 56`) when `X1` points to an RW NUL-terminated string `path`. -/
theorem step_svc_openat_rw {prog : Program} {target_pc : BitVec 64}
    {s : State} {path : String} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc fname : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 56#64)
    (hfname : s.readReg64 .x1 = fname)
    (hlen : path.toList.length < PATH_MAX)
    (hvalid : ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0)
    (hnext : readCString s.mem (s.readReg64 .x1) = .ok path →
      SepWP prog target_pc (execOpenat s) ((fname ↦ₛ cstrBytes path) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execOpenat s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s ((fname ↦ₛ cstrBytes path) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hm' : s.mem ⊨ (fname ↦ₛ cstrBytes path) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcs : readCString s.mem (s.readReg64 .x1) = .ok path := by
    rw [hfname]; exact readCString_of_pointsToBytes hlen hvalid hm'
  exact SepWP.to_reaches_pc
    (SepWP.step_pure hpc hrun hfetch (by rw [hpc_eq, hsvc]) (mem_execOpenat_rw s) (hnext hcs)) hm

/-- `execFcntl` reduction for `F_GETFD` (`cmd = 1`) on an open `.localFile` or `.localDir`
    descriptor. -/
theorem execFcntl_getfd {s : State} {fd : BitVec 64} {desc : FdEntry}
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hcmd : s.readReg32 .x1 = F_GETFD_W32)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir) :
    execFcntl s = (s.writeReg64 .x0 (if desc.cloexec then 1#64 else 0#64)).advancePC := by
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hget : (F_GETFD_W32 == F_GETFD_W32) = true := by decide
  dsimp only [execFcntl]
  rw [hslt, hfd, hopen]; dsimp only
  rcases hkind with hk | hk <;> (rw [hk, hcmd, hget]; rfl)

/-- `execFcntl` reduction for `F_SETFD` (`cmd = 2`) on an open `.localFile` or `.localDir`
    descriptor. -/
theorem execFcntl_setfd {s : State} {fd arg : BitVec 64} {desc : FdEntry}
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31)
    (hcmd : s.readReg32 .x1 = F_SETFD_W32)
    (harg : s.readReg64 .x2 = arg)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir) :
    execFcntl s =
      ((s.setFs (s.fs.setFd fd (some { desc with cloexec := (arg &&& 1#64) != 0#64 }))).writeReg64
        .x0 0#64).advancePC := by
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hget : (F_SETFD_W32 == F_GETFD_W32) = false := by decide
  have hset : (F_SETFD_W32 == F_SETFD_W32) = true := by decide
  dsimp only [execFcntl]
  rw [hslt, hfd, hopen]; dsimp only
  rcases hkind with hk | hk <;> (rw [hk, hcmd, harg, hget, hset]; rfl)

/-- `SVC #0` rule for `fcntl(fd, F_GETFD = 1, _)` (`X8 = 25`) on an open `.localFile` or
    `.localDir` descriptor. -/
theorem step_svc_fcntl_getfd_local {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 25#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hcmd : s.readReg32 .x1 = F_GETFD_W32)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir := by
      first | exact Or.inl rfl | exact Or.inr rfl)
    (hnext :
      let s' := (s.writeReg64 .x0 (if desc.cloexec then 1#64 else 0#64)).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execFcntl s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  refine SepWP.step_pure hpc hrun hfetch (by rw [hpc_eq, hsvc])
    (by dsimp only [execFcntl]; (repeat' split) <;> (cases s; rfl)) ?_
  rw [execFcntl_getfd hfd hfd_lt hcmd hopen hkind,
      state_advancePC_eq_setPC (pc := pc) (by simp [hpc])]
  exact hnext

/-- `SVC #0` rule for `fcntl(fd, F_SETFD = 2, arg)` (`X8 = 25`) on an open `.localFile` or
    `.localDir` descriptor. -/
theorem step_svc_fcntl_setfd_local {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd arg : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 25#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hcmd : s.readReg32 .x1 = F_SETFD_W32)
    (harg : s.readReg64 .x2 = arg)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile ∨ desc.kind = .localDir := by
      first | exact Or.inl rfl | exact Or.inr rfl)
    (hnext :
      let fs' := s.fs.setFd fd (some { desc with cloexec := (arg &&& 1#64) != 0#64 })
      let s' := ((s.setFs fs').writeReg64 .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execFcntl s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  refine SepWP.step_pure hpc hrun hfetch (by rw [hpc_eq, hsvc])
    (by dsimp only [execFcntl]; (repeat' split) <;> (cases s; rfl)) ?_
  rw [execFcntl_setfd hfd hfd_lt hcmd harg hopen hkind,
      state_advancePC_eq_setPC (pc := pc) (by simp [hpc])]
  exact hnext

/-- `SVC #0` rule for `fcntl(fd, F_SETFD = 2, arg)` (`X8 = 25`) on an open `.localFile` descriptor. -/
theorem step_svc_fcntl_setfd {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd arg : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 25#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hcmd : s.readReg32 .x1 = F_SETFD_W32)
    (harg : s.readReg64 .x2 = arg)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile := by rfl)
    (hnext :
      let fs' := s.fs.setFd fd (some { desc with cloexec := (arg &&& 1#64) != 0#64 })
      let s' := ((s.setFs fs').writeReg64 .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execFcntl s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom :=
  step_svc_fcntl_setfd_local hpc hrun hfetch hx8 hfd hfd_lt hcmd harg hopen (Or.inl hkind) hnext hsvc

/-- `SVC #0` rule for `fstat(fd, statbuf)` (`X8 = 80`) on an open `.localFile` descriptor,
    writing the 128-byte `encodeLinuxStat entry` into `(statbuf ↦ₛ bs₀)` (`bs₀.length = 128`). -/
theorem step_svc_fstat_file {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd statbuf : BitVec 64} {desc : FdEntry} {bs₀ : List (BitVec 8)}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 80#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = statbuf)
    (hlen : bs₀.length = 128)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile := by rfl)
    (hnext :
      let entry := (s.fs.files desc.path).getD (.file [])
      let s' := ((s.setMem (s.mem.writeBytes statbuf (encodeLinuxStat entry))).writeReg64
        .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s' ((statbuf ↦ₛ encodeLinuxStat entry) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execFstat s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s ((statbuf ↦ₛ bs₀) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hm' : s.mem ⊨ (statbuf ↦ₛ bs₀) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw : s.mem.canWrite statbuf 128 = true := by
    rw [← hlen]
    exact (IsBlock.pointsToBytes statbuf bs₀).canWrite
      ((IsBlock.pointsToBytes statbuf bs₀).read hm').1 hm'
  have henc_len : (encodeLinuxStat ((s.fs.files desc.path).getD (.file []))).length = 128 := by
    cases (s.fs.files desc.path).getD (.file []) <;>
      simp [encodeLinuxStat, leBytes64, leBytes32]
  refine SepWP.to_reaches_pc
    (SepWP.step_writeBytes_exact hpc hrun hfetch ?_ rfl (henc_len.trans hlen.symm) hnext) hm
  refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
  rw [hpc_eq, hsvc]
  dsimp only [execFstat]
  rw [hslt, hfd, hbuf, hopen]; dsimp only
  rw [hkind, hcw]; rfl

/-- `SVC #0` rule for `write` (`X8 = 64`) of a read-only slice `buf ↦ᵣ bs`
    (`bs.length = min count.toNat MAX_RW_COUNT`) to `stdout` (`fd = 1`) or `stderr` (`fd = 2`). -/
theorem step_svc_write_stdio_ro_clamped {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (isOut : Bool) {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 64#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = (if isOut then 1#64 else 2#64))
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs.length = min count.toNat Arm64.MAX_RW_COUNT)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64))
      ((buf ↦ᵣ bs) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s := by
      simp [wp_norm, arm64_norm, Reg.x8, *])
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega) :
    SepWP prog target_pc s ((buf ↦ᵣ bs) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm' : s.mem ⊨ (buf ↦ᵣ bs) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hlen64 : bs.length ≤ 2 ^ 64 := by
    rw [hlen]; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_lt count.isLt)
  have hblk := IsBlockRO.pointsToBytesRO buf bs hlen64
  have hcr : s.mem.canRead buf (min count.toNat Arm64.MAX_RW_COUNT) = true := by
    rw [← hlen]; exact hblk.canRead hlen64 hm'
  have hrd : s.mem.readBytes buf (min count.toNat Arm64.MAX_RW_COUNT) = bs := by
    rw [← hlen]; exact hblk.read hm'
  have hslt : (s.readReg32 .x0).slt 0#32 = false :=
    readReg32_slt_zero_false hfd (by cases isOut <;> decide)
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have hexec : execWrite s =
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64)) := by
    refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
    dsimp only [execWrite]
    rw [hslt, hfd, hbuf, hcnt]
    by_cases h0 : count = 0#64
    · subst h0
      have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hbs0
      have hnotva : ¬ (Arm64.USER_VA_LIMIT < buf.toNat) := by
        simpa using Nat.not_lt.mpr hva
      cases isOut <;> simp [hnotva, TraceEvent.ofBytes, State.appendTrace]
    · have h0_f : (count == 0#64) = false := beq_false_of_ne h0
      cases isOut <;> (simp only [beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte,
        hva_f, h0_f, hcr, hrd, Bool.false_eq_true, OutputStream.ofFd]; try rfl)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

/-- `SVC #0` rule for `write` (`X8 = 64`) of a read-only slice `buf ↦ᵣ bs` to `stdout` (`fd = 1`)
    or `stderr` (`fd = 2`). -/
theorem step_svc_write_stdio_ro {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (isOut : Bool) {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 64#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = (if isOut then 1#64 else 2#64))
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs.length = count.toNat)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 count).setPC (pc + 4#64))
      ((buf ↦ᵣ bs) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s := by
      simp [wp_norm, arm64_norm, Reg.x8, *])
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega) :
    SepWP prog target_pc s ((buf ↦ᵣ bs) ∗ F) post oom := by
  refine step_svc_write_stdio_ro_clamped isOut hpc hrun hfetch _hx8 hfd hbuf hcnt
    (by rw [Nat.min_eq_left hmax]; exact hlen) ?_ hsvc hva
  simpa only [Nat.min_eq_left hmax, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hnext

/-- `SVC #0` rule for `write` (`X8 = 64`) of an owned slice `buf ↦ₛ bs`
    (`bs.length = min count.toNat MAX_RW_COUNT`, `count > 0`) to an open writable `.localFile`
    descriptor `fd ≥ 3` (`append = false`). -/
theorem step_svc_write_file_clamped {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {bs : List (BitVec 8)}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 64#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_ge : 3 ≤ fd.toNat := by omega)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hnz : count ≠ 0#64)
    (hlen : bs.length = min count.toNat Arm64.MAX_RW_COUNT)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile := by rfl)
    (hwr : desc.accMode.canWrite = true)
    (happ : desc.append = false := by rfl)
    (hlfs : desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
      simp only [Arm64.MAX_LFS_FILESIZE, Arm64.FS_SAFE_MAX_FILESIZE] at *; omega)
    (hnext :
      let count' := min count.toNat Arm64.MAX_RW_COUNT
      let oldBytes := match s.fs.files desc.path with | some (.file b) => b | _ => []
      let newBytes := writeFileBytes oldBytes desc.offset bs
      let fs' := (s.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + count' })
      let s' := (((s.setFs fs').appendTrace (TraceEvent.ofBytes (OutputStream.ofFd fd) bs)).writeReg64
        .x0 (BitVec.ofNat 64 count')).setPC (pc + 4#64)
      SepWP prog target_pc s' ((buf ↦ₛ bs) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s := by
      simp [wp_norm, arm64_norm, Reg.x8, *])
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega)
    (hext4 : desc.offset + min count.toNat Arm64.MAX_RW_COUNT ≤ Arm64.FS_SAFE_MAX_FILESIZE := by
      simp only [Arm64.FS_SAFE_MAX_FILESIZE] at *; omega) :
    SepWP prog target_pc s ((buf ↦ₛ bs) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm' : s.mem ⊨ (buf ↦ₛ bs) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hblk := IsBlock.pointsToBytes buf bs
  have hlen64 : bs.length ≤ 2 ^ 64 := by
    rw [hlen]; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_lt count.isLt)
  have hcr : s.mem.canRead buf (min count.toNat Arm64.MAX_RW_COUNT) = true := by
    rw [← hlen]; exact hblk.canRead hlen64 hm'
  have hrd : s.mem.readBytes buf (min count.toNat Arm64.MAX_RW_COUNT) = bs := by
    rw [← hlen]; exact (hblk.read hm').2
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hne1 : (fd == 1#64) = false := beq_false_of_ne (fun h => by subst h; simp at hfd_ge)
  have hne2 : (fd == 2#64) = false := beq_false_of_ne (fun h => by subst h; simp at hfd_ge)
  have hcnt0 : (count == 0#64) = false := beq_false_of_ne hnz
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  cases desc with
  | mk dpath dacc dapp dclo doff dkind =>
    dsimp only at hkind hwr happ hlfs hext4 hnext
    subst hkind happ
    have hk_dir : (FdKind.localFile == FdKind.localDir) = false := rfl
    have hk_ne : (FdKind.localFile != FdKind.localFile) = false := rfl
    have hexec : execWrite s =
        ((((s.setFs ((s.fs.setFile dpath (some (.file
            (writeFileBytes (match s.fs.files dpath with | some (.file b) => b | _ => []) doff bs)))).setFd
            fd (some { path := dpath, accMode := dacc, append := false, cloexec := dclo,
                       offset := doff + min count.toNat Arm64.MAX_RW_COUNT, kind := .localFile }))).appendTrace
          (TraceEvent.ofBytes (OutputStream.ofFd fd) bs)).writeReg64
            .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64)) := by
      refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
      dsimp only [execWrite, FsState.fileBytes, FsState.writePos]
      rw [hslt, hfd, hne1, hne2, hopen]; dsimp only
      rw [hk_dir, hk_ne, hwr, hbuf, hcnt, hva_f, hcnt0, hcr, hrd]
      have hlfs_min : doff + min count.toNat Arm64.MAX_RW_COUNT ≤ Arm64.MAX_LFS_FILESIZE := by omega
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        gt_iff_lt, Nat.not_lt.mpr hlfs, Nat.not_lt.mpr hlfs_min, Nat.not_lt.mpr hext4, decide_false]; rfl
    apply reaches_pc_step hrun (hpc ▸ hfetch)
    rw [hsvc, hexec]
    exact SepWP.to_reaches_pc hnext (by simpa using hm)

/-- `SVC #0` rule for `write` (`X8 = 64`) of an owned slice `buf ↦ₛ bs` (`count > 0`) to an open
    writable `.localFile` descriptor `fd ≥ 3` (`append = false`). -/
theorem step_svc_write_file {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {bs : List (BitVec 8)}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 64#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_ge : 3 ≤ fd.toNat := by omega)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hnz : count ≠ 0#64)
    (hlen : bs.length = count.toNat)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile := by rfl)
    (hwr : desc.accMode.canWrite = true)
    (happ : desc.append = false := by rfl)
    (hlfs : desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
      simp only [Arm64.MAX_LFS_FILESIZE, Arm64.FS_SAFE_MAX_FILESIZE] at *; omega)
    (hnext :
      let oldBytes := match s.fs.files desc.path with | some (.file b) => b | _ => []
      let newBytes := writeFileBytes oldBytes desc.offset bs
      let fs' := (s.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + count.toNat })
      let s' := (((s.setFs fs').appendTrace (TraceEvent.ofBytes (OutputStream.ofFd fd) bs)).writeReg64
        .x0 count).setPC (pc + 4#64)
      SepWP prog target_pc s' ((buf ↦ₛ bs) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s := by
      simp [wp_norm, arm64_norm, Reg.x8, *])
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega)
    (hext4 : desc.offset + count.toNat ≤ Arm64.FS_SAFE_MAX_FILESIZE := by
      simp only [Arm64.FS_SAFE_MAX_FILESIZE] at *; omega) :
    SepWP prog target_pc s ((buf ↦ₛ bs) ∗ F) post oom := by
  refine step_svc_write_file_clamped hpc hrun hfetch _hx8 hfd hfd_ge hfd_lt hbuf hcnt hnz
    (by rw [Nat.min_eq_left hmax]; exact hlen) hopen hkind hwr happ hlfs ?_ hsvc hva
    (by rw [Nat.min_eq_left hmax]; exact hext4)
  simpa only [Nat.min_eq_left hmax, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hnext

/-! ## Relative-Path `execOpenat` Characterizations -/

/-- Pure regular-file lookup model for `openat(AT_FDCWD, path, O_RDONLY | O_CLOEXEC, 0)`:
    returns `some bytes` when `path` is non-empty, has no trailing directory syntax, has valid
    directory ancestors, and resolves to `some (.file bytes)` in `fs`. -/
def fsReadFile? (fs : FsState) (path : String) : Option (List (BitVec 8)) :=
  if path.isEmpty || trailingDir path || (ancestorWalkErrno? fs path).isSome then
    none
  else
    match fs.files path with
    | some (.file bs) => some bs
    | _ => none

/-- Pure writability model for `openat(AT_FDCWD, path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, mode)`:
    `path` is non-empty, has no trailing directory syntax, has valid directory ancestors, and does
    not resolve to an existing directory. -/
def fsCanWriteFile (fs : FsState) (path : String) : Bool :=
  !path.isEmpty && !trailingDir path && (ancestorWalkErrno? fs path).isNone &&
  fs.files path != some .dir

private theorem ancestorWalk_walk_values (fs : FsState) :
    ∀ (segs : List String) (cur : FsPath) (err : BitVec 64),
      ancestorWalkErrno?.walk fs cur segs = some err →
      err = ENOENT ∨ err = ENOTDIR ∨ err = ENAMETOOLONG
  | [], _, _, h => by simp [ancestorWalkErrno?.walk] at h
  | seg :: rest, cur, err, h => by
    dsimp only [ancestorWalkErrno?.walk] at h
    split at h
    · simp only [Option.some.injEq] at h; exact Or.inr (Or.inr h.symm)
    · split at h
      · exact ancestorWalk_walk_values fs rest _ err h
      · simp only [Option.some.injEq] at h; exact Or.inr (Or.inl h.symm)
      · simp only [Option.some.injEq] at h; exact Or.inl h.symm

theorem ancestorWalkErrno_eq_strict (fs : FsState) (p : String) :
    ancestorWalkErrno? fs p =
      match strictAncestorWalkErrno? fs p with
      | some err => some err
      | none =>
        if ((splitSlash p).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) then
          some ENAMETOOLONG
        else none := rfl

theorem strictAncestorWalkErrno_values {fs : FsState} {p : String} {err : BitVec 64}
    (h : strictAncestorWalkErrno? fs p = some err) :
    err = ENOENT ∨ err = ENOTDIR ∨ err = ENAMETOOLONG :=
  ancestorWalk_walk_values fs _ [] _ h

theorem ancestorWalkErrno_values {fs : FsState} {p : String} {err : BitVec 64}
    (h : ancestorWalkErrno? fs p = some err) :
    err = ENOENT ∨ err = ENOTDIR ∨ err = ENAMETOOLONG := by
  dsimp only [ancestorWalkErrno?] at h
  split at h
  · rename_i e he
    simp only [Option.some.injEq] at h; subst h
    exact ancestorWalk_walk_values fs _ [] _ he
  · split at h
    · simp only [Option.some.injEq] at h; exact Or.inr (Or.inr h.symm)
    · cases h

theorem strictAncestorWalkErrno_of_none {fs : FsState} {p : String}
    (h : ancestorWalkErrno? fs p = none) :
    strictAncestorWalkErrno? fs p = none ∧
      ((splitSlash p).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) = false := by
  rw [ancestorWalkErrno_eq_strict] at h
  cases hs : strictAncestorWalkErrno? fs p with
  | some _ => rw [hs] at h; cases h
  | none =>
    rw [hs] at h
    cases hl : ((splitSlash p).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true => rw [hl] at h; cases h
    | false => exact ⟨rfl, rfl⟩

theorem ancestorWalkErrno_walk_of_none {fs : FsState} {p : String}
    (h : ancestorWalkErrno? fs p = none) :
    ancestorWalkErrno?.walk fs [] ((splitSlash p).filter (!·.isEmpty)).dropLast = none :=
  (strictAncestorWalkErrno_of_none h).1

private theorem ancestorWalk_walk_none_dir (fs : FsState) :
    ∀ (segs : List String) (cur : FsPath),
      fs.getEntry cur = some .dir →
      ancestorWalkErrno?.walk fs cur segs = none →
      fs.getEntry (cur ++ segs.filter (· != ".")) = some .dir
  | [], cur, hdir, _ => by simpa using hdir
  | seg :: rest, cur, hdir, hnone => by
    dsimp only [ancestorWalkErrno?.walk] at hnone
    split at hnone
    case isTrue => cases hnone
    split at hnone
    case h_1 hcur' =>
      have ih := ancestorWalk_walk_none_dir fs rest _ hcur' hnone
      by_cases hdot : (seg == ".") = true
      · have hndot : (seg != ".") = false := by simp [bne, hdot]
        simpa [hdot, hndot] using ih
      · have hndot : (seg != ".") = true := by simp [bne, Bool.eq_false_iff.mpr hdot]
        simpa [hdot, hndot, List.append_assoc] using ih
    case h_2 => cases hnone
    case h_3 => cases hnone

private theorem splitSlash_go_append_slash_dot :
    ∀ (r cur : List Char),
      ∃ pref : List String, splitSlash.go cur (r ++ ['/', '.']) = pref ++ ["."]
  | [], cur => ⟨[String.ofList cur.reverse], rfl⟩
  | c :: rs, cur => by
    by_cases hc : c = '/'
    · subst hc
      obtain ⟨pref, hp⟩ := splitSlash_go_append_slash_dot rs []
      exact ⟨String.ofList cur.reverse :: pref, by simpa [splitSlash.go] using hp⟩
    · obtain ⟨pref, hp⟩ := splitSlash_go_append_slash_dot rs (c :: cur)
      exact ⟨pref, by simpa [splitSlash.go, hc] using hp⟩

theorem getEntry_dir_of_trailingDir_not_normSlash {fs : FsState} {p : String}
    (htd : trailingDir p = true) (htns : trailingNormSlash p = false)
    (hanc : ancestorWalkErrno? fs p = none) :
    fs.getEntry (normalizePath p) = some .dir := by
  let nes := (splitSlash p).filter (!·.isEmpty)
  have hnorm_eq : normalizePath p = nes.filter (· != ".") := by
    unfold normalizePath nes
    rw [List.filter_filter]
    congr 1; funext seg; simp [Bool.and_comm]
  have hdrop_dir : fs.getEntry (nes.dropLast.filter (· != ".")) = some .dir := by
    simpa using ancestorWalk_walk_none_dir fs nes.dropLast [] rfl (ancestorWalkErrno_walk_of_none hanc)
  unfold trailingDir at htd
  rcases Bool.or_eq_true_iff.mp htd with h12 | hesd
  · rcases Bool.or_eq_true_iff.mp h12 with hpdot | hts
    · rw [eq_of_beq hpdot]; rfl
    · unfold trailingNormSlash at htns
      rw [hts] at htns; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htns
      cases hrev : nes.reverse with
      | nil =>
        have hnes : nes = [] := List.reverse_eq_nil_iff.mp hrev
        rw [hnorm_eq, hnes]; rfl
      | cons last revPref =>
        rw [hrev] at htns; dsimp only at htns
        have hlast : last = "." := by
          by_cases hl : last = "."
          · exact hl
          · simp [bne, beq_false_of_ne hl] at htns
        subst hlast
        have hnes : nes = revPref.reverse ++ ["."] := by
          have := congrArg List.reverse hrev
          simpa using this
        rw [hnorm_eq]
        rw [hnes] at hdrop_dir ⊢
        simpa using hdrop_dir
  · unfold endsWithSlashDot at hesd
    cases hrev_cs : p.toList.reverse with
    | nil => rw [hrev_cs] at hesd; cases hesd
    | cons c1 rest1 =>
      cases rest1 with
      | nil =>
        rw [hrev_cs] at hesd
        by_cases hc1 : c1 = '.' <;> simp [hc1] at hesd
      | cons c2 rest2 =>
        rw [hrev_cs] at hesd
        by_cases hc1 : c1 = '.'
        · subst hc1
          by_cases hc2 : c2 = '/'
          · subst hc2
            have hcs : p.toList = rest2.reverse ++ ['/', '.'] := by
              have := congrArg List.reverse hrev_cs
              simpa [List.reverse_cons, List.append_assoc] using this
            obtain ⟨pref, hsp⟩ := splitSlash_go_append_slash_dot rest2.reverse []
            have hnes : nes = pref.filter (!·.isEmpty) ++ ["."] := by
              dsimp only [nes, splitSlash]
              rw [hcs, hsp, List.filter_append]; rfl
            rw [hnorm_eq]
            rw [hnes] at hdrop_dir ⊢
            simpa using hdrop_dir
          · simp [hc2] at hesd
        · simp [hc1] at hesd

/-- Exact characterization of `execOpenat s` for relative read-only opens
    (`dfd = AT_FDCWD_W32`, `flags = O_LARGEFILE_W32 ||| O_CLOEXEC_W32`). -/
theorem execOpenat_rdonly_cloexec {s : State} {path : String} {fd : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hnotdir : ancestorWalkErrno? s.fs path = none → s.fs.files path ≠ some .dir)
    (halloc : s.fs.allocFd = some fd) :
    match fsReadFile? s.fs path with
    | some fileBytes =>
      s.fs.files path = some (.file fileBytes) ∧
      execOpenat s =
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true, offset := 0 }))).writeReg64
          .x0 fd).advancePC
    | none =>
      ∃ err : BitVec 64, (err = ENOENT ∨ err = ENOTDIR ∨ err = ENAMETOOLONG) ∧
        execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_ex : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_EXCL_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict, fsReadFile?]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_ex, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  by_cases hemp : path.isEmpty = true
  · simp [resolveCwdPath, hemp]
  · simp only [Bool.not_eq_true] at hemp
    have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
      simp [resolveCwdPath, hemp, hlead, hdot]
    rw [hres]; simp only [hemp, Bool.false_or]
    cases hanc : ancestorWalkErrno? s.fs path with
    | some err =>
      simp only [Option.isSome_some, Bool.or_true, ↓reduceIte]
      rw [ancestorWalkErrno_eq_strict] at hanc
      cases hsanc : strictAncestorWalkErrno? s.fs path with
      | some e =>
        rw [hsanc] at hanc; simp only [Option.some.injEq] at hanc; subst hanc
        exact ⟨e, strictAncestorWalkErrno_values hsanc, rfl⟩
      | none =>
        rw [hsanc] at hanc
        cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
        | true =>
          rw [hlast] at hanc; simp only [↓reduceIte, Option.some.injEq] at hanc; subst hanc
          exact ⟨ENAMETOOLONG, Or.inr (Or.inr rfl), rfl⟩
        | false => rw [hlast] at hanc; cases hanc
    | none =>
      obtain ⟨hsanc, hlast⟩ := strictAncestorWalkErrno_of_none hanc
      rw [hsanc]; dsimp only
      rw [hlast]; simp only [Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      have hnd := hnotdir hanc
      unfold FsState.files at hnd ⊢
      cases hent : s.fs.getEntry (normalizePath path) with
      | some entry =>
        cases entry with
        | dir => exact absurd hent hnd
        | file oldBytes =>
          by_cases htd : trailingDir path = true
          · simp [htd]
          · simp only [Bool.not_eq_true] at htd
            have hne_segs : normalizePath path ≠ [] := by
              intro hnil; rw [hnil] at hent; cases hent
            simp [htd, halloc, FsState.setEntry_self_of_nonEmpty hne_segs hent]
      | none =>
        cases trailingDir path <;> simp

/-- Exact characterization of `execOpenat s` for relative create/truncate-open
    (`dfd = AT_FDCWD_W32`, `flags = 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32`,
    owner read-write `mode`). -/
theorem execOpenat_wronly_creat_trunc_cloexec {s : State} {path : String} {fd : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 =
      1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hmode : s.readReg32 .x3 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (halloc : s.fs.allocFd = some fd) :
    if fsCanWriteFile s.fs path then
      let fs' := (s.fs.setFile path (some (.file []))).setFd fd
        (some { path := path, accMode := .wronly, append := false, cloexec := true, offset := 0 })
      execOpenat s =
        (((s.setFs fs').appendTrace [.fileChanged (normalizePath path).toPathString]).writeReg64
          .x0 fd).advancePC
    else
      ∃ err : BitVec 64, (err = ENOENT ∨ err = ENOTDIR ∨ err = EISDIR ∨ err = ENAMETOOLONG) ∧
        execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad :
      (((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
          ~~~OPENAT_KNOWN_MASK) != 0#32 ||
        ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
          3#32) == 3#32) = false := by decide
  have hf_m0 :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        3#32 == 0#32) = false := by decide
  have hf_m1 :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        3#32 == 1#32) = true := by decide
  have hf_cr :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_CREAT_W32 != 0#32) = true := by decide
  have hf_ex :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_EXCL_W32 != 0#32) = false := by decide
  have hf_tr :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_TRUNC_W32 != 0#32) = true := by decide
  have hf_ap :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl :
      ((1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&&
        O_CLOEXEC_W32 != 0#32) = true := by decide
  have hmode_ne : (s.readReg32 .x3 &&& O_CREAT_OWNER_RW_MASK != O_CREAT_OWNER_RW_MASK) = false := by
    simp [hmode]
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict, fsCanWriteFile]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_m1, hf_cr, hf_ex, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.and_false, ↓reduceIte]
  by_cases hemp : path.isEmpty = true
  · simp [resolveCwdPath, hemp]
  · simp only [Bool.not_eq_true] at hemp
    have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
      simp [resolveCwdPath, hemp, hlead, hdot]
    rw [hres]; simp only [hemp, Bool.not_false, Bool.true_and]
    cases hsanc : strictAncestorWalkErrno? s.fs path with
    | some err =>
      have hanc : ancestorWalkErrno? s.fs path = some err := by
        rw [ancestorWalkErrno_eq_strict, hsanc]
      simp only [hanc, Option.isNone_some, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rcases strictAncestorWalkErrno_values hsanc with rfl | rfl | rfl
      · exact ⟨ENOENT, Or.inl rfl, rfl⟩
      · exact ⟨ENOTDIR, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨ENAMETOOLONG, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    | none =>
      dsimp only
      by_cases htns : trailingNormSlash path = true
      · have htd : trailingDir path = true := by
          unfold trailingNormSlash at htns
          by_cases hts : hasTrailingSlash path = true
          · unfold trailingDir; simp [hts]
          · simp [hts] at htns
        simp [htd, htns]
      · simp only [Bool.not_eq_true] at htns
        simp only [htns, Bool.false_eq_true, ↓reduceIte]
        cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
        | true =>
          have hanc : ancestorWalkErrno? s.fs path = some ENAMETOOLONG := by
            rw [ancestorWalkErrno_eq_strict, hsanc, hlast]; rfl
          simp [hanc]
        | false =>
          have hanc : ancestorWalkErrno? s.fs path = none := by
            rw [ancestorWalkErrno_eq_strict, hsanc, hlast]; rfl
          simp only [hanc, Option.isNone_none, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
          unfold FsState.files
          by_cases htd : trailingDir path = true
          · simp only [htd, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            have hdir := getEntry_dir_of_trailingDir_not_normSlash htd htns hanc
            rw [hdir]; simp
          · simp only [Bool.not_eq_true] at htd
            simp only [htd, Bool.not_false, Bool.true_and]
            have hne_none : ((none : Option FsEntry) != some .dir) = true := by decide
            have hne_dir : ((some .dir : Option FsEntry) != some .dir) = false := by decide
            cases hent : s.fs.getEntry (normalizePath path) with
            | none =>
              simp [hne_none, halloc, hmode_ne, FsState.setFile]
            | some e =>
              cases e with
              | dir => simp [hne_dir]
              | file oldBytes =>
                have hne_file : ((some (.file oldBytes) : Option FsEntry) != some .dir) = true := rfl
                simp [hne_file, halloc, FsState.setFile]

/-! ## Syscall State Preservation -/

/-- State fields preserved across file and stdio syscalls: thread pointer `tpidrEl0`, signal
    dispositions `sigActions`, and virtual-memory fields (`VmFieldsPreserved`). -/
def SyscallPreserved (s0 sf : State) : Prop :=
  sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧
  VmFieldsPreserved s0 sf

theorem SyscallPreserved.refl (s : State) : SyscallPreserved s s :=
  ⟨rfl, rfl, VmFieldsPreserved.refl s⟩

theorem SyscallPreserved.trans {s0 s1 s2 : State}
    (h01 : SyscallPreserved s0 s1) (h12 : SyscallPreserved s1 s2) :
    SyscallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, VmFieldsPreserved.trans h01.2.2 h12.2.2⟩

theorem SyscallPreserved.of_std {s0 sf : State} (h : StdStatePreserved s0 sf) :
    SyscallPreserved s0 sf :=
  ⟨h.2.2.1, h.2.2.2.1, ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩⟩

end ProofLib
