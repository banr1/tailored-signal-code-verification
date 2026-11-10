/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.Invariant
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.WP.Structural
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.Defs

/-!
# Weakest-Precondition Rules for Linux Syscalls

Separation-logic `SepWP` step lemmas for Linux AArch64 `SVC #0` file-system, virtual-memory,
time, stream-I/O, and exit syscalls (`openat`, `read`, `write`, `close`, `clock_gettime`,
`brk`, `mmap`, `exit`), together with byte-slice carving, C-string reading, and stream-trace
projection helpers.
-/

@[expose] public section

namespace ProofLib

open Arm64

set_option maxRecDepth 200000

/-- Writing a byte list `chunk` (`chunk.length ≤ bs₀.length`) at `dst` updates the prefix of
    `(dst ↦ₛ bs₀)` to `chunk`, leaving the suffix `bs₀.drop chunk.length` and `R` intact. -/
theorem satisfies_writeBytes_prefix {m : Memory} {dst : BitVec 64}
    {bs₀ chunk : List (BitVec 8)} {R : SepProp}
    (hle : chunk.length ≤ bs₀.length)
    (hm : m ⊨ (dst ↦ₛ bs₀) ∗ R) :
    m.writeBytes dst chunk ⊨ (dst ↦ₛ (chunk ++ bs₀.drop chunk.length)) ∗ R := by
  rw [pointsToBytes_take_drop dst chunk.length bs₀ hle, sepConj_assoc] at hm
  have hw :
      m.writeBytes dst chunk ⊨
        (dst ↦ₛ chunk) ∗ ((dst + BitVec.ofNat 64 chunk.length) ↦ₛ bs₀.drop chunk.length ∗ R) :=
    satisfies_writeBytes_step hm (by rw [List.length_take_of_le hle])
  rw [← sepConj_assoc, ← pointsToBytes_append] at hw
  exact hw

/-- Generic `SepWP` rule for an instruction whose execution writes `chunk` (`chunk.length ≤ bs₀.length`)
    to an owned buffer `((dst ↦ₛ bs₀) ∗ F)` without modifying other memory cells. -/
theorem SepWP.step_writeBytes_prefix {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {dst : BitVec 64} {bs₀ chunk : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64} {inst : Instr}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = s')
    (hmem : s'.mem = s.mem.writeBytes dst chunk)
    (hle : chunk.length ≤ bs₀.length)
    (hnext : SepWP prog target_pc s' ((dst ↦ₛ (chunk ++ bs₀.drop chunk.length)) ∗ F) post oom) :
    SepWP prog target_pc s ((dst ↦ₛ bs₀) ∗ F) post oom := by
  intro R hm
  have hs_pc : s.setPC pc = s := by cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hfetch' : prog.fetch s.pc = some inst := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [← hs_pc, hexec]
  apply hnext R
  rw [hmem, sepConj_assoc]
  have hm_assoc : s.mem ⊨ (dst ↦ₛ bs₀) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  exact satisfies_writeBytes_prefix hle hm_assoc

/-- Specialized `SepWP` byte-slice write rule when `chunk.length = bs₀.length`. -/
theorem SepWP.step_writeBytes_exact {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {dst : BitVec 64} {bs₀ chunk : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64} {inst : Instr}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = s')
    (hmem : s'.mem = s.mem.writeBytes dst chunk)
    (heq : chunk.length = bs₀.length)
    (hnext : SepWP prog target_pc s' ((dst ↦ₛ chunk) ∗ F) post oom) :
    SepWP prog target_pc s ((dst ↦ₛ bs₀) ∗ F) post oom := by
  refine SepWP.step_writeBytes_prefix hpc hrun hfetch hexec hmem (Nat.le_of_eq heq) ?_
  have hd : bs₀.drop chunk.length = [] := List.drop_eq_nil_of_le (Nat.le_of_eq heq.symm)
  simpa [hd] using hnext


/-- Null-terminated byte encoding of a character list (`chars.map ... ++ [0#8]`). -/
def cstrBytes (path : String) : List (BitVec 8) :=
  path.toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8]



private theorem readCStringAux_of_bytesRO {m : Memory} {ptr : BitVec 64} {R : SepProp} :
    ∀ (cs : List Char) (fuel : Nat) (acc : List Char),
      cs.length < fuel →
      (∀ c ∈ cs, c.toNat < 256 ∧ c.toNat ≠ 0) →
      m ⊨ (ptr ↦ᵣ (cs.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])) ∗ R →
      readCStringAux m ptr fuel acc = .ok (String.ofList (acc.reverse ++ cs))
  | [], fuel + 1, acc, _, _, hm => by
    simp only [List.map_nil, List.nil_append, pointsToBytesRO_singleton] at hm
    have hc : m.canRead ptr 1 = true := (IsBlockRO.pointsTo8RO ptr 0#8).canRead (by decide) hm
    have har : (m.perm ptr).r = true := by
      have h1 := ((Bool.and_eq_true _ _).mp hc).1
      simpa [Memory.allPerm] using h1
    have hr : m.read8 ptr = 0#8 := (IsBlockRO.pointsTo8RO ptr 0#8).read hm
    simp [readCStringAux, har, hc, hr]
  | c :: cs, fuel + 1, acc, hfuel, hcs, hm => by
    have ⟨hc_lt, hc_ne⟩ := hcs c (List.mem_cons_self ..)
    have hbv_ne : BitVec.ofNat 8 c.toNat ≠ 0#8 := by
      intro h; exact hc_ne (by have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hc_lt] using this)
    have hbv_eq : (BitVec.ofNat 8 c.toNat == 0#8) = false := beq_false_of_ne hbv_ne
    simp only [List.map_cons, List.cons_append, pointsToBytesRO_cons, sepConj_assoc] at hm
    have hc : m.canRead ptr 1 = true := (IsBlockRO.pointsTo8RO ptr _).canRead (by decide) hm
    have har : (m.perm ptr).r = true := by
      have h1 := ((Bool.and_eq_true _ _).mp hc).1
      simpa [Memory.allPerm] using h1
    have hr : m.read8 ptr = BitVec.ofNat 8 c.toNat := (IsBlockRO.pointsTo8RO ptr _).read hm
    have hm_tail : m ⊨ ((ptr + 1#64) ↦ᵣ (cs.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])) ∗
        ((ptr ↦₈ᵣ BitVec.ofNat 8 c.toNat) ∗ R) := by
      rw [sepConj_left_comm] at hm; exact hm
    have hchr : Char.ofNat (BitVec.ofNat 8 c.toNat).toNat = c := by
      simp [Nat.mod_eq_of_lt hc_lt]
    rw [readCStringAux]
    simp only [har, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr, hbv_eq, hchr]
    rw [readCStringAux_of_bytesRO cs fuel (c :: acc) (by simp at hfuel; omega)
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) hm_tail]
    simp [List.reverse_cons, List.append_assoc]

/-- Reading a NUL-terminated string from an RO byte slice `(ptr ↦ᵣ cstrBytes path) ∗ R`. -/
theorem readCString_of_pointsToBytesRO {m : Memory} {ptr : BitVec 64} {path : String} {R : SepProp}
    (hlen : path.toList.length < PATH_MAX)
    (hvalid : ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0)
    (hm : m ⊨ (ptr ↦ᵣ cstrBytes path) ∗ R) :
    readCString m ptr = .ok path := by
  unfold readCString cstrBytes at *
  simpa using readCStringAux_of_bytesRO path.toList PATH_MAX [] hlen hvalid hm

/-! ## `FsState` Descriptor Table Lemmas -/

@[simp, arm64_norm]
theorem FsState.setFd_setFd_same (fs : FsState) (fd : BitVec 64) (d1 d2 : Option FdEntry) :
    (fs.setFd fd d1).setFd fd d2 = fs.setFd fd d2 := by
  cases fs
  simp only [FsState.setFd, FsState.mk.injEq, true_and]
  funext k
  by_cases h : (k == fd) = true <;> simp [h]


private theorem allocFd_aux {fs : FsState} {fd : BitVec 64} :
    ∀ (l : List Nat),
      (∀ x ∈ l, x + 3 < FsState.maxOpenFds ∧ x + 3 < 2 ^ 64) →
      (l.find? fun i => fs.fds (BitVec.ofNat 64 (i + 3)) == none).map
        (fun i => BitVec.ofNat 64 (i + 3)) = some fd →
      fs.fds fd = none ∧ fd.toNat ≥ 3 ∧ fd.toNat < FsState.maxOpenFds
  | [], _, h => by simp at h
  | x :: xs, hl, h => by
    simp only [List.find?_cons] at h
    split at h
    · next hpred =>
      simp only [Option.map_some, Option.some.injEq] at h; subst h
      have ⟨hmax, hlt264⟩ := hl x (List.mem_cons_self ..)
      refine ⟨by simpa using hpred, ?_, ?_⟩
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt264]; omega
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt264]; exact hmax
    · exact allocFd_aux xs (fun y hy => hl y (List.mem_cons_of_mem _ hy)) h

/-- `FsState.allocFd = some fd` yields an unused descriptor `fd ∈ [3, FsState.maxOpenFds)`. -/
theorem FsState.allocFd_spec {fs : FsState} {fd : BitVec 64}
    (h : fs.allocFd = some fd) :
    fs.fds fd = none ∧ fd.toNat ≥ 3 ∧ fd.toNat < FsState.maxOpenFds :=
  allocFd_aux (List.range (FsState.maxOpenFds - 3))
    (fun x hx => by
      have hx' : x < FsState.maxOpenFds - 3 := List.mem_range.mp hx
      have hmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmax] at hx' ⊢
      omega)
    h

private theorem state_setPC_eq_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.setPC pc = s := by
  cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm

/-! ## Per-Syscall `SepWP` Rules -/


/-- `SVC #0` rule for `close` (`X8 = 57`). -/
theorem SepWP.step_svc_close {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 57#64)
    (hnext : SepWP prog target_pc (execClose s) P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execClose s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom :=
  let _ := hx8
  let hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  SepWP.step_pure hpc hrun hfetch
    (by rw [hpc_eq, hsvc])
    (by dsimp only [execClose]; (repeat' split) <;> rfl)
    hnext



private theorem mem_advancePC (s : State) : s.advancePC.mem = s.mem := by cases s; rfl
private theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
private theorem mem_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).mem = s.mem := by cases s; rfl
private theorem mem_setFs (s : State) (f : FsState) : (s.setFs f).mem = s.mem := by
  cases s; rfl
private theorem mem_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).mem = s.mem := by
  cases s; rfl
private theorem mem_execOpenat (s : State) : (execOpenat s).mem = s.mem := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;>
    simp only [mem_advancePC, mem_writeReg64, mem_setStatus, mem_setFs, mem_appendTrace]

/-- `SVC #0` rule for `openat` (`X8 = 56`) when `X1` points to an RO NUL-terminated string `path`. -/
theorem SepWP.step_svc_openat_ro {prog : Program} {target_pc : BitVec 64}
    {s : State} {path : String} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc fname : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 56#64)
    (hfname : s.readReg64 .x1 = fname)
    (hlen : path.toList.length < PATH_MAX)
    (hvalid : ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0)
    (hnext : readCString s.mem (s.readReg64 .x1) = .ok path →
      SepWP prog target_pc (execOpenat s) ((fname ↦ᵣ cstrBytes path) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execOpenat s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s ((fname ↦ᵣ cstrBytes path) ∗ F) post oom := by
  let _ := hx8
  intro R hm
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hm' : s.mem ⊨ (fname ↦ᵣ cstrBytes path) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcs : readCString s.mem (s.readReg64 .x1) = .ok path := by
    rw [hfname]; exact readCString_of_pointsToBytesRO hlen hvalid hm'
  exact SepWP.step_pure hpc hrun hfetch
    (by rw [hpc_eq, hsvc])
    (mem_execOpenat s)
    (hnext hcs) R hm

public meta section
/-- Close a `prog.fetch pc = some ?inst` subgoal from a local `FnCode.holds` / `hasCode` /
    `codeAt` hypothesis or generated fetch lemma. -/
elab "wp_fetch" : tactic => do
  unless (← ProofLib.tryCloseFetchFromHasCode) do
    Lean.throwError "wp_fetch: could not close instruction fetch subgoal from context"
end

private theorem state_advancePC_eq_setPC {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.advancePC = s.setPC (pc + 4#64) := by
  subst hpc; rfl

private theorem readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by omega : 2 ^ 32 < 2 ^ 64))] using hlt
  unfold BitVec.slt BitVec.toInt
  simp; omega

/-- `SVC #0` rule for `read` (`X8 = 63`) on an open readable `.localFile` or `.stdio` descriptor
    `fd`, clamping the transfer length to `min count.toNat MAX_RW_COUNT` per Linux `rw_verify_area`. -/
theorem SepWP.step_svc_read_clamped {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {bs₀ : List (BitVec 8)}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs₀.length = count.toNat)
    (hopen : s.fs.fds fd = some desc)
    (hkind : (desc.kind == .localFile || desc.kind == .stdio) = true := by rfl)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let fileBytes := s.fs.fdBytes desc
      let chunk := (fileBytes.drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)
      let s' := (((s.setMem (s.mem.writeBytes buf chunk)).setFs
        (s.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }))).writeReg64
        .x0 (BitVec.ofNat 64 chunk.length)).setPC (pc + 4#64)
      SepWP prog target_pc s' ((buf ↦ₛ (chunk ++ bs₀.drop chunk.length)) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s := by simp [wp_norm, arm64_norm, Reg.x8, execRead, *])
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega)
    (hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
      intro _; simp only [Arm64.MAX_LFS_FILESIZE] at *; omega) :
    SepWP prog target_pc s ((buf ↦ₛ bs₀) ∗ F) post oom := by
  let _ := hx8
  intro R hm
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  have hm' : s.mem ⊨ (buf ↦ₛ bs₀) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw : s.mem.canWrite buf count.toNat = true := by
    rw [← hlen]
    exact (IsBlock.pointsToBytes buf bs₀).canWrite ((IsBlock.pointsToBytes buf bs₀).read hm').1 hm'
  have hle_cnt : (((s.fs.fdBytes desc).drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)).length ≤ count.toNat :=
    Nat.le_trans (List.length_take_le _ _) (Nat.min_le_left _ _)
  have hcwk : s.mem.canWrite buf (((s.fs.fdBytes desc).drop desc.offset).take (min count.toNat Arm64.MAX_RW_COUNT)).length = true :=
    Memory.canWrite_take_of_le hcw hle_cnt
  refine SepWP.step_writeBytes_prefix hpc hrun hfetch ?_ rfl
    (by rw [hlen]; exact hle_cnt) hnext R hm
  refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
  have hnotdir : (!false && desc.kind == .localDir) = false := by
    cases hk : desc.kind <;> first | rfl | exact False.elim (Bool.noConfusion (hk ▸ hkind))
  have hguard : (!(desc.kind == .localFile || (!false && desc.kind == .stdio))) = false := by
    cases hk : desc.kind <;> first | rfl | exact False.elim (Bool.noConfusion (hk ▸ hkind))
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have hlfs_f : (desc.kind == .localFile && decide (desc.offset + count.toNat > Arm64.MAX_LFS_FILESIZE)) = false := by
    cases hk : desc.kind
    · change (true && decide _) = false; rw [Bool.true_and]; exact decide_eq_false (Nat.not_lt.mpr (hlfs hk))
    · rfl
    · rfl
    · rfl
  rw [hpc_eq, hsvc]
  dsimp only [execRead, execReadCommon]
  rw [hslt, hfd, hbuf, hcnt, hopen]
  simp only [Bool.false_eq_true, ↓reduceIte, hnotdir, hguard, hrd, hva_f, hlfs_f, hcwk]
  rfl

theorem SepWP.step_svc_read {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {bs₀ : List (BitVec 8)}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs₀.length = count.toNat)
    (hopen : s.fs.fds fd = some desc)
    (hkind : (desc.kind == .localFile || desc.kind == .stdio) = true := by rfl)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let fileBytes := s.fs.fdBytes desc
      let chunk := (fileBytes.drop desc.offset).take count.toNat
      let s' := (((s.setMem (s.mem.writeBytes buf chunk)).setFs
        (s.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }))).writeReg64
        .x0 (BitVec.ofNat 64 chunk.length)).setPC (pc + 4#64)
      SepWP prog target_pc s' ((buf ↦ₛ (chunk ++ bs₀.drop chunk.length)) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s := by simp [wp_norm, arm64_norm, Reg.x8, execRead, *])
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega)
    (hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
      intro _; simp only [Arm64.MAX_LFS_FILESIZE] at *; omega) :
    SepWP prog target_pc s ((buf ↦ₛ bs₀) ∗ F) post oom := by
  refine SepWP.step_svc_read_clamped hpc hrun hfetch hx8 hfd hfd_lt hbuf hcnt hlen hopen hkind hrd ?_ hsvc hva hlfs
  simpa only [Nat.min_eq_left hmax] using hnext






/-- `SVC #0` rule for `close` (`X8 = 57`) closing an open descriptor `fd`. -/
theorem SepWP.step_svc_close_fd {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 57#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localFile := by rfl)
    (hnext :
      let s' := ((s.setFs (s.fs.setFd fd none)).writeReg64 .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execClose s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  have hslt : (s.readReg32 .x0).slt 0#32 = false := readReg32_slt_zero_false hfd hfd_lt
  refine SepWP.step_svc_close hpc hrun hfetch hx8 ?_ hsvc
  dsimp only [execClose]
  rw [hslt, hfd, hopen]; dsimp only
  rw [hkind]
  change SepWP prog target_pc
    (((s.setFs (s.fs.setFd fd none)).writeReg64 .x0 0#64).setPC (s.pc + 4#64)) P post oom
  rw [hpc]
  exact hnext

/-- `SVC #0` rule for `openat(AT_FDCWD, fname, O_RDONLY, _)` opening an existing regular file
    `path` read-only in the working-directory tree when `X1` points to an RO NUL-terminated
    relative path string `path`. -/
theorem SepWP.step_svc_openat_file_ro {prog : Program} {target_pc : BitVec 64}
    {s : State} {path : String} {fileBytes : List (BitVec 8)} {fd : BitVec 64}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {pc fname : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 56#64)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hfname : s.readReg64 .x1 = fname)
    (hflags : s.readReg32 .x2 = 0#32)
    (hemp : path.isEmpty = false)
    (hnorel : hasLeadingSlash path = false := by decide)
    (hnodd : hasDotDot path = false := by decide)
    (hntrail : trailingDir path = false := by decide)
    (hlen : path.toList.length < PATH_MAX)
    (hvalid : ∀ c ∈ path.toList, c.toNat < 256 ∧ c.toNat ≠ 0)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfiles : s.fs.files path = some (.file fileBytes))
    (halloc : s.fs.allocFd = some fd)
    (hnext :
      let s' := ((s.setFs (s.fs.setFd fd (some { path := path, accMode := .rdonly }))).writeReg64
        .x0 fd).setPC (pc + 4#64)
      SepWP prog target_pc s' ((fname ↦ᵣ cstrBytes path) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execOpenat s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s ((fname ↦ᵣ cstrBytes path) ∗ F) post oom := by
  refine SepWP.step_svc_openat_ro hpc hrun hfetch hx8 hfname hlen hvalid (fun hcs => ?_) hsvc
  have hsf : s.fs.setEntry (normalizePath path) (some (.file fileBytes)) = s.fs := by
    have hge : s.fs.getEntry (normalizePath path) = some (.file fileBytes) := hfiles
    rcases hfs_eq : s.fs with ⟨entries, fds⟩
    dsimp only [FsState.setEntry]
    congr; funext k
    by_cases hk : k = normalizePath path
    · subst hk
      dsimp only [FsState.getEntry] at hge
      rw [hfs_eq] at hge
      split at hge
      · cases hge
      · simpa using hge.symm
    · simp [hk]
  have hres : resolveCwdPath (s.readReg32 .x0) path = .ok (normalizePath path) := by
    rw [hdfd]; simp [resolveCwdPath, hemp, hnorel, hnodd]
  have hge : s.fs.getEntry (normalizePath path) = some (.file fileBytes) := hfiles
  have hsanc : strictAncestorWalkErrno? s.fs path = none := by
    dsimp only [ancestorWalkErrno?] at hanc
    cases hw : strictAncestorWalkErrno? s.fs path with
    | some _ => dsimp only [strictAncestorWalkErrno?] at hw; rw [hw] at hanc; cases hanc
    | none => rfl
  have hlast : (((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX)) = false := by
    dsimp only [ancestorWalkErrno?] at hanc
    have hw : ancestorWalkErrno?.walk s.fs [] ((splitSlash path).filter (!·.isEmpty)).dropLast = none := hsanc
    rw [hw] at hanc
    cases hl : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true => rw [hl] at hanc; cases hanc
    | false => rfl
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hflags, hcs]
  dsimp only
  have hnc : (0#32 &&& O_CREAT_W32 != 0#32) = false := rfl
  rw [hres, hsanc]
  dsimp only
  rw [hnc, Bool.false_and, hlast, hntrail]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, halloc]
  change SepWP prog target_pc
    (((s.setFs ((s.fs.setEntry (normalizePath path) (some (.file fileBytes))).setFd fd
      (some { path := path, accMode := .rdonly }))).writeReg64 .x0 fd).setPC (s.pc + 4#64))
    ((fname ↦ᵣ cstrBytes path) ∗ F) post oom
  rw [hsf, hpc]
  exact hnext

/-- Bridge between the 16-byte little-endian `encodeTimespec ts` slice at `tp` and the two
    64-bit `struct timespec` fields `tv_sec` at `tp` and `tv_nsec` at `tp + 8`. -/
theorem pointsToBytes_encodeTimespec (tp : BitVec 64) (ts : Timespec) :
    (tp ↦ₛ encodeTimespec ts) =
      ((tp ↦₆₄ ts.sec) ∗ ((tp + 8#64) ↦₆₄ BitVec.ofNat 64 ts.nsec.val)) := by
  change (tp ↦ₛ (unpack64 ts.sec ++ unpack64 (BitVec.ofNat 64 ts.nsec.val))) = _
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]

/-- `SVC #0` rule for `clock_gettime` (`X8 = 113`) writing the 16-byte little-endian
    `ts := s.oracle.clockGettime s.oracleIdx` (`ts.nsec.val < 1_000_000_000`) to an owned
    16-byte buffer `(tp ↦ₛ bs₀)` and advancing `s.oracleIdx` via `s.nextOracle`. -/
theorem SepWP.step_svc_clock_gettime {prog : Program} {target_pc : BitVec 64}
    {s : State} {tp : BitVec 64} {bs₀ : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 113#64)
    (hclk : (s.readReg32 .x0).toNat ≤ 7)
    (htp : s.readReg64 .x1 = tp)
    (hlen : bs₀.length = 16)
    (hnext :
      let ts := s.oracle.clockGettime s.oracleIdx
      let s' := (((s.setMem (s.mem.writeBytes tp (encodeTimespec ts))).nextOracle).writeReg64
        .x0 0#64).setPC (pc + 4#64)
      ts.nsec.val < 1000000000 →
      SepWP prog target_pc s' ((tp ↦ₛ encodeTimespec ts) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execClockGettime s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s ((tp ↦ₛ bs₀) ∗ F) post oom := by
  let _ := hx8
  intro R hm
  have hpc_eq : s.setPC pc = s := state_setPC_eq_self hpc
  have hm' : s.mem ⊨ (tp ↦ₛ bs₀) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw : s.mem.canWrite tp 16 = true :=
    hlen ▸ (IsBlock.pointsToBytes tp bs₀).canWrite ((IsBlock.pointsToBytes tp bs₀).read hm').1 hm'
  refine SepWP.step_writeBytes_exact hpc hrun hfetch ?_ rfl
    (by simp only [encodeTimespec_length, hlen])
    (hnext (s.oracle.clockGettime s.oracleIdx).nsec.isLt) R hm
  refine Eq.trans ?_ (state_advancePC_eq_setPC hpc)
  rw [hpc_eq, hsvc]
  dsimp only [execClockGettime]
  split
  · omega
  · rw [htp, hcw]; rfl

/-- `SVC #0` rule for `clock_gettime` (`X8 = 113`) over a two-word `((tp ↦₆₄ sec₀) ∗ ((tp + 8#64) ↦₆₄ nsec₀))`
    `struct timespec` buffer, exposing `ts := s.oracle.clockGettime s.oracleIdx` with
    `ts.nsec.val < 1_000_000_000`. -/
theorem SepWP.step_svc_clock_gettime_words {prog : Program} {target_pc : BitVec 64}
    {s : State} {tp sec₀ nsec₀ : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 113#64)
    (hclk : (s.readReg32 .x0).toNat ≤ 7)
    (htp : s.readReg64 .x1 = tp)
    (hnext :
      let ts := s.oracle.clockGettime s.oracleIdx
      let s' := (((s.setMem (s.mem.writeBytes tp (encodeTimespec ts))).nextOracle).writeReg64
        .x0 0#64).setPC (pc + 4#64)
      ts.nsec.val < 1000000000 →
      SepWP prog target_pc s'
        (((tp ↦₆₄ ts.sec) ∗ ((tp + 8#64) ↦₆₄ BitVec.ofNat 64 ts.nsec.val)) ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execClockGettime s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (((tp ↦₆₄ sec₀) ∗ ((tp + 8#64) ↦₆₄ nsec₀)) ∗ F) post oom := by
  have hpre :
      ((tp ↦₆₄ sec₀) ∗ ((tp + 8#64) ↦₆₄ nsec₀)) =
        (tp ↦ₛ (unpack64 sec₀ ++ unpack64 nsec₀)) := by
    rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]
  rw [hpre]
  refine SepWP.step_svc_clock_gettime hpc hrun hfetch hx8 hclk htp (by rfl) (fun hlt => ?_) hsvc
  rw [pointsToBytes_encodeTimespec]
  exact hnext hlt

/-! ### Byte-Slice Carving and `memRegion` Folding -/

theorem list_eq_of_length_eq_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] :=
  ⟨_, _, List.eq_getElem_of_length_eq_two l h⟩

theorem list_eq_of_length_eq_four {α : Type} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] :=
  ⟨_, _, _, _, List.eq_getElem_of_length_eq_four l h⟩

theorem readBytes_two {m : Memory} {a : BitVec 64} {b0 b1 : BitVec 8}
    (h : m.readBytes a [b0, b1].length = [b0, b1]) :
    m.read8 a = b0 ∧ m.read8 (a + 1#64) = b1 := by
  refine ⟨?_, ?_⟩
  · simpa using Memory.read8_of_readBytes m a _ h 0 (by simp)
  · simpa using Memory.read8_of_readBytes m a _ h 1 (by simp)

theorem readBytes_four {m : Memory} {a : BitVec 64} {b0 b1 b2 b3 : BitVec 8}
    (h : m.readBytes a [b0, b1, b2, b3].length = [b0, b1, b2, b3]) :
    m.read16 a = pack16 b0 b1 ∧ m.read8 a = b0 ∧ m.read8 (a + 1#64) = b1 ∧
      m.read8 (a + 2#64) = b2 ∧ m.read8 (a + 3#64) = b3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using Memory.read16_of_readBytes m a _ h 0 (by simp)
  · simpa using Memory.read8_of_readBytes m a _ h 0 (by simp)
  · simpa using Memory.read8_of_readBytes m a _ h 1 (by simp)
  · simpa using Memory.read8_of_readBytes m a _ h 2 (by simp)
  · simpa using Memory.read8_of_readBytes m a _ h 3 (by simp)

theorem pointsToBytes_two_two (a : BitVec 64) (x0 x1 x2 x3 : BitVec 8) :
    (a ↦ₛ [x0, x1, x2, x3]) = (a ↦ₛ [x0, x1]) ∗ ((a + 2#64) ↦ₛ [x2, x3]) := by
  rw [show [x0, x1, x2, x3] = [x0, x1] ++ [x2, x3] from rfl, pointsToBytes_append]
  rfl

theorem pointsToBytes_entails_memRegion_of_length {a : BitVec 64} {bs : List (BitVec 8)} {n : Nat}
    (h : bs.length = n) : (a ↦ₛ bs) ⊢ memRegion a n :=
  h ▸ pointsToBytes_entails_memRegion a bs

theorem pointsToBytes_sepConj_memRegion_entails {a : BitVec 64} {bs : List (BitVec 8)} {n N : Nat}
    (hlen : bs.length = n) (hn : n ≤ N) (hN : N ≤ 2 ^ 64) :
    ((a ↦ₛ bs) ∗ memRegion (a + BitVec.ofNat 64 n) (N - n)) ⊢ memRegion a N := by
  rw [memRegion_split_le a n N hn hN]
  exact sepConj_mono (pointsToBytes_entails_memRegion_of_length hlen) (Entails.refl _)

/-- Close a post that hands back `memRegion a N` from an `n`-byte slice at its front: merge the
    slice back and expose its bytes as `readBytes`. -/
theorem satisfies_memRegion_of_pointsToBytes {m : Memory} {a : BitVec 64}
    {bs : List (BitVec 8)} {n N : Nat} {φ : Prop} {F R : SepProp}
    (hlen : bs.length = n) (hn : n ≤ N) (hN : N ≤ 2 ^ 64)
    (hm : m ⊨ ((a ↦ₛ bs) ∗ memRegion (a + BitVec.ofNat 64 n) (N - n) ∗ F) ∗ R)
    (hF : F ⊢ emp)
    (hφ : m.readBytes a bs.length = bs → φ) :
    m ⊨ (⌜φ⌝ ∗ memRegion a N) ∗ R := by
  have hm' : m ⊨ (a ↦ₛ bs) ∗ (memRegion (a + BitVec.ofNat 64 n) (N - n) ∗ F ∗ R) := by
    simpa only [sepConj_assoc] using hm
  have hrd := ((IsBlock.pointsToBytes a bs).read hm').2
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hφ hrd, Satisfies.mono ?_ hm⟩
  refine sepConj_mono ?_ (Entails.refl _)
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono (pointsToBytes_sepConj_memRegion_entails hlen hn hN) hF) ?_
  rw [sepConj_emp]
  exact Entails.refl _

/-- Split an `n`-byte slice with unknown contents off the front of `memRegion a N`. -/
theorem SepWP.carve_bytes {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {a : BitVec 64} {n N : Nat}
    (hn : n ≤ N) (hN : N ≤ 2 ^ 64)
    (h : ∀ bs : List (BitVec 8), bs.length = n →
      SepWP prog target_pc s ((a ↦ₛ bs) ∗ memRegion (a + BitVec.ofNat 64 n) (N - n) ∗ P) post oom) :
    SepWP prog target_pc s (memRegion a N ∗ P) post oom := by
  rw [memRegion_split_le a n N hn hN, memRegion_eq_exists_bytes a n (by omega), sepConj_assoc,
    sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  exact SepWP.pure_elim fun hlen => h bs hlen

/-! ### `brk`, `mmap`, `write`, and `exit` Syscall Step Rules -/

/-- `svc #0` with `X8 = 214` (`brk`) growing the page-aligned break `oldBrk` to `oldBrk + c`
    (`0 < c ≤ 4096`): maps the fresh page `memRegion oldBrk 4096`, deducts `4096` from
    `s.physMemAvail`, sets `brk`, and returns `X0 = oldBrk + c`. -/
theorem SepWP.step_svc_brk_grow_page {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc oldBrk c : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx0 : s.readReg64 .x0 = oldBrk + c)
    (hbrk : s.brk = oldBrk)
    (hc0 : c ≠ 0#64) (hc : c.toNat ≤ 4096)
    (hdvd : 4096 ∣ oldBrk.toNat) (hfit : oldBrk.toNat + (4096 + BRK_GUARD_GAP) ≤ 2 ^ 48)
    (hstart : s.brkStart.ule (oldBrk + c) = true)
    (hmap : s.mem.canMap oldBrk (4096 + BRK_GUARD_GAP) = true)
    (hphys : 4096 ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext : SepWP prog target_pc
      (((((s.setBrk (oldBrk + c)).setMem (s.mem.mapZero oldBrk 4096)).setPhysMemAvail
        (s.physMemAvail - 4096)).writeReg64
        .x0 (oldBrk + c)).setPC (pc + 4#64))
      (memRegion oldBrk 4096 ∗ P) post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hfit' : oldBrk.toNat ≤ 281474976706560 := by unfold BRK_GUARD_GAP PAGE_SIZE at hfit; omega
  have hold : pageAlignUp s.brk.toNat = oldBrk.toNat := by rw [hbrk]; exact pageAlignUp_of_dvd hdvd
  have hnew : pageAlignUp (s.readReg64 .x0).toNat = oldBrk.toNat + 4096 := by
    rw [hx0]; exact pageAlignUp_toNat_add_of_le_taskSize hdvd hc0 hc hfit'
  have hne : s.readReg64 .x0 ≠ 0#64 := by
    rw [hx0]; simpa using add_beq_zero_of_le_taskSize hc0 hc hfit'
  have hmap4096 : s.mem.canMap oldBrk 4096 = true := by
    rw [Memory.canMap, Memory.allPerm_iff] at hmap ⊢
    exact fun i hi => hmap i (by unfold BRK_GUARD_GAP PAGE_SIZE; omega)
  have hexec := execBrk_grow_ok s hne (by rw [hx0]; exact hstart)
    (by intro _; rw [hnew]; unfold BRK_GUARD_GAP PAGE_SIZE USER_VA_LIMIT at *; omega)
    (by omega)
    (by intro _; rw [hold, hnew, BitVec.ofNat_toNat, BitVec.setWidth_eq]; simpa [BRK_GUARD_GAP, PAGE_SIZE] using hmap)
    (by rw [hold, hnew]; omega)
  rw [hold, hnew, BitVec.ofNat_toNat, BitVec.setWidth_eq, hx0,
    show oldBrk.toNat + 4096 - oldBrk.toNat = 4096 by omega] at hexec
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, state_advancePC_eq_setPC (by simpa using hpc)]
  refine SepWP.to_reaches_pc hnext ?_
  rw [sepConj_assoc]
  simpa using Satisfies.mapZero hm hmap4096

/-- `svc #0` with `X8 = 222` (anonymous `mmap`, `PROT_READ | PROT_WRITE`, `MAP_PRIVATE |
    MAP_ANONYMOUS`) of `0 < len ≤ 4096` bytes at the oracle's free page `base`: maps
    `memRegion base 4096`, deducts `4096` from `s.physMemAvail`, advances the oracle and
    returns `X0 = base`. -/
theorem SepWP.step_svc_mmap_page {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc base : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen0 : s.readReg64 .x1 ≠ 0#64) (hlen : (s.readReg64 .x1).toNat ≤ 4096)
    (hbase : s.oracle.mmap s.oracleIdx = base)
    (hmin : MMAP_MIN_ADDR ≤ base.toNat) (hdvd : 4096 ∣ base.toNat) (hfit : base.toNat + 4096 ≤ 2 ^ 48)
    (hmap : s.mem.canMap base 4096 = true)
    (hphys : 4096 ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s)
    (hnext : SepWP prog target_pc
      (((((s.setMem (s.mem.mapZero base 4096)).setPhysMemAvail
        (s.physMemAvail - 4096)).nextOracle).writeReg64 .x0 base).setPC (pc + 4#64))
      (memRegion base 4096 ∗ P) post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hpage : pageAlignUp (s.readReg64 .x1).toNat = 4096 := by
    have h0 : (s.readReg64 .x1).toNat ≠ 0 := fun h =>
      hlen0 (BitVec.eq_of_toNat_eq (by simpa using h))
    unfold pageAlignUp PAGE_SIZE; omega
  have hexec := execMmap_ok s hprot hflags hoff hlen0 (by rw [hbase]; exact hmin)
    (by rw [hbase]; unfold PAGE_SIZE; omega) (by rw [hbase, hpage]; exact hfit)
    (by rw [hbase, hpage]; exact hmap) (by rw [hpage]; exact hphys)
  rw [hbase, hpage] at hexec
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, state_advancePC_eq_setPC (by simpa using hpc)]
  refine SepWP.to_reaches_pc hnext ?_
  rw [sepConj_assoc]
  simpa using Satisfies.mapZero hm hmap

/-- `svc #0` with `X8 = 64` (`write`) of an owned byte slice `buf ↦ₛ bs` (`bs.length = min count.toNat MAX_RW_COUNT`)
    to `stdout` (`isOut`, `X0 = 1`) or `stderr` (`X0 = 2`): appends `bs` to the trace,
    returns `X0 = BitVec.ofNat 64 bs.length` and leaves memory unchanged. -/
theorem SepWP.step_svc_write_stdio_clamped {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (isOut : Bool) {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hfd : s.readReg64 .x0 = (if isOut then 1#64 else 2#64))
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hlen : bs.length = min count.toNat Arm64.MAX_RW_COUNT)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64))
      ((buf ↦ₛ bs) ∗ F) post oom)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega) :
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
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have hexec : execWrite s =
      ((s.appendTrace (TraceEvent.ofBytes (if isOut then .stdout else .stderr) bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).advancePC := by
    by_cases h0 : count = 0#64
    · subst h0
      have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
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
        simp only [hbuf, hcnt, hva_f, h0_f, hcr, hrd, Bool.false_eq_true, ↓reduceIte]
      · rw [execWrite_stdout s (by simpa using hfd)]
        simp only [hbuf, hcnt, hva_f, h0_f, hcr, hrd, Bool.false_eq_true, ↓reduceIte]
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, state_advancePC_eq_setPC (by simpa using hpc)]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

/-- `svc #0` with `X8 = 64` (`write`) of an owned byte slice `buf ↦ₛ bs` (`count = bs.length`)
    to `stdout` (`isOut`, `X0 = 1`) or `stderr` (`X0 = 2`): appends the bytes to the trace,
    returns `X0 = count` and leaves memory unchanged. -/
theorem SepWP.step_svc_write_stdio {prog : Program} {target_pc : BitVec 64}
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
      ((buf ↦ₛ bs) ∗ F) post oom)
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega) :
    SepWP prog target_pc s ((buf ↦ₛ bs) ∗ F) post oom := by
  refine SepWP.step_svc_write_stdio_clamped isOut hpc hrun hfetch hfd hbuf hcnt
    (by rw [Nat.min_eq_left hmax]; exact hlen) hsvc ?_ hva
  simpa only [Nat.min_eq_left hmax, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hnext

/-- Prove `exit_ok` with `SepWP`: run from the entry state up to a final `svc #0` at `mid`
    whose execution exits with `code x` in a state satisfying the postcondition. -/
theorem exit_ok_of_sepWP_svc {α : Type} {prog : Program} {entry mid : BitVec 64}
    {code : α → BitVec 64} {spec : Spec α}
    (hfetch : prog.fetch mid = some (.system false 0#16))
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWP prog mid s0 P_init
          (fun sm P_f => (sm.mem ⊨ P_f ∗ R) →
            (prog.evalInst (.system false 0#16) sm).status = .Exited (code x) ∧
            ((prog.evalInst (.system false 0#16) sm).mem ⊨
              spec.post x s0 (prog.evalInst (.system false 0#16) sm) ∗ R))
          (fun sf => spec.onOom x s0 sf)) :
    exit_ok prog entry code spec := by
  apply exit_ok_intro
  intro x R s0 hpc hrun hpre
  obtain ⟨P, hm, hwp⟩ := h x R s0 hpc hrun hpre
  refine exits_with_of_reaches_pc (SepWP.to_reaches_pc hwp hm)
    (fun sm hpcm hrunm hmid => ?_) (fun _ _ ho => ho)
  obtain ⟨P_f, hmf, hpost⟩ := hmid
  obtain ⟨hex, hpo⟩ := hpost hmf
  exact exits_with_step hrunm (hpcm ▸ hfetch) (exits_with_refl hex hpo)

/-! ### `State.fs` / `State.tpidrEl0` `wp_norm` Lemmas, `UnmappedBetween`, Multi-Page `SYS_brk`, and Stream-Trace Helpers -/

attribute [wp_norm]
  tpidrEl0_setTpidrEl0 readReg64_setTpidrEl0 mem_setTpidrEl0 sp_setTpidrEl0 pc_setTpidrEl0
  pstate_setTpidrEl0 status_setTpidrEl0 readVReg128_setTpidrEl0
  State.tpidrEl0_advancePC State.tpidrEl0_setPC State.tpidrEl0_setMem
  State.tpidrEl0_setPState State.tpidrEl0_writeReg64 State.tpidrEl0_writeVReg128
  State.tpidrEl0_setFs State.tpidrEl0_appendTrace
  State.fs_advancePC State.fs_setPC State.fs_setPState State.fs_setMem
  State.fs_appendTrace State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).tpidrEl0 = s.tpidrEl0 := by
  unfold State.writeReg32; simp

/-- Clearing the low 12 bits of `b` rounds `b.toNat` down to a 4096-byte page boundary. -/
theorem pageMask_toNat (b : BitVec 64) :
    (b &&& 0xfffffffffffff000#64).toNat = b.toNat / 4096 * 4096 := by
  have heq : b &&& 0xfffffffffffff000#64 = b - (b &&& 4095#64) := by bv_bits
  have h1 : (b &&& 4095#64).toNat = b.toNat % 4096 := by bv_bits
  rw [heq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, h1]; omega), h1]
  omega

/-- Every byte in the virtual-address interval `[lo, hi)` is unmapped (`m.perm a = none`). -/
def UnmappedBetween (lo hi : Nat) (m : Memory) : Prop :=
  ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → m.perm a = none

theorem UnmappedBetween.of_perm_eq {lo hi : Nat} {m1 m2 : Memory}
    (h : UnmappedBetween lo hi m1) (hp : ∀ a, m2.perm a = m1.perm a) :
    UnmappedBetween lo hi m2 :=
  fun a hlo hhi => (hp a).trans (h a hlo hhi)

theorem UnmappedBetween.mono {lo lo' hi hi' : Nat} {m : Memory}
    (h : UnmappedBetween lo hi m) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    UnmappedBetween lo' hi' m :=
  fun a ha hb => h a (Nat.le_trans hlo ha) (Nat.lt_of_lt_of_le hb hhi)

theorem UnmappedBetween.canMap {lo hi : Nat} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : UnmappedBetween lo hi m)
    (hlo : lo ≤ base.toNat) (hhi : base.toNat + len ≤ hi)
    (hbnd : base.toNat + len < 2 ^ 64) :
    m.canMap base len = true := by
  unfold Memory.canMap
  induction len generalizing base with
  | zero => rfl
  | succ k ih =>
    have hp : m.perm base = none := h base hlo (by omega)
    have hnext : (base + 1#64).toNat = base.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [Memory.allPerm, hp, Option.mapped, Option.isSome_none, Bool.not_false,
      Bool.true_and]
    exact ih (by omega) (by omega) (by omega)

theorem UnmappedBetween.mapZero_above {lo hi : Nat} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : UnmappedBetween lo hi m)
    (hlo : lo ≤ base.toNat) (hbnd : base.toNat + len < 2 ^ 64) :
    UnmappedBetween (base.toNat + len) hi (m.mapZero base len) := by
  intro a ha hlt
  have hm : (m.mapZero base len).perm a =
      if (a - base).toNat < len && !(m.perm a).mapped then some Perm.rw else m.perm a := by
    conv => lhs; unfold Memory.perm Memory.mapZero; dsimp only
    cases ((a - base).toNat < len && !(m.perm a).mapped) <;> rfl
  have hnot : ¬ ((a - base).toNat < len) := by
    have := a.isLt; have := base.isLt
    rw [BitVec.toNat_sub]
    omega
  rw [hm]
  simp only [hnot, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact h a (by omega) hlt

/-- `SVC #0` rule for `SYS_brk(0)` (`X8 = 214`, `X0 = 0`): writes `s.brk` to `X0` and preserves
    memory and all process fields. -/
theorem SepWP.step_svc_brk_query {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : SepWP prog target_pc ((s.writeReg64 .x0 s.brk).setPC (pc + 4#64)) P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  apply SepWP.of_reaches_pc
  intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execBrk_query s hx0]
  have hadv : (s.writeReg64 .x0 s.brk).advancePC = (s.writeReg64 .x0 s.brk).setPC (pc + 4#64) := by
    cases s; simp [State.writeReg64, State.advancePC, State.setPC, hpc]
  rw [hadv]
  have hmem_eq : ((s.writeReg64 .x0 s.brk).setPC (pc + 4#64)).mem = s.mem := by cases s; rfl
  exact SepWP.to_reaches_pc hnext (hmem_eq ▸ hm)

/-- `SVC #0` rule for page-aligned `SYS_brk(newBrk)` (`X8 = 214`), producing
    `memRegion s.brk (newBrk.toNat - s.brk.toNat) ∗ P`. -/
theorem SepWP.step_svc_brk_grow {prog : Program} {target_pc : BitVec 64}
    {s : State} {newBrk : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = newBrk)
    (hne : newBrk ≠ 0#64)
    (hmin : s.brkStart.toNat ≤ s.brk.toNat)
    (hle : s.brk.toNat ≤ newBrk.toNat)
    (hfit : newBrk.toNat + BRK_GUARD_GAP ≤ 2 ^ 48)
    (hcur_al : s.brk.toNat % 4096 = 0)
    (hnew_al : newBrk.toNat % 4096 = 0)
    (hmap : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : newBrk.toNat - s.brk.toNat ≤ s.physMemAvail)
    (hnext :
      let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
      let s' := ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)
      SepWP prog target_pc s' (memRegion s.brk (newBrk.toNat - s.brk.toNat) ∗ P) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  apply SepWP.of_reaches_pc
  intro R hm
  have hp_cur : Arm64.pageAlignUp s.brk.toNat = s.brk.toNat :=
    pageAlignUp_of_dvd (Nat.dvd_of_mod_eq_zero hcur_al)
  have hp_new : Arm64.pageAlignUp newBrk.toNat = newBrk.toNat :=
    pageAlignUp_of_dvd (Nat.dvd_of_mod_eq_zero hnew_al)
  have hbv_brk : BitVec.ofNat 64 s.brk.toNat = s.brk := by simp
  have hule : s.brkStart.ule newBrk = true := by
    simp [BitVec.ule]; omega
  have hmap0 : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat) = true := by
    rw [Memory.canMap, Memory.allPerm_iff] at hmap ⊢
    exact fun i hi => hmap i (by omega)
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execBrk_grow_ok s (hx0 ▸ hne) (hx0 ▸ hule)
    (by intro _; rw [hx0, hp_new]; unfold USER_VA_LIMIT; exact hfit)
    (by rw [hx0, hp_cur, hp_new]; exact hle)
    (by intro _; rw [hx0, hp_cur, hp_new, hbv_brk]; exact hmap)
    (by rw [hx0, hp_cur, hp_new]; exact hphys)]
  rw [hx0, hp_cur, hp_new, hbv_brk]
  let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
  have hadv :
      ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).advancePC =
      ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64) := by
    cases s; simp [State.setBrk, State.setMem, State.setPhysMemAvail, State.writeReg64,
      State.advancePC, State.setPC, hpc]
  rw [hadv]
  have hmem_eq :
      (((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)).mem =
      m' := by
    cases s; rfl
  apply SepWP.to_reaches_pc hnext
  rw [hmem_eq, sepConj_assoc]
  exact Satisfies.mapZero hm hmap0

private theorem readBytes_mapZero_aux {m : Memory} {base : BitVec 64} {len : Nat}
    (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    ∀ (k off : Nat), off + k ≤ len →
      (m.mapZero base len).readBytes (base + BitVec.ofNat 64 off) k = List.replicate k 0#8
  | 0, _, _ => rfl
  | k + 1, off, hle => by
    have ha : InRegion base len (base + BitVec.ofNat 64 off) := by
      simp only [InRegion]
      have hsub : base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel]
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hr8 := m.read8_mapZero_of_canMap hmap ha
    have hstep : base + BitVec.ofNat 64 off + 1#64 = base + BitVec.ofNat 64 (off + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [Memory.readBytes, List.replicate_succ, hr8, hstep,
      readBytes_mapZero_aux hmap hlen k (off + 1) (by omega)]

private theorem satisfies_mapZero_bytes {P : SepProp} {m : Memory} (h : m ⊨ P)
    {base : BitVec 64} {len : Nat} (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    m.mapZero base len ⊨ (base ↦ₛ List.replicate len 0#8) ∗ P := by
  have hm := Satisfies.mapZero h hmap
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  refine (IsBlock.memRegion base len).update hblk (Nat.le_refl _) hm
    (AgreesOutside.rfl' _ base len) ⟨by simp [hlen], ?_⟩
  simpa using readBytes_mapZero_aux hmap hlen len 0 (by omega)

/-- Zero-filled byte-slice variant of `SepWP.step_svc_brk_grow`, producing
    `(s.brk ↦ₛ List.replicate (newBrk.toNat - s.brk.toNat) 0#8) ∗ P`. -/
theorem SepWP.step_svc_brk_grow_bytes {prog : Program} {target_pc : BitVec 64}
    {s : State} {newBrk : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = newBrk)
    (hne : newBrk ≠ 0#64)
    (hmin : s.brkStart.toNat ≤ s.brk.toNat)
    (hle : s.brk.toNat ≤ newBrk.toNat)
    (hfit : newBrk.toNat + BRK_GUARD_GAP ≤ 2 ^ 48)
    (hcur_al : s.brk.toNat % 4096 = 0)
    (hnew_al : newBrk.toNat % 4096 = 0)
    (hmap : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : newBrk.toNat - s.brk.toNat ≤ s.physMemAvail)
    (hnext :
      let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
      let s' := ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)
      SepWP prog target_pc s'
        ((s.brk ↦ₛ List.replicate (newBrk.toNat - s.brk.toNat) 0#8) ∗ P) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  apply SepWP.of_reaches_pc
  intro R hm
  have hp_cur : Arm64.pageAlignUp s.brk.toNat = s.brk.toNat :=
    pageAlignUp_of_dvd (Nat.dvd_of_mod_eq_zero hcur_al)
  have hp_new : Arm64.pageAlignUp newBrk.toNat = newBrk.toNat :=
    pageAlignUp_of_dvd (Nat.dvd_of_mod_eq_zero hnew_al)
  have hbv_brk : BitVec.ofNat 64 s.brk.toNat = s.brk := by simp
  have hule : s.brkStart.ule newBrk = true := by
    simp [BitVec.ule]; omega
  have hmap0 : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat) = true := by
    rw [Memory.canMap, Memory.allPerm_iff] at hmap ⊢
    exact fun i hi => hmap i (by omega)
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execBrk_grow_ok s (hx0 ▸ hne) (hx0 ▸ hule)
    (by intro _; rw [hx0, hp_new]; unfold USER_VA_LIMIT; exact hfit)
    (by rw [hx0, hp_cur, hp_new]; exact hle)
    (by intro _; rw [hx0, hp_cur, hp_new, hbv_brk]; exact hmap)
    (by rw [hx0, hp_cur, hp_new]; exact hphys)]
  rw [hx0, hp_cur, hp_new, hbv_brk]
  let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
  have hadv :
      ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).advancePC =
      ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64) := by
    cases s; simp [State.setBrk, State.setMem, State.setPhysMemAvail, State.writeReg64,
      State.advancePC, State.setPC, hpc]
  rw [hadv]
  have hmem_eq :
      (((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)).mem =
      m' := by
    cases s; rfl
  apply SepWP.to_reaches_pc hnext
  rw [hmem_eq, sepConj_assoc]
  exact satisfies_mapZero_bytes hm hmap0 (by omega)

section TraceStreamBytes
open Arm64.Process

theorem traceStreamBytes_append (stream : OutputStream) (t1 t2 : List TraceEvent) :
    ProcessOutcome.traceStreamBytes stream (t1 ++ t2) =
      ProcessOutcome.traceStreamBytes stream t1 ++ ProcessOutcome.traceStreamBytes stream t2 := by
  unfold ProcessOutcome.traceStreamBytes
  exact List.filterMap_append

theorem traceStreamBytes_ofBytes_stdout :
    ∀ bs : List (BitVec 8),
      ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stdout bs) = bs ∧
      ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stdout bs) = []
  | [] => ⟨rfl, rfl⟩
  | b :: bs => by
    obtain ⟨ih1, ih2⟩ := traceStreamBytes_ofBytes_stdout bs
    exact ⟨congrArg (b :: ·) ih1, ih2⟩

theorem traceStreamBytes_ofBytes_stderr :
    ∀ bs : List (BitVec 8),
      ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stderr bs) = [] ∧
      ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stderr bs) = bs
  | [] => ⟨rfl, rfl⟩
  | b :: bs => by
    obtain ⟨ih1, ih2⟩ := traceStreamBytes_ofBytes_stderr bs
    exact ⟨ih1, congrArg (b :: ·) ih2⟩

@[simp]
theorem traceStreamBytes_stdout_ofBytes (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stdout bs) = bs :=
  (traceStreamBytes_ofBytes_stdout bs).1

@[simp]
theorem traceStreamBytes_stderr_ofBytes_stdout (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stdout bs) = [] :=
  (traceStreamBytes_ofBytes_stdout bs).2

@[simp]
theorem traceStreamBytes_stdout_ofBytes_stderr (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stderr bs) = [] :=
  (traceStreamBytes_ofBytes_stderr bs).1

@[simp]
theorem traceStreamBytes_stderr_ofBytes (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stderr bs) = bs :=
  (traceStreamBytes_ofBytes_stderr bs).2

@[simp]
theorem traceStreamBytes_ofBytes_fd3_stdout (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes (OutputStream.ofFd 3#64) bs) = [] := by
  induction bs with | nil => rfl | cons _ _ ih => exact ih

@[simp]
theorem traceStreamBytes_ofBytes_fd3_stderr (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes (OutputStream.ofFd 3#64) bs) = [] := by
  induction bs with | nil => rfl | cons _ _ ih => exact ih

end TraceStreamBytes

/-! ### `madvise` (`MADV_FREE` and `MADV_DONTNEED`) `SepWP` Step Lemmas -/

/-- `SVC #0` rule for `madvise(addr, len, MADV_FREE)` (`X8 = 233`, `X2 = 8`) on an anonymous
    page-aligned region `memRegion addr sz ∗ memMapped addr sz`, producing
    `memRegionLazy addr sz ∗ memMapped addr sz` and returning `X0 = 0`. -/
theorem SepWP.step_svc_madvise_free {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : s.readReg64 .x2 = 8#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_reg : s.mem ⊨ memRegion addr sz ∗ ((memMapped addr sz ∗ F) ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hm_map : s.mem ⊨ memMapped addr sz ∗ (memRegion addr sz ∗ F ∗ R) := by ac_nf at hm ⊢
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [(IsBlock.memRegion addr sz).perm_rw hm_reg (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hmap : s.mem.allPerm (·.mapped) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [(IsBlock.memRegion addr sz).perm_rw hm_reg (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hanon : s.mem.allAnon addr sz = true := Satisfies.allAnon_of_memMapped hm_map
  have hexec := execMadvise_free_ok s hadv (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
    (by rw [haddr, hlen, hsz]; exact hmap)
    (by rw [haddr, hlen, hsz]; exact hanon)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  have hm' : s.mem.madvFreeNonFrozen addr sz ⊨
      (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.madvFreeNonFrozen hm_reg
  exact SepWP.to_reaches_pc (hnext (s.mem.madvFreeNonFrozen addr sz)) hm'

/-- `SVC #0` rule for `madvise(addr, len, MADV_DONTNEED)` (`X8 = 233`, `X2 = 4`) on an anonymous
    lazy-free region `memRegionLazy addr sz ∗ memMapped addr sz`, clearing `lazyFree` and upgrading
    back to `memRegion addr sz ∗ memMapped addr sz` with `X0 = 0`. -/
theorem SepWP.step_svc_madvise_dontneed_lazy {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : s.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_lz : s.mem ⊨ memRegionLazy addr sz ∗ ((memMapped addr sz ∗ F) ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hm_map : s.mem ⊨ memMapped addr sz ∗ (memRegionLazy addr sz ∗ F ∗ R) := by ac_nf at hm ⊢
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [Satisfies.perm_rw_of_memRegionLazy hm_lz (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hmap : s.mem.allPerm (·.mapped) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [Satisfies.perm_rw_of_memRegionLazy hm_lz (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hanon : s.mem.allAnon addr sz = true := Satisfies.allAnon_of_memMapped hm_map
  have hexec := execMadvise_dontneed_ok s hadv (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
    (by rw [haddr, hlen, hsz]; exact hmap)
    (by rw [haddr, hlen, hsz]; exact hanon)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  have hm' : s.mem.zeroNonFrozen addr sz ⊨
      (memRegion addr sz ∗ (memMapped addr sz ∗ F)) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.zeroNonFrozen_of_memRegionLazy hm_lz
  exact SepWP.to_reaches_pc (hnext (s.mem.zeroNonFrozen addr sz)) hm'

/-- `SVC #0` rule for `madvise(addr, len, MADV_DONTNEED)` (`X8 = 233`, `X2 = 4`) on an anonymous
    lazy-free region `memRegionLazy addr sz ∗ memMapped addr sz`, clearing `lazyFree` and exposing
    the zero-filled byte slice `(addr ↦ₛ List.replicate sz 0#8) ∗ memMapped addr sz` with `X0 = 0`. -/
theorem SepWP.step_svc_madvise_dontneed_lazy_bytes {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : s.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        ((addr ↦ₛ List.replicate sz 0#8) ∗ (memMapped addr sz ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_lz : s.mem ⊨ memRegionLazy addr sz ∗ ((memMapped addr sz ∗ F) ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hm_map : s.mem ⊨ memMapped addr sz ∗ (memRegionLazy addr sz ∗ F ∗ R) := by ac_nf at hm ⊢
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [Satisfies.perm_rw_of_memRegionLazy hm_lz (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hmap : s.mem.allPerm (·.mapped) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [Satisfies.perm_rw_of_memRegionLazy hm_lz (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hanon : s.mem.allAnon addr sz = true := Satisfies.allAnon_of_memMapped hm_map
  have hexec := execMadvise_dontneed_ok s hadv (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
    (by rw [haddr, hlen, hsz]; exact hmap)
    (by rw [haddr, hlen, hsz]; exact hanon)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  have hm' : s.mem.zeroNonFrozen addr sz ⊨
      ((addr ↦ₛ List.replicate sz 0#8) ∗ (memMapped addr sz ∗ F)) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.zeroNonFrozen_pointsToBytes_of_memRegionLazy (by omega) hm_lz
  exact SepWP.to_reaches_pc (hnext (s.mem.zeroNonFrozen addr sz)) hm'

/-- `SVC #0` rule for `madvise(addr, len, MADV_DONTNEED)` (`X8 = 233`, `X2 = 4`) on an anonymous
    read-write region `memRegion addr sz ∗ memMapped addr sz`, zero-filling the region and
    returning `memRegion addr sz ∗ memMapped addr sz` with `X0 = 0`. -/
theorem SepWP.step_svc_madvise_dontneed {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : s.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_lz : s.mem ⊨ (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) ∗ R := by
    rw [sepConj_assoc] at hm ⊢
    exact Satisfies.memRegion_to_lazy hm
  exact SepWP.to_reaches_pc
    (SepWP.step_svc_madvise_dontneed_lazy hpc hrun hfetch hx8 haddr hlen hadv hal hlenNe hsz hfit hnext hsvc)
    hm_lz

/-- `SVC #0` rule for `madvise(addr, len, MADV_DONTNEED)` (`X8 = 233`, `X2 = 4`) on an anonymous
    read-write region `memRegion addr sz ∗ memMapped addr sz`, exposing the zero-filled byte slice
    `(addr ↦ₛ List.replicate sz 0#8) ∗ memMapped addr sz` with `X0 = 0`. -/
theorem SepWP.step_svc_madvise_dontneed_bytes {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : s.readReg64 .x2 = 4#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        ((addr ↦ₛ List.replicate sz 0#8) ∗ (memMapped addr sz ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_lz : s.mem ⊨ (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) ∗ R := by
    rw [sepConj_assoc] at hm ⊢
    exact Satisfies.memRegion_to_lazy hm
  exact SepWP.to_reaches_pc
    (SepWP.step_svc_madvise_dontneed_lazy_bytes hpc hrun hfetch hx8 haddr hlen hadv hal hlenNe hsz hfit hnext hsvc)
    hm_lz

/-- `SVC #0` rule for no-op hint `madvise(addr, len, advice)` (`X8 = 233`,
    `advice ∈ {MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL, MADV_WILLNEED, MADV_HUGEPAGE,
    MADV_NOHUGEPAGE, MADV_DONTDUMP, MADV_DODUMP}`) on a mapped read-write region
    `memRegion addr sz ∗ F`, leaving memory unchanged and returning `X0 = 0`. -/
theorem SepWP.step_svc_madvise_noop {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 233#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hadv : (s.readReg64 .x2 == MADV_NORMAL || s.readReg64 .x2 == MADV_RANDOM ||
      s.readReg64 .x2 == MADV_SEQUENTIAL || s.readReg64 .x2 == MADV_WILLNEED ||
      s.readReg64 .x2 == MADV_HUGEPAGE || s.readReg64 .x2 == MADV_NOHUGEPAGE ||
      s.readReg64 .x2 == MADV_DONTDUMP || s.readReg64 .x2 == MADV_DODUMP) = true)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : SepWP prog target_pc ((s.writeReg64 .x0 0#64).setPC (pc + 4#64))
      (memRegion addr sz ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMadvise s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ F) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_reg : s.mem ⊨ memRegion addr sz ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true :=
    Satisfies.allPerm_not_frozen_of_memRegion hm_reg
  have hmap : s.mem.allPerm (·.mapped) addr sz = true :=
    Satisfies.allPerm_mapped_of_memRegion hm_reg
  have hexec := execMadvise_noop_ok s hadv (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
    (by rw [haddr, hlen, hsz]; exact hmap)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, state_advancePC_eq_setPC (by simpa using hpc)]
  exact SepWP.to_reaches_pc hnext hm

/-! ### `munmap` (`SYS_MUNMAP = 215`) and `mprotect` (`SYS_MPROTECT = 226`) `SepWP` Step Lemmas -/

/-- `SVC #0` rule for `munmap(addr, len)` (`X8 = 215`) on a page-aligned read-write region
    `memRegion addr sz ∗ memMapped addr sz`, consuming both the physical region and the mapping
    reservation token, refunding `s.mem.countRw addr sz` to `s.physMemAvail`, and returning `X0 = 0`. -/
theorem SepWP.step_svc_munmap {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 215#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ (m' : Memory) (phys' : Nat),
      SepWP prog target_pc ((((s.setMem m').setPhysMemAvail phys').writeReg64 .x0 0#64).setPC (pc + 4#64))
        F post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMunmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_reg : s.mem ⊨ memRegion addr sz ∗ (memMapped addr sz ∗ (F ∗ R)) := by
    simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true :=
    Satisfies.allPerm_not_frozen_of_memRegion hm_reg
  have hexec := execMunmap_ok s (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  exact SepWP.to_reaches_pc
    (hnext (s.mem.unmapNonFrozen addr sz) (s.physMemAvail + s.mem.countRw addr sz))
    (Satisfies.unmapNonFrozen hm_reg)

/-- `SVC #0` rule for `munmap(addr, len)` (`X8 = 215`) on a page-aligned `PROT_NONE` region
    `memRegionProtNone addr sz ∗ memMapped addr sz`, consuming both the region and its mapping
    reservation token and returning `X0 = 0`. -/
theorem SepWP.step_svc_munmap_protNone {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 215#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ (m' : Memory) (phys' : Nat),
      SepWP prog target_pc ((((s.setMem m').setPhysMemAvail phys').writeReg64 .x0 0#64).setPC (pc + 4#64))
        F post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMunmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionProtNone addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_pn : s.mem ⊨ memRegionProtNone addr sz ∗ (memMapped addr sz ∗ (F ∗ R)) := by
    simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true :=
    Satisfies.allPerm_not_frozen_of_memRegionProtNone hm_pn
  have hexec := execMunmap_ok s (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  exact SepWP.to_reaches_pc
    (hnext (s.mem.unmapNonFrozen addr sz) (s.physMemAvail + s.mem.countRw addr sz))
    (Satisfies.unmapNonFrozen_protNone hm_pn)

/-- `SVC #0` rule for `munmap(addr, len)` (`X8 = 215`) on a page-aligned lazy-free region
    `memRegionLazy addr sz ∗ memMapped addr sz`, consuming both the region and its mapping
    reservation token and returning `X0 = 0`. -/
theorem SepWP.step_svc_munmap_lazy {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 215#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ (m' : Memory) (phys' : Nat),
      SepWP prog target_pc ((((s.setMem m').setPhysMemAvail phys').writeReg64 .x0 0#64).setPC (pc + 4#64))
        F post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMunmap s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionLazy addr sz ∗ (memMapped addr sz ∗ F)) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_lz : s.mem ⊨ memRegionLazy addr sz ∗ (memMapped addr sz ∗ (F ∗ R)) := by
    simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true := by
    rw [Memory.allPerm_iff]; intro i hi
    rw [Satisfies.perm_rw_of_memRegionLazy hm_lz (inRegion_base_add addr sz i hi (by omega))]; rfl
  have hexec := execMunmap_ok s (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, state_advancePC_eq_setPC (by simpa using hpc)]
  exact SepWP.to_reaches_pc
    (hnext (s.mem.unmapNonFrozen addr sz) (s.physMemAvail + s.mem.countRw addr sz))
    (Satisfies.unmapNonFrozen_lazy hm_lz)

/-- `SVC #0` rule for `mprotect(addr, len, PROT_NONE)` (`X8 = 226`, `X2 = 0`) on a page-aligned
    read-write region `memRegion addr sz ∗ F`, demoting permissions to `memRegionProtNone addr sz ∗ F`
    and returning `X0 = 0`. -/
theorem SepWP.step_svc_mprotect_protNone {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 226#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hprot : s.readReg64 .x2 = 0#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (memRegionProtNone addr sz ∗ F) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMprotect s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr sz ∗ F) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_reg : s.mem ⊨ memRegion addr sz ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true :=
    Satisfies.allPerm_not_frozen_of_memRegion hm_reg
  have hmap : s.mem.allPerm (·.mapped) addr sz = true :=
    Satisfies.allPerm_mapped_of_memRegion hm_reg
  have hexec := execMprotect_ok s (Or.inl hprot) (haddr ▸ hal) (hlen ▸ hlenNe)
    (by rw [haddr, hlen, hsz]; exact hfit)
    (by rw [haddr, hlen, hsz]; exact hfrz)
    (by rw [haddr, hlen, hsz]; exact hmap)
    (fun h3 => by rw [hprot] at h3; contradiction)
  have hsetPhys : ∀ m' : Memory, (s.setMem m').setPhysMemAvail s.physMemAvail = s.setMem m' := by
    intro m'; cases s; rfl
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, haddr, hlen, hsz, hprot]
  simp only [beq_self_eq_true, ↓reduceIte, hsetPhys]
  rw [state_advancePC_eq_setPC (by simpa using hpc)]
  have hm' : s.mem.setPermNonFrozen addr sz Perm.protNone ⊨ (memRegionProtNone addr sz ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.setPermProtNone_of_memRegion hm_reg
  exact SepWP.to_reaches_pc (hnext (s.mem.setPermNonFrozen addr sz Perm.protNone)) hm'

/-- `SVC #0` rule for `mprotect(addr, len, PROT_READ | PROT_WRITE)` (`X8 = 226`, `X2 = 3`) on a
    page-aligned `PROT_NONE` region `memRegionProtNone addr sz ∗ F`: either promotes permissions to
    `memRegion addr sz ∗ F` and returns `X0 = 0`, or transitions to `.OutOfMemory`. -/
theorem SepWP.step_svc_mprotect_rw {prog : Program} {target_pc : BitVec 64}
    {s : State} {pc addr len : BitVec 64} {sz : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 226#64)
    (haddr : s.readReg64 .x0 = addr)
    (hlen : s.readReg64 .x1 = len)
    (hprot : s.readReg64 .x2 = 3#64)
    (hal : addr.toNat % PAGE_SIZE = 0)
    (hlenNe : len ≠ 0#64)
    (hsz : pageAlignUp len.toNat = sz)
    (hfit : addr.toNat + sz ≤ 2 ^ 48)
    (hnext : ∀ (m' : Memory) (phys' : Nat),
      SepWP prog target_pc ((((s.setMem m').setPhysMemAvail phys').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (memRegion addr sz ∗ F) post oom)
    (hoom : ∀ R, (s.mem ⊨ (memRegionProtNone addr sz ∗ F) ∗ R) →
      (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢);
      first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMprotect s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegionProtNone addr sz ∗ F) post oom := by
  let _ := hx8
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm_pn : s.mem ⊨ memRegionProtNone addr sz ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) addr sz = true :=
    Satisfies.allPerm_not_frozen_of_memRegionProtNone hm_pn
  have hmap : s.mem.allPerm (·.mapped) addr sz = true :=
    Satisfies.allPerm_mapped_of_memRegionProtNone hm_pn
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc]
  by_cases hphys :
      pageAlignUp (s.readReg64 .x1).toNat -
        s.mem.countRw (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) ≤
        s.physMemAvail
  · have hexec := execMprotect_ok s (Or.inr hprot) (haddr ▸ hal) (hlen ▸ hlenNe)
      (by rw [haddr, hlen, hsz]; exact hfit)
      (by rw [haddr, hlen, hsz]; exact hfrz)
      (by rw [haddr, hlen, hsz]; exact hmap)
      (fun _ => hphys)
    have hnot0 : (3#64 == (0#64 : BitVec 64)) = false := rfl
    rw [hexec, haddr, hlen, hsz, hprot, hnot0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [state_advancePC_eq_setPC (by simpa using hpc)]
    have hm' : s.mem.setPermNonFrozen addr sz Perm.rw ⊨ (memRegion addr sz ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.setPermRw_of_memRegionProtNone hm_pn
    exact SepWP.to_reaches_pc
      (hnext (s.mem.setPermNonFrozen addr sz Perm.rw)
        (s.physMemAvail - (sz - s.mem.countRw addr sz))) hm'
  · have hexec := execMprotect_rw_oom s hprot (haddr ▸ hal) (hlen ▸ hlenNe)
      (by rw [haddr, hlen, hsz]; exact hfit)
      (by rw [haddr, hlen, hsz]; exact hfrz)
      (by rw [haddr, hlen, hsz]; exact hmap)
      hphys
    rw [hexec]
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)

end ProofLib
