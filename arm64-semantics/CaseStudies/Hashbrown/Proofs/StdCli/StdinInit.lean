/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import CaseStudies.Hashbrown.Proofs.StdCli.SyscallsAndStderr
public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutFlush
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.StdStartup.MemOps
public import ProofLib.MallocngIface
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Placement-Generic `Stdin` `OnceLock` and `RawVecInner` Code Bundle

Symbolic `CodeChunk` bundle (`HbStdinAndVecCode`) for `OnceLock<Stdin>::initialize`,
`RawVecInner::{finish_grow, do_reserve_and_handle}`, and `default_read_to_end::small_probe_read`
parameterized by `HbCliLayout`, together with `HbStdinInv` and `hbStdinOnceLockInit_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## Symbolic code bundle -/

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))

def hbStdinOutlinedOnceCallWords : List (BitVec 32) :=
  [0x910043e2#32, 0x52800021#32, 0xa90027e8#32, 0xf9000bea#32]

def hbStdinOnceLockEntryWords : List (BitVec 32) :=
  [0x88dffd08#32, 0x35000048#32, 0xd65f03c0#32,
   0xd100c3ff#32, 0xa9027bfd#32, 0x910083fd#32, 0xd503201f#32]

def hbStdinOnceLockMidWords : List (BitVec 32) :=
  [0xd10007a9#32, 0x910003ea#32, 0xd503201f#32]

def hbRdlAllocWords : List (BitVec 32) :=
  [0xf100403f#32, 0xaa0003e2#32, 0x540000a8#32,
   0xeb02003f#32, 0x54000068#32, 0xaa0203e0#32]

def hbRdlReallocWords : List (BitVec 32) :=
  [0xd10103ff#32, 0xa9017bfd#32, 0xa90257f6#32, 0xa9034ff4#32,
   0x910043fd#32, 0xaa0303f3#32, 0xaa0103f4#32, 0xf100405f#32,
   0x54000128#32, 0xeb13005f#32, 0x540000e8#32, 0xaa1303e1#32,
   0xa9434ff4#32, 0xa94257f6#32, 0xa9417bfd#32, 0x910103ff#32]

def hbStdinInitClosurePreWords : List (BitVec 32) :=
  [0xa9be7bfd#32, 0xf9000bf3#32, 0x910003fd#32, 0xf9400008#32,
   0xf9400113#32, 0xf900011f#32, 0xb40001f3#32]

def hbStdinInitClosureMidWords : List (BitVec 32) :=
  [0x52840000#32, 0x52800021#32]

def hbStdinInitClosurePostWords : List (BitVec 32) :=
  [0xb40001a0#32, 0x52840008#32, 0xb900027f#32, 0x3900127f#32,
   0xa900a260#32, 0xa901fe7f#32, 0x3900a27f#32, 0xf9400bf3#32,
   0xa8c27bfd#32, 0xd65f03c0#32]

def hbRawVecFinishGrowPreWords : List (BitVec 32) :=
  [0xa9bd7bfd#32, 0xf9000bf5#32, 0xa9024ff4#32, 0x910003fd#32,
   0x9bc37ca8#32, 0xaa0003f3#32, 0xaa1f03e9#32, 0x5280010a#32,
   0xeb0803ff#32, 0x52800028#32, 0x540003a1#32, 0x9b037cb4#32,
   0xd2f0000b#32, 0xaa0403f5#32, 0xcb04016b#32, 0xeb0b029f#32,
   0x540002e8#32, 0xb4000101#32, 0x9b017ca1#32, 0xaa0203e0#32,
   0xaa1503e2#32, 0xaa1403e3#32]

def hbRawVecFinishGrowMidWords : List (BitVec 32) :=
  [0xb5000180#32, 0x14000007#32, 0xb4000134#32]

def hbRawVecFinishGrowAllocArgsWords : List (BitVec 32) :=
  [0xaa1403e0#32, 0xaa1503e1#32]

def hbRawVecFinishGrowPostWords : List (BitVec 32) :=
  [0xaa1f03e8#32, 0xf9000660#32, 0x5280020a#32, 0xaa1403e9#32,
   0xf82a6a69#32, 0xf9000268#32, 0xa9424ff4#32, 0xf9400bf5#32,
   0xa8c37bfd#32, 0xd65f03c0#32]

def hbRawVecDoReservePreWords : List (BitVec 32) :=
  [0xd10103ff#32, 0xa9027bfd#32, 0xa9034ff4#32, 0x910083fd#32,
   0xab010048#32, 0x54000342#32, 0xa9400801#32, 0xaa0403e5#32,
   0x5280010a#32, 0xaa0303e4#32, 0xaa0003f3#32, 0x910023e0#32,
   0xd37ff829#32, 0xeb09011f#32, 0x9a898108#32, 0xf10004bf#32,
   0x52800089#32, 0x9a890149#32, 0xeb09011f#32, 0x9a898114#32,
   0xaa1403e3#32]

def hbRawVecDoReservePostWords : List (BitVec 32) :=
  [0xf94007e8#32, 0xf100051f#32, 0x54000120#32, 0xf9400be8#32,
   0xa9002274#32, 0xa9434ff4#32, 0xa9427bfd#32, 0x910103ff#32,
   0xd65f03c0#32]

def hbSmallProbeEntryWords : List (BitVec 32) :=
  [0xd10243ff#32, 0xa9037bfd#32, 0xf90023fb#32, 0xa90567fa#32,
   0xa9065ff8#32, 0xa90757f6#32, 0xa9084ff4#32, 0x9100c3fd#32,
   0x6f00e400#32, 0xaa0003f3#32, 0x910003e1#32, 0x2a1f03e0#32,
   0x52800402#32, 0xad0003e0#32]

def hbSmallProbeMidWords : List (BitVec 32) :=
  [0xb100041f#32, 0x54000380#32, 0xaa0003f4#32, 0xf100841f#32,
   0x540006e2#32, 0xf9400a76#32, 0xf9400268#32, 0xcb160108#32,
   0xeb08029f#32, 0x54000708#32, 0xb40000d4#32, 0xf9400668#32,
   0x910003e1#32, 0xaa1403e2#32, 0x8b160100#32]

def hbSmallProbeExitWords : List (BitVec 32) :=
  [0xaa1f03f5#32, 0x8b1402c8#32, 0xf9000a68#32, 0xaa1503e0#32,
   0xaa1403e1#32, 0xa9484ff4#32, 0xf94023fb#32, 0xa94757f6#32,
   0xa9465ff8#32, 0xa94567fa#32, 0xa9437bfd#32, 0x910243ff#32,
   0xd65f03c0#32]

def hbSmallProbeGrowCallWords : List (BitVec 32) :=
  [0xaa1303e0#32, 0xaa1603e1#32, 0xaa1403e2#32, 0x52800023#32,
   0x52800024#32]

def hbStdinAndVecChunks (C : HbCliLayout) : List CodeChunk :=
  [ -- `outlinedOnceCall` (`OUTLINED_FUNCTION_2`, 5 insns)
    .words C.outlinedOnceCallAddr hbStdinOutlinedOnceCallWords,
    .instrs C.outlinedOnceCallAddr 0x10 [iB (C.outlinedOnceCallAddr + 0x10#64) C.std.onceCallAddr],
    -- `outlinedFn72` (`OUTLINED_FUNCTION_72`, 3 insns)
    .words C.outlinedFn72Addr [0xd503201f#32],
    .instrs C.outlinedFn72Addr 0x04 [iAdr .x4 (C.outlinedFn72Addr + 0x04#64) C.onceLockPanicLocAddr],
    .words (C.outlinedFn72Addr + 0x08#64) [0xd65f03c0#32],
    -- `OnceLock<Stdin>::initialize`
    .instrs0 C.stdinOnceLockInitAddr
      [iAdrp .x8 C.stdinOnceLockInitAddr (C.stdinGlobalAddr + 0x30#64),
       iAddLo12 .x8 .x8 (C.stdinGlobalAddr + 0x30#64)],
    .words (C.stdinOnceLockInitAddr + 0x08#64) hbStdinOnceLockEntryWords,
    .instrs C.stdinOnceLockInitAddr 0x24
      [iAdr .x8 (C.stdinOnceLockInitAddr + 0x24#64) C.stdinGlobalAddr],
    .words (C.stdinOnceLockInitAddr + 0x28#64) hbStdinOnceLockMidWords,
    .instrs C.stdinOnceLockInitAddr 0x34
      [iAdr .x3 (C.stdinOnceLockInitAddr + 0x34#64) C.stdinInitVtableAddr,
       iBl (C.stdinOnceLockInitAddr + 0x38#64) C.outlinedFn72Addr],
    .words (C.stdinOnceLockInitAddr + 0x3c#64) [0x9100c100#32],
    .instrs C.stdinOnceLockInitAddr 0x40 [iBl (C.stdinOnceLockInitAddr + 0x40#64) C.outlinedOnceCallAddr],
    .words (C.stdinOnceLockInitAddr + 0x44#64) [0xa9427bfd#32, 0x9100c3ff#32, 0xd65f03c0#32],
    -- Allocator shims (`__rust_no_alloc_shim_is_unstable_v2`, `__rust_alloc`, `__rdl_alloc`,
    -- `__rust_realloc`, `__rdl_realloc`)
    .words C.rustAllocShimAddr [0xd65f03c0#32],
    .instrs0 C.rustAllocAddr [iB C.rustAllocAddr C.rdlAllocAddr],
    .words C.rdlAllocAddr hbRdlAllocWords,
    .instrs C.rdlAllocAddr 0x18 [iB (C.rdlAllocAddr + 0x18#64) C.mallocng.mallocAddr],
    .instrs0 C.rustReallocAddr [iB C.rustReallocAddr C.rdlReallocAddr],
    .words C.rdlReallocAddr hbRdlReallocWords,
    .instrs C.rdlReallocAddr 0x40 [iB (C.rdlReallocAddr + 0x40#64) C.mallocng.reallocAddr],
    -- `stdinInitClosure`
    .words C.stdinInitClosureAddr hbStdinInitClosurePreWords,
    .instrs C.stdinInitClosureAddr 0x1c [iBl (C.stdinInitClosureAddr + 0x1c#64) C.rustAllocShimAddr],
    .words (C.stdinInitClosureAddr + 0x20#64) hbStdinInitClosureMidWords,
    .instrs C.stdinInitClosureAddr 0x28 [iBl (C.stdinInitClosureAddr + 0x28#64) C.rustAllocAddr],
    .words (C.stdinInitClosureAddr + 0x2c#64) hbStdinInitClosurePostWords,
    -- `RawVecInner::finish_grow`
    .words C.rawVecFinishGrowAddr hbRawVecFinishGrowPreWords,
    .instrs C.rawVecFinishGrowAddr 0x58 [iBl (C.rawVecFinishGrowAddr + 0x58#64) C.rustReallocAddr],
    .words (C.rawVecFinishGrowAddr + 0x5c#64) hbRawVecFinishGrowMidWords,
    .instrs C.rawVecFinishGrowAddr 0x68 [iBl (C.rawVecFinishGrowAddr + 0x68#64) C.rustAllocShimAddr],
    .words (C.rawVecFinishGrowAddr + 0x6c#64) hbRawVecFinishGrowAllocArgsWords,
    .instrs C.rawVecFinishGrowAddr 0x74 [iBl (C.rawVecFinishGrowAddr + 0x74#64) C.rustAllocAddr],
    .words (C.rawVecFinishGrowAddr + 0x78#64) [0xb50000a0#32],
    .words (C.rawVecFinishGrowAddr + 0x8c#64) hbRawVecFinishGrowPostWords,
    -- `RawVecInner::do_reserve_and_handle`
    .words C.rawVecDoReserveAddr hbRawVecDoReservePreWords,
    .instrs C.rawVecDoReserveAddr 0x54 [iBl (C.rawVecDoReserveAddr + 0x54#64) C.rawVecFinishGrowAddr],
    .words (C.rawVecDoReserveAddr + 0x58#64) hbRawVecDoReservePostWords,
    -- `default_read_to_end::small_probe_read`
    .words C.smallProbeReadAddr hbSmallProbeEntryWords,
    .instrs C.smallProbeReadAddr 0x38 [iBl (C.smallProbeReadAddr + 0x38#64) C.readAddr],
    .words (C.smallProbeReadAddr + 0x3c#64) hbSmallProbeMidWords,
    .instrs C.smallProbeReadAddr 0x78 [iBl (C.smallProbeReadAddr + 0x78#64) C.std.memcpyAddr],
    .words (C.smallProbeReadAddr + 0x7c#64) hbSmallProbeExitWords,
    .words (C.smallProbeReadAddr + 0x140#64) hbSmallProbeGrowCallWords,
    .instrs C.smallProbeReadAddr 0x154 [iBl (C.smallProbeReadAddr + 0x154#64) C.rawVecDoReserveAddr],
    .words (C.smallProbeReadAddr + 0x158#64) [0xf9400a76#32, 0x17ffffc3#32] ]

def HbStdinAndVecCode (P : Program) (C : HbCliLayout) : Prop :=
  CodeChunks P (hbStdinAndVecChunks C)

section WordTreeCheck
open ProofLib.ProgramReflection

private theorem hbStdinCodeChunk_withSvc {P : Program} {svc : State → State} :
    ∀ {c : CodeChunk}, c.holds P → c.holds (P.withSvc svc)
  | .words _ _, h => h
  | .instrs0 _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi
  | .instrs _ _ _, h => fun i hi => by rw [Program.withSvc_fetch]; exact h i hi

private theorem hbStdinCodeChunks_withSvc {P : Program} {svc : State → State} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeChunks (P.withSvc svc) cs
  | [], _ => trivial
  | [_], h => hbStdinCodeChunk_withSvc h
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨hbStdinCodeChunk_withSvc h1, hbStdinCodeChunks_withSvc h2⟩

theorem HbStdinAndVecCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbStdinAndVecCode P C) :
    HbStdinAndVecCode (P.withSvc svc) C :=
  hbStdinCodeChunks_withSvc h

private theorem hbStdinCodeChunks_of_check {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, hbStdinCodeChunks_of_check hc h.2⟩

def checkHbStdinAndVecCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbStdinAndVecChunks C).all (checkCodeChunk base t)

theorem hbStdinAndVecCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbStdinAndVecCode C P.base t = true) :
    HbStdinAndVecCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  exact hbStdinCodeChunks_of_check hc hok

end WordTreeCheck

/-! ## Code unpacking and allocator call helpers -/

def fetchAtAcc (P : Program) (base : BitVec 64) : Nat → List Instr → Prop → Prop
  | _, [], acc => acc
  | off, x :: xs, acc => P.fetch (base + BitVec.ofNat 64 off) = some x ∧ fetchAtAcc P base (off + 4) xs acc

theorem fetchAtAcc_of_fn {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr),
      (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) →
      fetchAtAcc P base off is acc
  | _, [], _ => hacc
  | off, _ :: xs, h =>
    ⟨by simpa using h 0 (Nat.zero_lt_succ _),
     fetchAtAcc_of_fn hacc (off + 4) xs fun i hi => by
       simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩

def chunkStepAcc (P : Program) (acc : Prop) : CodeChunk → Prop
  | .words a ws => P.hasCode a ws ∧ acc
  | .instrs0 b is => fetchAtAcc P b 0 is acc
  | .instrs b o is => fetchAtAcc P b o is acc

def chunksStepFacts (P : Program) : List CodeChunk → Prop
  | [] => True
  | c :: cs => chunkStepAcc P (chunksStepFacts P cs) c

theorem chunkToStepAcc {P : Program} {acc : Prop} (hacc : acc) :
    ∀ {c : CodeChunk}, c.holds P → chunkStepAcc P acc c
  | .words _ _, h => ⟨h, hacc⟩
  | .instrs0 _ _, h => fetchAtAcc_of_fn hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => fetchAtAcc_of_fn hacc o _ fun i hi => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi

theorem chunksToStepFacts {P : Program} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → chunksStepFacts P cs
  | [], _ => trivial
  | [_], h => chunkToStepAcc trivial h
  | _ :: _ :: _, ⟨h1, h2⟩ => chunkToStepAcc (chunksToStepFacts h2) h1

local macro "unpack_hb_stdin_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := chunksToStepFacts $h
  simp only [$chunks:ident, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

theorem bv64_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_lin
local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "unpack_cells " k:num : tactic => `(tactic| (
  conv => arg 4; (try simp only [Nat.reduceMul])
  cells_unfold
  conv => arg 4; (try simp only [sepExists_sepConj_left, sepExists_sepConj_right])
  iterate $k (apply SepWP.exists_left; intro _)))
local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]; cells_unfold
  try simp only [BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))
local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *] <;> try bv_lin)

theorem vmHeapTransport {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s0 sf : State}
    (h : VmFieldsPreserved s0 sf) :
    M.Heap γ lc blk s0 ⊢ M.Heap γ lc blk sf :=
  M.heap_transport h.brk_eq h.brkStart_eq h.physMemAvail_eq h.perm_eq

theorem vmOfStdState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    VmFieldsPreserved s0 sf :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem mono_head_sat {m : Memory} {A A' P Rest : SepProp} (himp : A ⊢ A') (hm : m ⊨ P)
    (hsplit : P = A ∗ Rest := by sep_frame) :
    m ⊨ A' ∗ Rest :=
  Satisfies.mono (hsplit ▸ sepConj_mono himp (Entails.refl Rest)) hm

theorem sepWP_mono_atom {prog : Program} {target_pc : BitVec 64} {s : State}
    {A A' P Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (himp : A ⊢ A') (hsplit : P = A ∗ Rest := by sep_frame)
    (h : SepWP prog target_pc s (A' ∗ Rest) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.weaken_pre (hsplit ▸ sepConj_mono himp (Entails.refl Rest)) h

theorem sepConj_pull_pure {φ : Prop} (A B : SepProp) : A ∗ (⌜φ⌝ ∗ B) = ⌜φ⌝ ∗ (A ∗ B) := by
  rw [← sepConj_assoc, sepConj_comm A, sepConj_assoc]

theorem MallocngStatePreserved.refl (s : State) : MallocngStatePreserved s s :=
  ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl s.mem⟩

theorem MallocngStatePreserved.trans {s0 s1 s2 : State}
    (h01 : MallocngStatePreserved s0 s1) (h12 : MallocngStatePreserved s1 s2) :
    MallocngStatePreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, Memory.KeepsFrozen.trans h01.2.2.2.2 h12.2.2.2.2⟩

theorem subroutine_ok_of_sepWP_frozen {α : Type} {prog : Program} {entry_pc : BitVec 64}
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

private theorem step_ldar32_words_stdin {prog : Program} {target_pc : BitVec 64}
    (addr : BitVec 64) (words : List (BitVec 32))
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w : BitVec 32} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (i : Nat) (next_pc : BitVec 64) (halign : MemWidth.isAligned .W32 ea = true)
    (rt' : Reg := .gpr 8#5)
    (hw : prog.hasCode addr words := by with_reducible assumption)
    (hget : words[i]? = some w := by rfl)
    (hdec : decode w = some (.ldarStlr .W32 true rn rt) := by rfl)
    (hrt : rt = rt' := by decide) (hrn : rn ≠ .sp := by decide)
    (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (haddr : s.readReg64 rn = ea := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hload : SepLoad32 ea P v := by wp_sep_access_fast)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt' (v.zeroExtend 64)).setPC next_pc) P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hrt hpc_next
  have hsp : checkRegSPAligned s rn = true := by cases rn <;> simp_all [checkRegSPAligned]
  apply SepWP.weaken_pre_frame (P' := ⌜s.mem.read32 ea = v ∧ s.mem.canRead ea 4 = true⌝ ∗ P)
  · intro R hm; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hload.load hm, hload.readable hm⟩, hm⟩
  · apply SepWP.pure_elim; rintro ⟨hread, hcan⟩
    refine SepWP.step_pure (s' := (s.writeReg64 rt (v.zeroExtend 64)).setPC (addr + BitVec.ofNat 64 (4 * (i + 1))))
      hpc hrun (Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec) ?_ rfl hnext
    have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by
      cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
    have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
    rw [hs_eq]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg, State.advancePC,
      State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

theorem call_malloc {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    {lc blk req : Nat} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s)
    (hreq_lim : req ≤ lim.maxReq)
    (hlc_lim : lc + mallocngBlockCost req ≤ lim.maxPeakCost)
    (hblk_lim : blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp_call MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      let ret := sf.readReg64 .x0
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf → ret ≠ 0#64 → 16 ∣ ret.toNat → ret.toNat + req < 2 ^ 64 →
      SepWP P target_pc sf
        ((M.Heap γ (lc + mallocngBlockCost req) (blk + 1) sf ∗
          M.Block γ ret req ∗ memRegion ret req ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call MallocngStackBytes) ∗ F) post oom)
    (hpc : s.pc = addrs.mallocAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hreq_reg : req = (s.readReg64 .x0).toNat := by simp (config := { decide := true }) only [arm64_norm, *]; try omega)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame (M.malloc_ok γ) (x := (lc, blk, req, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simpa [Reg.x0] using hreq_reg, hreq_lim, hlc_lim, hblk_lim⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (sepConj_mono (vmHeapTransport M hvm) (Entails.refl _))
      (by simpa only [sepConj_assoc] using hm')
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hmsp, hnz, hal16, hnw⟩
    have herr_eq : muslErrnoAddr s = muslErrnoAddr sf := by
      simp [muslErrnoAddr, hmsp.2.2.2.1]
    rw [herr_eq, hsp_call, show Reg.gpr 0#5 = Reg.x0 from rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    exact SepWP.weaken_pre (by sep_frame)
      (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp (by simpa [Reg.x0] using hnz)
        (by simpa [Reg.x0] using hal16) (by simpa [Reg.x0] using hnw))

theorem call_realloc {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (M : HbMallocngIface P addrs lim) (γ : GhostName)
    {lc blk oldReq newReq : Nat} {oldPtr : BitVec 64} {bs : List (BitVec 8)} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s)
    (hp_nz : oldPtr ≠ 0#64)
    (hbs_len : bs.length = oldReq)
    (hreq_lim : newReq ≤ lim.maxReq)
    (hlc_lim : lc + mallocngBlockCost newReq ≤ lim.maxPeakCost)
    (hblk_lim : blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s0 ∗ M.Block γ oldPtr oldReq ∗ (oldPtr ↦ₛ bs) ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp_call MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      let ret := sf.readReg64 .x0
      let kept := bs.take newReq
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf → ret ≠ 0#64 → 16 ∣ ret.toNat → ret.toNat + newReq < 2 ^ 64 →
      SepWP P target_pc sf
        ((M.Heap γ ((lc - mallocngBlockCost oldReq) + mallocngBlockCost newReq) blk sf ∗
          M.Block γ ret newReq ∗ (ret ↦ₛ kept) ∗
          memRegion (ret + BitVec.ofNat 64 kept.length) (newReq - kept.length) ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call MallocngStackBytes) ∗ F) post oom)
    (hpc : s.pc = addrs.reallocAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = oldPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hreq_reg : newReq = (s.readReg64 .x1).toNat := by simp (config := { decide := true }) only [arm64_norm, *]; try omega)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame (M.realloc_ok γ)
    (x := (lc, blk, some (oldReq, bs), newReq, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    have hx0' : s.readReg64 (.gpr 0#5) = oldPtr := hx0
    dsimp only; simp only [hx0', sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simpa [Reg.x1] using hreq_reg, hreq_lim, hlc_lim, hblk_lim⟩, ?_⟩
    rw [sepConj_left_comm (M.Heap γ lc blk s) ⌜oldPtr ≠ 0#64 ∧ bs.length = oldReq⌝,
      satisfies_pure_sepConj]
    refine ⟨⟨hp_nz, hbs_len⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (sepConj_mono (vmHeapTransport M.toMallocngCoreIface hvm) (Entails.refl _))
      (by simpa only [sepConj_assoc] using hm')
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hmsp, hnz, hal16, hnw⟩
    have herr_eq : muslErrnoAddr s = muslErrnoAddr sf := by
      simp [muslErrnoAddr, hmsp.2.2.2.1]
    rw [herr_eq, hsp_call, show Reg.gpr 0#5 = Reg.x0 from rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    exact SepWP.weaken_pre (by sep_frame)
      (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp (by simpa [Reg.x0] using hnz)
        (by simpa [Reg.x0] using hal16) (by simpa [Reg.x0] using hnw))

/-! ## `HbStdinInv` and `OnceLock<Stdin>::initialize` -/

abbrev hbStdinInitStackBytes : Nat := 192 + MallocngStackBytes

/-- Separation-logic invariant for `STDIN` (`C.stdinGlobalAddr`, 52 bytes `[g .. g + 0x34)`):
    when `init = false`, `[g + 0x30] = 3#32` (`Once` uninitialized) and `[g .. g + 0x30)` is zeroed;
    when `init = true`, an unlocked `Mutex<BufReader<StdinRaw>>` with `[g + 0x30] = 0#32` and one
    live 8192-byte `mallocng` buffer `M.Block γ bufPtr 8192`. -/
def HbStdinInv {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (init : Bool) : SepProp :=
  let g := C.stdinGlobalAddr
  if init then
    ∃∗ bufPtr : BitVec 64,
      ⌜bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 8192 < 2 ^ 64⌝ ∗
      (g ↦₃₂ 0#32) ∗
      memRegion (g + 0x04#64) 4 ∗
      ((g + 0x08#64) ↦₆₄ bufPtr) ∗
      ((g + 0x10#64) ↦₆₄ 8192#64) ∗
      ((g + 0x18#64) ↦₆₄ 0#64) ∗
      ((g + 0x20#64) ↦₆₄ 0#64) ∗
      ((g + 0x28#64) ↦₈ 0#8) ∗
      memRegion (g + 0x29#64) 7 ∗
      ((g + 0x30#64) ↦₃₂ 0#32) ∗
      M.Block γ bufPtr 8192 ∗
      memRegion bufPtr 8192
  else
    ((g + 0x30#64) ↦₃₂ 3#32) ∗
    (g ↦ₛ List.replicate 48 0#8)

theorem HbStdinInv_init {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) :
    ((C.stdinGlobalAddr + 0x30#64) ↦₃₂ 3#32) ∗
      (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ⊢
      HbStdinInv C M γ false :=
  Entails.refl _

def hbStdinCost (init : Bool) : Nat :=
  if init then mallocngBlockCost 8192 else 0

def hbStdinBlocks (init : Bool) : Nat :=
  if init then 1 else 0

theorem HbCliLayout.Valid.stdinOnceAligned {C : HbCliLayout} (hV : C.Valid) :
    MemWidth.isAligned .W32 (C.stdinGlobalAddr + 0x30#64) = true := by
  have hal := hV.stdinGlobal_align
  have hnw := hV.stdinGlobal_noWrap
  simp only [MemWidth.isAligned]
  have htn : (C.stdinGlobalAddr + 0x30#64).toNat = C.stdinGlobalAddr.toNat + 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : (C.stdinGlobalAddr + 0x30#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, htn, BitVec.toNat_ofNat]
    change (C.stdinGlobalAddr.toNat + 48) &&& 3 = 0
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; omega
  simp [h0]

private theorem stdinGlobal_zero48_split (g : BitVec 64) :
    (g ↦ₛ List.replicate 48 0#8) =
      (g ↦₃₂ 0#32) ∗ ((g + 0x04#64) ↦₈ 0#8) ∗ ((g + 0x05#64) ↦ₛ List.replicate 3 0#8) ∗
      ((g + 0x08#64) ↦₆₄ 0#64) ∗ ((g + 0x10#64) ↦₆₄ 0#64) ∗
      ((g + 0x18#64) ↦₆₄ 0#64) ∗ ((g + 0x20#64) ↦₆₄ 0#64) ∗
      ((g + 0x28#64) ↦₈ 0#8) ∗ ((g + 0x29#64) ↦ₛ List.replicate 7 0#8) := by
  have hbs : List.replicate 48 0#8 =
      unpack32 0#32 ++ ([0#8] ++ (List.replicate 3 0#8 ++ (unpack64 0#64 ++ (unpack64 0#64 ++
        (unpack64 0#64 ++ (unpack64 0#64 ++ ([0#8] ++ List.replicate 7 0#8))))))) := by decide
  rw [hbs]
  simp only [pointsToBytes_append, pointsToBytes_singleton,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    unpack32_length, unpack64_length, List.length_replicate, List.length_cons, List.length_nil]
  simp (config := { decide := true }) only [BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd]

private theorem stdinGlobal_zero48_entails (g : BitVec 64) :
    (g ↦ₛ List.replicate 48 0#8) ⊢
      (g ↦₃₂ 0#32) ∗ ((g + 0x04#64) ↦₈ 0#8) ∗ memRegion (g + 0x05#64) 3 ∗
      ((g + 0x08#64) ↦₆₄ 0#64) ∗ ((g + 0x10#64) ↦₆₄ 0#64) ∗
      ((g + 0x18#64) ↦₆₄ 0#64) ∗ ((g + 0x20#64) ↦₆₄ 0#64) ∗
      ((g + 0x28#64) ↦₈ 0#8) ∗ memRegion (g + 0x29#64) 7 := by
  rw [stdinGlobal_zero48_split g]
  have h3 : ((g + 0x05#64) ↦ₛ List.replicate 3 0#8) ⊢ memRegion (g + 0x05#64) 3 :=
    pointsToBytes_entails_memRegion (g + 0x05#64) (List.replicate 3 0#8)
  have h7 : ((g + 0x29#64) ↦ₛ List.replicate 7 0#8) ⊢ memRegion (g + 0x29#64) 7 :=
    pointsToBytes_entails_memRegion (g + 0x29#64) (List.replicate 7 0#8)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono h3
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) h7)))))))

private theorem pointsTo8_memRegion3_entails (g : BitVec 64) (b : BitVec 8) :
    ((g + 0x04#64) ↦₈ b) ∗ memRegion (g + 0x05#64) 3 ⊢ memRegion (g + 0x04#64) 4 := by
  have heq : g + 0x04#64 + BitVec.ofNat 64 1 = g + 0x05#64 := by bv_lin
  rw [show (4 : Nat) = 1 + 3 from rfl, memRegion_split (g + 0x04#64) 1 3 (by decide), heq,
    ← pointsToBytes_singleton]
  exact sepConj_mono (pointsToBytes_entails_memRegion (g + 0x04#64) [b]) (Entails.refl _)

private theorem pointsTo8_combine32_sub (sp o0 o1 o2 o3 : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R =
      ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3
  simpa only [sepConj_assoc,
    show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin,
    show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin,
    show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin]
    using congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)

private theorem pointsTo32_split8_sub (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R =
      ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗
      ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [pointsTo8_combine32_sub sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3,
    show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by bv_bits]

private theorem stackAt_split_stdin (sp : BitVec 64) (a b : Nat) (h : a + b ≤ 2 ^ 64 := by decide) :
    stackAt sp (a + b) = stackAt (sp - BitVec.ofNat 64 a) b ∗ stackAt sp a := by
  rw [stackAt_split_bottom sp a b h]; unfold stackAt; rw [BitVec.sub_sub, BitVec.ofNat_add]

private theorem hbStdinInitClosure_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc dataPtr slotPtr : BitVec 64}
    (hc : HbStdinAndVecCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {lc blk : Nat} {e0 : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s.pc = C.stdinInitClosureAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = dataPtr)
    (hg_nz : C.stdinGlobalAddr ≠ 0#64)
    (hreq_lim : 8192 ≤ lim.maxReq)
    (hlc_lim : lc + mallocngBlockCost 8192 ≤ lim.maxPeakCost)
    (hblk_lim : blk + 1 ≤ lim.maxPeakBlocks)
    (hnext : ∀ (sf : State) (bufPtr : BitVec 64) (e1 : BitVec 32),
      let g := C.stdinGlobalAddr
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.fs = s.fs → sf.trace = s.trace → sf.sigActions = s.sigActions → sf.tpidrEl0 = s.tpidrEl0 →
      bufPtr ≠ 0#64 → 16 ∣ bufPtr.toNat → bufPtr.toNat + 8192 < 2 ^ 64 →
      SepWP P target_pc sf
        ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ 0#64) ∗
          (g ↦₃₂ 0#32) ∗ memRegion (g + 0x04#64) 4 ∗
          ((g + 0x08#64) ↦₆₄ bufPtr) ∗ ((g + 0x10#64) ↦₆₄ 8192#64) ∗
          ((g + 0x18#64) ↦₆₄ 0#64) ∗ ((g + 0x20#64) ↦₆₄ 0#64) ∗
          ((g + 0x28#64) ↦₈ 0#8) ∗ memRegion (g + 0x29#64) 7 ∗
          M.Heap γ (lc + mallocngBlockCost 8192) (blk + 1) sf ∗
          M.Block γ bufPtr 8192 ∗ memRegion bufPtr 8192 ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp (MallocngStackBytes + 32) ∗ F) post) :
    SepWP P target_pc s
      ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ C.stdinGlobalAddr) ∗
        (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ∗
        M.Heap γ lc blk s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗
        stackAt s.sp (MallocngStackBytes + 32) ∗ F) post := by
  refine sepWP_mono_atom (stdinGlobal_zero48_entails C.stdinGlobalAddr) (h := ?_)
  rw [show MallocngStackBytes + 32 = MallocngStackBytes + 8 * 4 from rfl,
    stackAt_split_cells s.sp MallocngStackBytes 4 (by decide)]; unpack_cells 4
  refine SepWP.seq_nonVm (mid := C.mallocng.mallocAddr) hext hsvc ?_
  have hc_nv1 := hc.withSvc nonVmSvc
  unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
  wp_steps; norm_jmp; wp_steps; wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine call_malloc M γ (req := 8192) (e0 := e0) (sp_call := s.sp - 32#64)
    (ret_pc := C.stdinInitClosureAddr + 0x2c#64)
    hvm1 hreq_lim hlc_lim hblk_lim (F := ?_) (by sep_frame)
    (fun s2 e1 hpc2 hrun2 hsp2 hcs2 hmsp2 hnz2 hal16_2 hnw2 => ?_)
    (hsp_align := by
      simp only [State.spAligned, wp_norm, arm64_norm]
      simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
  have hnz2' : s2.readReg64 (.gpr 0#5) ≠ 0#64 := hnz2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = C.stdinGlobalAddr := by
    rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hsp2_eq : s2.sp = s.sp - 32#64 := by rw [hsp2]; exact wp_a
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 32#64 hsp_align
  refine SepWP.seq_nonVm (mid := ret_pc) hext hsvc ?_
  have hc_nv2 := hc.withSvc nonVmSvc
  unpack_hb_stdin_code hbStdinAndVecChunks hc_nv2
  wp_steps; wp_steps
  apply SepWP.done
    (by unpack_cs hcs2; simp [wp_norm, arm64_norm, *]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun2])
  intro hvm2
  refine SepWP.weaken_pre_frame ?_
    (hnext _ (s2.readReg64 .x0) e1
      (by unpack_cs hcs2; simp [wp_norm, arm64_norm, *]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun2])
      (by simp [wp_norm, arm64_norm])
      (by unpack_cs hcs2; close_cs)
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.2.2.1]; simp [wp_norm, arm64_norm])
      hnz2 hal16_2 hnw2)
  intro _ hm
  replace hm := mono_head_sat (vmHeapTransport M (γ := γ) (lc := lc + mallocngBlockCost 8192) (blk := blk + 1) hvm2) hm
  replace hm := mono_head_sat (pointsTo8_memRegion3_entails C.stdinGlobalAddr 0#8) hm
  simp only [muslErrnoAddr, wp_norm, arm64_norm] at hm ⊢
  rw [show MallocngStackBytes + 32 = MallocngStackBytes + 8 * 4 from rfl,
    stackAt_split_cells s.sp MallocngStackBytes 4 (by decide)]
  repack_cells

private theorem combine_cell_byte4_entails (sp o8 o4 o3 o2 o1 : BitVec 64)
    (lo : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl)
    (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) :
    ((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
      ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3) ⊢
      ((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) := by
  have h8 := pointsTo8_combine32_sub sp o4 o3 o2 o1 b0 b1 b2 b3 emp h1 h2 h3
  have h64 := pointsTo32_combine64_sub sp o8 o4 lo (b3 ++ b2 ++ b1 ++ b0) emp h4
  have heq : (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
      ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) =
      ((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) := by
    simpa only [sepConj_assoc, sepConj_emp] using (congrArg (((sp - o8) ↦₃₂ lo) ∗ ·) h8).trans h64
  exact heq ▸ Entails.refl _

private theorem hbStdinOnceCall_incomplete_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 onceAddr dataPtr vtableAddr shimAddr closureAddr : BitVec 64}
    {haveLse : BitVec 8} {s : State} {Pre Post : State → SepProp} {F : SepProp}
    {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (honce : HbOnceCallCode P C)
    (hcas : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hpc : s.pc = C.std.onceCallAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = onceAddr) (hx1 : s.readReg64 .x1 = 1#64)
    (hx2 : s.readReg64 .x2 = dataPtr) (hx3 : s.readReg64 .x3 = vtableAddr)
    (halign : MemWidth.isAligned .W32 onceAddr = true)
    (hPre_vm : ∀ s1 s2, VmFieldsPreserved s1 s2 → Pre s1 ⊢ Pre s2)
    (hPost_vm : ∀ s1 s2, VmFieldsPreserved s1 s2 → Post s1 ⊢ Post s2)
    (hclosure : ∀ sc : State, ∀ G : SepProp,
      sc.pc = closureAddr → sc.status = .Running → sc.sp = sp0 - 0x60#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = C.std.onceCallAddr + 0x11c#64 → sc.readReg64 .x0 = dataPtr →
      sc.fs = s.fs → sc.trace = s.trace → sc.sigActions = s.sigActions → sc.tpidrEl0 = s.tpidrEl0 →
      (∀ sr : State, sr.pc = C.std.onceCallAddr + 0x11c#64 → sr.status = .Running → sr.sp = sc.sp →
        CalleeSavedPreserved sc sr →
        sr.fs = sc.fs → sr.trace = sc.trace → sr.sigActions = sc.sigActions → sr.tpidrEl0 = sc.tpidrEl0 →
        SepWP P target_pc sr ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Post sr ∗ G) post) →
      SepWP P target_pc sc ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Pre sc ∗ G) post)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.fs = s.fs → sf.trace = s.trace → sf.sigActions = s.sigActions → sf.tpidrEl0 = s.tpidrEl0 →
      SepWP P target_pc sf ((onceAddr ↦₃₂ 0#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo vtableAddr shimAddr closureAddr ∗ stackAt sp0 96 ∗ Post sf ∗ F) post) :
    SepWP P target_pc s ((onceAddr ↦₃₂ 3#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo vtableAddr shimAddr closureAddr ∗ stackAt sp0 96 ∗ Pre s ∗ F) post := by
  subst hsp
  unfold StdVtableRo
  rw [stackAt_eq_cells s.sp 12]; unpack_cells 12
  rw [pointsTo64_split32_sub s.sp 88#64 84#64, pointsTo32_split8_sub s.sp 84#64 83#64 82#64 81#64]
  refine SepWP.seq_nonVm (mid := C.std.cas4AcqAddr) hext hsvc ?_
  have honce_nv1 := hbStdinCodeChunks_withSvc (svc := nonVmSvc) honce
  unpack_hb_stdin_code hbOnceCallPostChunks honce_nv1
  wp_steps
  refine step_ldar32_words_stdin C.std.onceCallAddr _ 7 (C.std.onceCallAddr + 0x20#64) halign
    (rt' := .gpr 22#5) (hnext := ?_)
  wp_steps; wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine call_stdCas4 hcas (haveLse := haveLse) (ptr := onceAddr) (v0 := 3#32) (exp := 3#32) (new := 1#32)
    (ret_pc := C.std.onceCallAddr + 0x64#64) (F := ?_) (by sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_)
    (hsp_align := by
      simp only [State.spAligned, wp_norm, arm64_norm]
      simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x60#64 hsp_align)
    (halign := halign)
  simp only [beq_self_eq_true, ↓reduceIte]
  have ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩ :
      s1.readReg64 (.gpr 19#5) = onceAddr ∧ s1.readReg64 (.gpr 20#5) = dataPtr ∧
      s1.readReg64 (.gpr 21#5) = vtableAddr ∧
      BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 ∧
      BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 :=
    ⟨by rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm],
     by rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm],
     by rw [← Reg.x21, hcs1.readReg64_x21]; simp [wp_norm, arm64_norm],
     by have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this,
     by have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this⟩
  have hsp1_eq : s1.sp = s.sp - 0x60#64 := by rw [hsp1]; exact wp_a
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  refine SepWP.seq_nonVm (mid := closureAddr) hext hsvc ?_
  have honce_nv2 := hbStdinCodeChunks_withSvc (svc := nonVmSvc) honce
  unpack_hb_stdin_code hbOnceCallPostChunks honce_nv2
  wp_steps; wp_steps
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
  intro hvm2
  have hvm_sc : VmFieldsPreserved s _ := (hvm1.trans (vmOfStdState hstd1)).trans hvm2
  refine sepWP_mono_atom (hPre_vm s _ hvm_sc) (h := ?_)
  refine SepWP.weaken_pre (P' := (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Pre _ ∗ ?G) (by sep_frame) ?_
  refine hclosure _ ?G wp_a (by simp [wp_norm, arm64_norm, hrun1])
    (by simp [wp_norm, arm64_norm, hsp1_eq])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
    wp_a wp_a
    (by simp only [wp_norm, arm64_norm]; rw [hstd1.1]; simp [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rw [hstd1.2.1]; simp [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rw [hstd1.2.2.2.1]; simp [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rw [hstd1.2.2.1]; simp [wp_norm, arm64_norm])
    fun s2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 hsig2 htid2 => ?_
  have hx19_2 : s2.readReg64 (.gpr 19#5) = onceAddr := by
    rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
  have hsp2_eq : s2.sp = s.sp - 0x60#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  refine SepWP.seq_nonVm (mid := C.std.swp4RelAddr) hext hsvc ?_
  have honce_nv3 := hbStdinCodeChunks_withSvc (svc := nonVmSvc) honce
  unpack_hb_stdin_code hbOnceCallPostChunks honce_nv3
  wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
  intro hvm3
  refine call_stdSwp4 hswp (haveLse := haveLse) (ptr := onceAddr) (v0 := 1#32) (new := 0#32)
    (ret_pc := C.std.onceCallAddr + 0x128#64) (F := ?_) (by sep_frame)
    (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_)
    (hsp_align := by
      simp only [State.spAligned, wp_norm, arm64_norm, hsp2_eq]
      simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x60#64 hsp_align)
    (halign := halign)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_3
  have hsp3_eq : s3.sp = s.sp - 0x60#64 := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by
    simp only [State.spAligned, hsp3_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  refine SepWP.seq_nonVm (mid := ret_pc) hext hsvc ?_
  have honce_nv4 := hbStdinCodeChunks_withSvc (svc := nonVmSvc) honce
  unpack_hb_stdin_code hbOnceCallPostChunks honce_nv4
  wp_steps; wp_steps
  apply SepWP.done
    (by unpack_cs hcs1; unpack_cs hcs2; unpack_cs hcs3; simp [wp_norm, arm64_norm, *]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun3])
  intro hvm4
  have hvm_s2_sf : VmFieldsPreserved s2 _ := (hvm3.trans (vmOfStdState hstd3)).trans hvm4
  refine SepWP.weaken_pre_frame ?_
    (hnext _
      (by unpack_cs hcs1; unpack_cs hcs2; unpack_cs hcs3; simp [wp_norm, arm64_norm, *]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun3])
      (by simp [wp_norm, arm64_norm])
      (by unpack_cs hcs1; unpack_cs hcs2; unpack_cs hcs3; close_cs)
      (by simp only [wp_norm, arm64_norm]; rw [hstd3.1]; simp only [wp_norm, arm64_norm]; rw [hfs2]; simp only [wp_norm, arm64_norm]; rw [hstd1.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hstd3.2.1]; simp only [wp_norm, arm64_norm]; rw [htr2]; simp only [wp_norm, arm64_norm]; rw [hstd1.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hstd3.2.2.2.1]; simp only [wp_norm, arm64_norm]; rw [hsig2]; simp only [wp_norm, arm64_norm]; rw [hstd1.2.2.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hstd3.2.2.1]; simp only [wp_norm, arm64_norm]; rw [htid2]; simp only [wp_norm, arm64_norm]; rw [hstd1.2.2.1]; simp [wp_norm, arm64_norm]))
  intro _ hm
  replace hm := mono_head_sat (hPost_vm s2 _ hvm_s2_sf) hm
  replace hm := mono_head_sat (combine_cell_byte4_entails s.sp 88#64 84#64 83#64 82#64 81#64 _ _ _ _ _) hm
  unfold StdVtableRo
  rw [stackAt_eq_cells s.sp 12]
  repack_cells

theorem entails_mono_atom {A A' P Q Rest : SepProp} (himp : A ⊢ A')
    (hP : P = A ∗ Rest := by sep_frame) (hQ : A' ∗ Rest ⊢ Q := by sep_entail) :
    P ⊢ Q :=
  Entails.trans (hP ▸ sepConj_mono himp (Entails.refl Rest)) hQ

/-- Specification for `OnceLock<Stdin>::initialize` (`C.stdinOnceLockInitAddr`), transitioning
    `HbStdinInv C M γ init` to `HbStdinInv C M γ true`. -/
def hbStdinOnceLockInitSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Bool × Nat × Nat × BitVec 8 × BitVec 32) where
  pre := fun (init, lc, blk, haveLse, e0) s0 =>
    ⌜C.stdinGlobalAddr ≠ 0#64 ∧
      (init = false →
        8192 ≤ lim.maxReq ∧
        lc + mallocngBlockCost 8192 ≤ lim.maxPeakCost ∧
        blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    (HbStdinInv C M γ init ∗
     (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
     StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
     M.Heap γ lc blk s0 ∗
     (muslErrnoAddr s0 ↦₃₂ e0) ∗
     stackAt s0.sp hbStdinInitStackBytes)
  post := fun (init, lc, blk, haveLse, _) s0 sf =>
    let lc' := lc + if init then 0 else mallocngBlockCost 8192
    let blk' := blk + if init then 0 else 1
    ⌜MallocngStatePreserved s0 sf⌝ ∗
    (∃∗ e1 : BitVec 32,
      HbStdinInv C M γ true ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      M.Heap γ lc' blk' sf ∗
      (muslErrnoAddr sf ↦₃₂ e1) ∗
      stackAt s0.sp hbStdinInitStackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbStdinOnceLockInit_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hV : C.Valid) (hc : HbStdinAndVecCode P C) (honce : HbOnceCallCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdinOnceLockInitAddr (hbStdinOnceLockInitSpec C M γ) := by
  apply subroutine_ok_of_sepWP_frozen
  rintro ⟨init, lc, blk, haveLse, e0⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbStdinOnceLockInitSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hg_nz, hlim⟩, hmem⟩
  refine ⟨HbStdinInv C M γ init ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp hbStdinInitStackBytes,
    by sep_frame, ?_⟩
  cases init
  ·
    obtain ⟨hreq_lim, hlc_lim, hblk_lim⟩ := hlim rfl
    conv =>
      arg 4
      simp only [HbStdinInv, Bool.false_eq_true, ↓reduceIte]
      rw [show hbStdinInitStackBytes = (96 + ((MallocngStackBytes + 32) + 16)) + 8 * 6 from by
            unfold hbStdinInitStackBytes; omega,
          stackAt_split_cells s0.sp _ 6 (by decide)]
    unpack_cells 6
    conv =>
      arg 4
      rw [show s0.sp - BitVec.ofNat 64 (8 * 6) = s0.sp - 48#64 from rfl,
          stackAt_split_stdin (s0.sp - 48#64) 96 ((MallocngStackBytes + 32) + 16),
          stackAt_split_stdin (s0.sp - 48#64 - 96#64) (MallocngStackBytes + 32) 16]
    refine SepWP.seq_nonVm (mid := C.std.onceCallAddr) hext hsvc ?_
    have hc_nv1 := hc.withSvc nonVmSvc
    unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
    wp_steps
    refine step_ldar32_words_stdin (C.stdinOnceLockInitAddr + 0x08#64) hbStdinOnceLockEntryWords 0
      (C.stdinOnceLockInitAddr + 0x0c#64) hV.stdinOnceAligned (hnext := ?_)
    wp_steps; wp_steps; norm_jmp; wp_steps; wp_steps; wp_steps; norm_jmp; wp_steps; norm_jmp
    conv => repeat rw [bv64_add_sub_cancel]
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm1
    let Pre : State → SepProp := fun st =>
      M.Heap γ lc blk st ∗
      (((s0.sp - 32#64) ↦₆₄ (s0.sp - 48#64)) ∗ ((s0.sp - 48#64) ↦₆₄ C.stdinGlobalAddr) ∗
       (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ∗
       (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt (s0.sp - 48#64 - 0x60#64) (MallocngStackBytes + 32))
    let Post : State → SepProp := fun st =>
      ∃∗ bufPtr : BitVec 64, ∃∗ e1 : BitVec 32,
        M.Heap γ (lc + mallocngBlockCost 8192) (blk + 1) st ∗
        (⌜bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 8192 < 2 ^ 64⌝ ∗
         ((s0.sp - 32#64) ↦₆₄ (s0.sp - 48#64)) ∗ ((s0.sp - 48#64) ↦₆₄ 0#64) ∗
         (C.stdinGlobalAddr ↦₃₂ 0#32) ∗ memRegion (C.stdinGlobalAddr + 0x04#64) 4 ∗
         ((C.stdinGlobalAddr + 0x08#64) ↦₆₄ bufPtr) ∗ ((C.stdinGlobalAddr + 0x10#64) ↦₆₄ 8192#64) ∗
         ((C.stdinGlobalAddr + 0x18#64) ↦₆₄ 0#64) ∗ ((C.stdinGlobalAddr + 0x20#64) ↦₆₄ 0#64) ∗
         ((C.stdinGlobalAddr + 0x28#64) ↦₈ 0#8) ∗ memRegion (C.stdinGlobalAddr + 0x29#64) 7 ∗
         M.Block γ bufPtr 8192 ∗ memRegion bufPtr 8192 ∗
         (muslErrnoAddr s0 ↦₃₂ e1) ∗ stackAt (s0.sp - 48#64 - 0x60#64) (MallocngStackBytes + 32))
    refine sepWP_mono_atom (vmHeapTransport M hvm1) (h := ?_)
    refine SepWP.weaken_pre (P' := ((C.stdinGlobalAddr + 0x30#64) ↦₃₂ 3#32) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      stackAt (s0.sp - 48#64) 96 ∗ Pre _ ∗ ?F_once) (by dsimp +zetaDelta only [Pre]; sep_frame) ?_
    refine hbStdinOnceCall_incomplete_wp
      (ret_pc := C.stdinOnceLockInitAddr + 68#64) (dataPtr := s0.sp - 32#64) (Pre := Pre) (Post := Post)
      hsvc hext honce hatom.cas4Acq_ok hatom.swp4Rel_ok
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simp only [State.spAligned, wp_norm, arm64_norm]
          simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 48#64 hsp_align)
      wp_a wp_a wp_a wp_a wp_a hV.stdinOnceAligned
      (fun _ _ hvm => sepConj_mono (vmHeapTransport M hvm) (Entails.refl _))
      (fun _ _ hvm => Entails.sepExists_mono fun _ =>
        Entails.sepExists_mono fun _ => sepConj_mono (vmHeapTransport M hvm) (Entails.refl _))
      (fun sc G hpc_c hrun_c hsp_c hal_c hlr_c hx0_c hfs_c htr_c hsig_c htid_c hret => ?_)
      (fun s2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 hsig2 htid2 => ?_)
    ·
      have herr_sc : muslErrnoAddr s0 = muslErrnoAddr sc := by
        simp only [muslErrnoAddr, htid_c]; simp [wp_norm, arm64_norm]
      conv => arg 4; dsimp +zetaDelta only [Pre]; rw [herr_sc, ← hsp_c]
      refine SepWP.weaken_pre (P' := ((s0.sp - 32#64) ↦₆₄ (s0.sp - 48#64)) ∗
        ((s0.sp - 48#64) ↦₆₄ C.stdinGlobalAddr) ∗
        (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ∗ M.Heap γ lc blk sc ∗
        (muslErrnoAddr sc ↦₃₂ e0) ∗ stackAt sc.sp (MallocngStackBytes + 32) ∗
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ G)) (by sep_frame) ?_
      refine hbStdinInitClosure_wp hc M γ hsvc hext hpc_c hrun_c hal_c hlr_c hx0_c hg_nz
        hreq_lim hlc_lim hblk_lim
        fun sr bufPtr e1 hpc_r hrun_r hsp_r hcs_r hfs_r htr_r hsig_r htid_r hnz_r hal16_r hnw_r => ?_
      have herr_sr : muslErrnoAddr sr = muslErrnoAddr s0 := by
        rw [herr_sc]; simp [muslErrnoAddr, htid_r]
      conv => arg 4; rw [herr_sr, hsp_c]
      refine SepWP.weaken_pre ?_ (hret sr hpc_r hrun_r hsp_r hcs_r hfs_r htr_r hsig_r htid_r)
      dsimp +zetaDelta only [Post]
      conv => rhs; rw [← sepConj_assoc, sepConj_comm (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse), sepConj_assoc]
      refine Entails.sepExists_intro_frame bufPtr ?_
      refine Entails.sepExists_intro_frame e1 ?_
      conv => rhs; rw [← sepConj_assoc (M.Heap _ _ _ _), sepConj_comm (M.Heap _ _ _ _),
        sepConj_assoc, pure_sepConj_of_true ⟨hnz_r, hal16_r, hnw_r⟩]
      sep_entail
    ·
      conv =>
        arg 4
        dsimp +zetaDelta only [Post]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWP.exists_elim fun bufPtr => SepWP.exists_elim fun e1 => ?_
      conv => arg 4; simp only [sepConj_assoc, sepConj_pull_pure]
      refine SepWP.pure_elim fun hbuf_pure => ?_
      have hsp2_al : s2.spAligned = true := by
        simp only [State.spAligned, hsp2]; exact s0.spAligned_sub 48#64 hsp_align
      refine SepWP.of_nonVm hext hsvc ?_
      have hc_nv2 := hc.withSvc nonVmSvc
      unpack_hb_stdin_code hbStdinAndVecChunks hc_nv2
      wp_steps
      apply SepWP.done
        (by unpack_cs hcs2; simp [wp_norm, arm64_norm, *]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun2])
      intro hvm_end
      refine ⟨fun hkf hm => ?_,
        by simp [wp_norm, arm64_norm],
        by unpack_cs hcs2; close_cs⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨e1, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp only [wp_norm, arm64_norm]; rw [hfs2]; simp [wp_norm, arm64_norm],
               by simp only [wp_norm, arm64_norm]; rw [htr2]; simp [wp_norm, arm64_norm],
               by simp only [wp_norm, arm64_norm]; rw [hsig2]; simp [wp_norm, arm64_norm],
               by simp only [wp_norm, arm64_norm]; rw [htid2]; simp [wp_norm, arm64_norm], hkf⟩, ?_⟩
      replace hm := mono_head_sat (vmHeapTransport M hvm_end) hm
      have htid_s2 : s2.tpidrEl0 = s0.tpidrEl0 := by
        rw [htid2]; simp [wp_norm, arm64_norm]
      simp +zetaDelta only [HbStdinInv, Bool.false_eq_true, ↓reduceIte,
        muslErrnoAddr, htid_s2, wp_norm, arm64_norm] at hm ⊢
      refine ⟨bufPtr, hbuf_pure, ?_⟩
      rw [show hbStdinInitStackBytes = (96 + ((MallocngStackBytes + 32) + 16)) + 8 * 6 from by
            unfold hbStdinInitStackBytes; omega,
          stackAt_split_cells s0.sp _ 6 (by decide),
          stackAt_split_stdin (s0.sp - BitVec.ofNat 64 (8 * 6)) 96 ((MallocngStackBytes + 32) + 16),
          stackAt_split_stdin (s0.sp - BitVec.ofNat 64 (8 * 6) - 96#64) (MallocngStackBytes + 32) 16]
      repack_cells
  ·
    conv =>
      arg 4
      simp only [HbStdinInv, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun bufPtr => ?_
    conv => arg 4; simp only [sepConj_assoc]
    refine SepWP.pure_elim fun hbuf_pure => ?_
    refine SepWP.of_nonVm hext hsvc ?_
    have hc_nv := hc.withSvc nonVmSvc
    unpack_hb_stdin_code hbStdinAndVecChunks hc_nv
    wp_steps
    refine step_ldar32_words_stdin (C.stdinOnceLockInitAddr + 0x08#64) hbStdinOnceLockEntryWords 0
      (C.stdinOnceLockInitAddr + 0x0c#64) hV.stdinOnceAligned (hnext := ?_)
    wp_steps
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm_end
    refine ⟨fun hkf hm => ?_, by simp [wp_norm, arm64_norm], by close_cs⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
             by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hkf⟩, ?_⟩
    replace hm := mono_head_sat (vmHeapTransport M hvm_end) hm
    simp only [HbStdinInv, ↓reduceIte, Nat.add_zero, muslErrnoAddr, wp_norm, arm64_norm] at hm ⊢
    exact ⟨e0, bufPtr, hbuf_pure, by sep_entail⟩

theorem hbStdinOnceLockInit_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (hV : C.Valid) (hc : HbStdinAndVecCode P C) (honce : HbOnceCallCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {init : Bool} {lc blk : Nat} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s := by exact ⟨rfl, rfl, rfl, fun _ => rfl⟩)
    (hg_nz : C.stdinGlobalAddr ≠ 0#64)
    (hlim : init = false →
      8192 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 8192 ≤ lim.maxPeakCost ∧
      blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (HbStdinInv C M γ init ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
        M.Heap γ lc blk s0 ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗
        stackAt sp_call hbStdinInitStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      let lc' := lc + if init then 0 else mallocngBlockCost 8192
      let blk' := blk + if init then 0 else 1
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      SepWP P target_pc sf
        ((HbStdinInv C M γ true ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
          M.Heap γ lc' blk' sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt sp_call hbStdinInitStackBytes) ∗ F) post oom)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hpc : s.pc = C.stdinOnceLockInitAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbStdinOnceLockInit_ok hV hc honce hatom M γ hsvc hext)
    (x := (init, lc, blk, haveLse, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only [hbStdinOnceLockInitSpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hg_nz, hlim⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (entails_mono_atom (vmHeapTransport M hvm)) hm'
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [hbStdinOnceLockInitSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; intro hmsp
    conv => arg 4; rw [hsp_call]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    exact SepWP.weaken_pre (by sep_frame) (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp)

end CaseStudies.Hashbrown.Proofs.StdCli
