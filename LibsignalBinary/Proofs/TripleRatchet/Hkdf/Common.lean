/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.HkdfCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.AesCbc.LibsignalAesCbcProofDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.WPFrozen

/-!
# Shared HKDF Symbolic-Execution and Framing Infrastructure

Defines `RunsTo`, `Frame`, `HmacSt`, `IsBlock`, and the `FinPre`/`FinPost`
cut invariants shared across the `finalize_fixed`, `extract`, and `expand_multi_info` proofs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `CalleeSaved`, `VCalleeSaved`, `TraceEq`, and `RunsTo` -/

/-- The callee-saved GPRs `x19`–`x30` and `sp` are preserved between `s` and `s'`. -/
def CalleeSaved (s s' : State) : Prop :=
  s'.sp = s.sp ∧
    ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .lr],
      s'.readReg64 r = s.readReg64 r

theorem CalleeSaved.sp_eq {s s' : State} (h : CalleeSaved s s') : s'.sp = s.sp := h.1
theorem CalleeSaved.x19 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x19 = s.readReg64 .x19 := h.2 .x19 (by simp)
theorem CalleeSaved.x20 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x20 = s.readReg64 .x20 := h.2 .x20 (by simp)
theorem CalleeSaved.x21 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x21 = s.readReg64 .x21 := h.2 .x21 (by simp)
theorem CalleeSaved.x22 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x22 = s.readReg64 .x22 := h.2 .x22 (by simp)
theorem CalleeSaved.x23 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x23 = s.readReg64 .x23 := h.2 .x23 (by simp)
theorem CalleeSaved.x24 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x24 = s.readReg64 .x24 := h.2 .x24 (by simp)
theorem CalleeSaved.x25 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x25 = s.readReg64 .x25 := h.2 .x25 (by simp)
theorem CalleeSaved.x26 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x26 = s.readReg64 .x26 := h.2 .x26 (by simp)
theorem CalleeSaved.x27 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x27 = s.readReg64 .x27 := h.2 .x27 (by simp)
theorem CalleeSaved.x28 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x28 = s.readReg64 .x28 := h.2 .x28 (by simp)
theorem CalleeSaved.x29 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x29 = s.readReg64 .x29 := h.2 .x29 (by simp)
theorem CalleeSaved.lr  {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .lr  = s.readReg64 .lr  := h.2 .lr  (by simp)

def TraceEq (s₀ s : State) : Prop :=
  s.trace = s₀.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s₀

theorem TraceEq.refl (s : State) : TraceEq s s := ⟨rfl, rfl⟩
theorem TraceEq.trans {s₀ s₁ s₂ : State} (h2 : TraceEq s₁ s₂) (h1 : TraceEq s₀ s₁) :
    TraceEq s₀ s₂ := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
theorem TraceEq.advancePC_step {s₀ s : State} (h : TraceEq s₀ s) : TraceEq s₀ s.advancePC := h
theorem TraceEq.setMem_step {s₀ s : State} {m : Memory} (h : TraceEq s₀ s) : TraceEq s₀ (s.setMem m) := h
theorem TraceEq.setPC_step {s₀ s : State} {pc : BitVec 64} (h : TraceEq s₀ s) : TraceEq s₀ (s.setPC pc) := h
theorem TraceEq.setPState_step {s₀ s : State} {f : PState} (h : TraceEq s₀ s) : TraceEq s₀ (s.setPState f) := h
theorem TraceEq.writeReg64_step {s₀ s : State} {r : Reg} {val : BitVec 64} (h : TraceEq s₀ s) :
    TraceEq s₀ (s.writeReg64 r val) := h
theorem TraceEq.writeReg32_step {s₀ s : State} {r : Reg} {val : BitVec 32} (h : TraceEq s₀ s) :
    TraceEq s₀ (s.writeReg32 r val) := h
theorem TraceEq.writeVReg128_step {s₀ s : State} {k : BitVec 5} {val : BitVec 128}
    (hk : k.toNat < 8) (h : TraceEq s₀ s) :
    TraceEq s₀ (s.writeVReg128 k val) := by
  refine ⟨h.1, ?_⟩
  have h8 : (8#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h9 : (9#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h10 : (10#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h11 : (11#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h12 : (12#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h13 : (13#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h14 : (14#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  have h15 : (15#5 : BitVec 5) ≠ k := by intro heq; subst heq; revert hk; decide
  simpa [calleeSavedVRegs, VRegFile.calleeSaved, State.writeVReg128, VRegFile.write, VRegFile.read,
    h8, h9, h10, h11, h12, h13, h14, h15] using h.2

theorem CallingConventionPreserved_of_calleeSaved {s₀ sf : State} (h : CalleeSaved s₀ sf)
    (htr : TraceEq s₀ sf := by assumption) :
    CallingConventionPreserved s₀ sf := by
  rcases h with ⟨hsp_eq, hregs⟩
  refine ⟨hsp_eq,
    hregs .x19 (by simp), hregs .x20 (by simp), hregs .x21 (by simp),
    hregs .x22 (by simp), hregs .x23 (by simp), hregs .x24 (by simp),
    hregs .x25 (by simp), hregs .x26 (by simp), hregs .x27 (by simp),
    hregs .x28 (by simp), hregs .x29 (by simp), htr.2⟩

/-- Symbolic execution from `s` in `prog` reaches some `s'` via `Steps`, preserving `trace`
relative to `s₀`, preserving `CodeLoaded`, and establishing `P s'`. -/
def RunsToFrom (prog : Program) (s₀ s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ s', Steps prog s s' ∧ TraceEq s₀ s' ∧ P s' ∧ prog.CodeLoaded s'.mem

/-- Symbolic execution from `s` in `prog` reaches some `s'` via `Steps`, preserving `trace`
and `CodeLoaded`, and establishing `P s'`. -/
abbrev RunsTo (prog : Program) (s : State) (P : State → Prop) : Prop :=
  RunsToFrom prog s s P

namespace RunsTo

variable {prog : Program}

theorem refl {s₀ s : State} {P : State → Prop} (h : P s)
    (htr : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide))) :
    RunsToFrom prog s₀ s P :=
  fun hL => ⟨s, .refl s, htr, h, hL⟩

theorem mono {s : State} {P Q : State → Prop}
    (h : RunsTo prog s P) (himp : ∀ s', P s' → Q s') :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s', hst, htr, hP, hL'⟩ := h hL
  exact ⟨s', hst, htr, himp s' hP, hL'⟩

theorem trans {s : State} {P Q : State → Prop}
    (h1 : RunsTo prog s P)
    (h2 : ∀ s₁, P s₁ → RunsTo prog s₁ Q) :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hQ, hL2⟩ := h2 s₁ hP hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hQ, hL2⟩

@[simp, arm64_norm]
theorem lsProg_svc [LibsignalPlacement] {prog : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H] : prog.svc = Syscall.standard := by
  rw [hprog.eq_blockProgram]; rfl

/-- One ordinary instruction step (`prog.fetch s.pc = some inst`). -/
theorem step {s₀ s : State} {inst : Instr} {P : State → Prop}
    (hrun : s.status = .Running)
    (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToFrom prog s₀ (execInst inst s) P)
    (hsvc : prog.svc = Syscall.standard := by first | rfl | exact RunsTo.lsProg_svc) :
    RunsToFrom prog s₀ s P := by
  intro hL
  have hfm := Program.fetchMem_of_fetch hL hfetch
  have hstep : Step prog s (execInst inst s) :=
    Program.evalInst_eq_execInst inst s hsvc ▸ Step.exec hrun hfm
  have hL' : prog.CodeLoaded (execInst inst s).mem := hstep.codeLoaded hL
  obtain ⟨s', hst, htr, hP, hL''⟩ := h hL'
  exact ⟨s', .step hstep hst, htr, hP, hL''⟩

/-- One extern-hook step (`prog.externAt? s.pc = some f`). -/
theorem hook {s₀ s : State} {f : State → State} {P : State → Prop}
    (hrun : s.status = .Running)
    (hhook : prog.externAt? s.pc = some f)
    (hkeep : s.mem.KeepsFrozen (f s).mem)
    (hsym : (f s).symtab = s.symtab)
    (h : RunsToFrom prog s₀ (f s) P) :
    RunsToFrom prog s₀ s P := by
  intro hL
  have hstep : Step prog s (f s) := Step.extern hrun hhook hkeep hsym
  have hL' : prog.CodeLoaded (f s).mem := hL.of_keepsFrozen hkeep
  obtain ⟨s', hst, htr, hP, hL''⟩ := h hL'
  exact ⟨s', .step hstep hst, htr, hP, hL''⟩

/-- Convert `RunsTo` into `reaches_pc` (providing `KeepsFrozen`, `symtab`, and `trace`). -/
theorem to_reaches_pc {target : BitVec 64} {s0 : State} {P Q : State → Prop}
    {oom : State → Prop}
    (h : RunsTo prog s0 P)
    (hpost : ∀ sf, P sf → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      TraceEq s0 sf →
      sf.pc = target ∧ sf.status = .Running ∧ Q sf) :
    reaches_pc prog target s0 Q oom := by
  intro hL
  obtain ⟨sf, hsteps, htr, hP, _⟩ := h hL
  obtain ⟨hpc, hrun, hQ⟩ := hpost sf hP hsteps.keepsFrozen hsteps.symtab_eq htr
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hQ⟩⟩

end RunsTo

/-! ## Extern Hook Lookups and Step Lemmas -/

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_fetch (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (addr : BitVec 64) :
    (tripleRatchetProgAt b C ctl abs).fetch addr =
      (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fetch addr := rfl

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_fetch_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (addr : BitVec 64) :
    (trTrapProgAt b C abs).fetch addr =
      (libsignalSessionCode.rebase b (Rust.withPanics (trTrapExterns C abs))).fetch addr := rfl

theorem hookMemcpy_eq_memcpyHook :
    ProofLib.hookMemcpy = memcpyHook := rfl

theorem truncate8_truncate32 (x : BitVec 64) :
    (x.truncate 32).truncate 8 = x.truncate 8 := by bv_bits

theorem hookMemset_eq_memsetHook :
    ProofLib.hookMemset = memsetHook := by
  funext s
  dsimp only [ProofLib.hookMemset, memsetHook, ProofLib.retHook, returnToLinkRegister,
    State.setMem, State.setPC, State.readReg32, State.readReg64]
  simp only [truncate8_truncate32]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_272972_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).externAt? (b + bv% (ls_off% "memset")) = some memsetHook := by
  rw [show (bv% (ls_off% "memset") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memset")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memset")), (ls_hook% "memset"),
    withPanics_trTrap_ne C abs (by decide)]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns,
    hookMemset_eq_memsetHook]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_272972 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt? (b + bv% (ls_off% "memset")) = some memsetHook := by
  rw [show (bv% (ls_off% "memset") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memset")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memset")), (ls_hook% "memset")]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns,
    hookMemset_eq_memsetHook]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_273012_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).externAt? (b + bv% (ls_off% "memcpy")) = some memcpyHook := by
  rw [show (bv% (ls_off% "memcpy") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memcpy")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memcpy")), (ls_hook% "memcpy"),
    withPanics_trTrap_ne C abs (by decide)]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns,
    hookMemcpy_eq_memcpyHook]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_273012 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt? (b + bv% (ls_off% "memcpy")) = some memcpyHook := by
  rw [show (bv% (ls_off% "memcpy") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memcpy")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memcpy")), (ls_hook% "memcpy")]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns,
    hookMemcpy_eq_memcpyHook]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_273212_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).externAt? (b + bv% (ls_off% "sha2::sha256::compress256")) = some (compress256Hook C.F) := by
  rw [show (bv% (ls_off% "sha2::sha256::compress256") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "sha2::sha256::compress256")), (ls_hook% "sha2::sha256::compress256"),
    withPanics_trTrap_ne C abs (by decide)]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns]

@[scoped simp, arm64_norm]
theorem tripleRatchetProgAt_externAt_273212 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt? (b + bv% (ls_off% "sha2::sha256::compress256")) = some (compress256Hook C.F) := by
  rw [show (bv% (ls_off% "sha2::sha256::compress256") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "sha2::sha256::compress256")), (ls_hook% "sha2::sha256::compress256")]
  simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns, LibsignalSession.sessionExterns]

/-- Take one ordinary instruction step of `RunsToFrom` on `tripleRatchetProgAt` and normalize the resulting state. -/
macro "s2_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

/-! ## Byte, Word, and `ShaState` Helpers -/

theorem toBEBytes_4_eq_list (w : BitVec 32) :
    toBEBytes 4 w =
      [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] :=
  rfl

theorem toBEBytes_8_eq_list (v : BitVec 64) :
    toBEBytes 8 v =
      [v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
       v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb' 8 8, v.extractLsb' 0 8] :=
  rfl

theorem toLEBytes_8_rev64 (v : BitVec 64) :
    toLEBytes 8 (rev64 v) = toBEBytes 8 v := by
  rw [Bytes.toLEBytes_8_eq_list, toBEBytes_8_eq_list]
  dsimp only [rev64]
  simp only [List.cons.injEq, and_true]
  generalize v.extractLsb' 0 8 = b0, v.extractLsb' 8 8 = b1, v.extractLsb' 16 8 = b2,
    v.extractLsb' 24 8 = b3, v.extractLsb' 32 8 = b4, v.extractLsb' 40 8 = b5,
    v.extractLsb' 48 8 = b6, v.extractLsb' 56 8 = b7
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem write64_rev64_eq_writeBytes_toBEBytes (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    m.write64 a (rev64 v) = m.writeBytes a (toBEBytes 8 v) := by
  rw [Bytes.write64_eq_writeBytes, toLEBytes_8_rev64]

private theorem extractLsb'_zeroExtend_64 (w : BitVec 32) (s : ℕ) (hs : s + 8 ≤ 32 := by decide) :
    (w.zeroExtend 64).extractLsb' s 8 = w.extractLsb' s 8 := by
  bv_bits

theorem toLEBytes_4_rev32 (w : BitVec 32) :
    toLEBytes 4 ((rev32_64 (w.zeroExtend 64)).truncate 32) = toBEBytes 4 w := by
  rw [Bytes.toLEBytes_4_eq_list, toBEBytes_4_eq_list]
  dsimp only [rev32_64]
  rw [extractLsb'_zeroExtend_64 w 0, extractLsb'_zeroExtend_64 w 8,
      extractLsb'_zeroExtend_64 w 16, extractLsb'_zeroExtend_64 w 24]
  generalize w.extractLsb' 0 8 = b0, w.extractLsb' 8 8 = b1,
    w.extractLsb' 16 8 = b2, w.extractLsb' 24 8 = b3
  simp only [List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem write32_rev32_eq_writeBytes_toBEBytes (m : Memory) (a : BitVec 64) (w : BitVec 32) :
    m.write32 a ((rev32_64 (w.zeroExtend 64)).truncate 32) = m.writeBytes a (toBEBytes 4 w) := by
  rw [Bytes.write32_eq_writeBytes, toLEBytes_4_rev32]

theorem readBytes_4_eq (m : Memory) (a : BitVec 64) :
    m.readBytes a 4 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64)] := by
  simp only [Memory.readBytes, BitVec.add_assoc]
  rfl

theorem read32_of_readBytes_toLEBytes_4 (m : Memory) (a : BitVec 64) (w : BitVec 32)
    (h : m.readBytes a 4 = toLEBytes 4 w) :
    m.read32 a = w := by
  rw [readBytes_4_eq, Bytes.toLEBytes_4_eq_list] at h
  simp only [List.cons.injEq] at h
  rcases h with ⟨h0, h1, h2, h3, -⟩
  dsimp only [Memory.read32]
  simp only [BitVec.add_zero]
  rw [h0, h1, h2, h3]
  bv_bits

theorem shaState_toList_eq (st : ShaState) :
    st.toList = [st.get 0, st.get 1, st.get 2, st.get 3, st.get 4, st.get 5, st.get 6, st.get 7] := by
  rcases st with ⟨l, hl⟩
  rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals (first | rfl | (simp at hl))

theorem shaStateBytes_eq_append (st : ShaState) :
    shaStateBytes st =
      toLEBytes 4 (st.get 0) ++ toLEBytes 4 (st.get 1) ++
      toLEBytes 4 (st.get 2) ++ toLEBytes 4 (st.get 3) ++
      toLEBytes 4 (st.get 4) ++ toLEBytes 4 (st.get 5) ++
      toLEBytes 4 (st.get 6) ++ toLEBytes 4 (st.get 7) := by
  unfold shaStateBytes
  rw [shaState_toList_eq]
  simp [List.flatMap_cons, List.flatMap_nil, List.append_assoc]

/-- The digest bytes of a state: each word big-endian (`sha256With`'s output). -/
def digestBytes (h : ShaState) : List (BitVec 8) :=
  h.toList.flatMap (toBEBytes 4)

theorem digestBytes_eq_append (st : ShaState) :
    digestBytes st =
      toBEBytes 4 (st.get 0) ++ toBEBytes 4 (st.get 1) ++
      toBEBytes 4 (st.get 2) ++ toBEBytes 4 (st.get 3) ++
      toBEBytes 4 (st.get 4) ++ toBEBytes 4 (st.get 5) ++
      toBEBytes 4 (st.get 6) ++ toBEBytes 4 (st.get 7) := by
  unfold digestBytes
  rw [shaState_toList_eq]
  simp [List.flatMap_cons, List.flatMap_nil, List.append_assoc]

@[scoped simp] theorem shaStateBytes_length (st : ShaState) :
    (shaStateBytes st).length = 32 := by
  rw [shaStateBytes_eq_append]
  simp

@[scoped simp] theorem digestBytes_length (st : ShaState) :
    (digestBytes st).length = 32 := by
  rw [digestBytes_eq_append]
  simp [toBEBytes]

theorem shaStateBytes_slice_word (st : ShaState) (i : Fin 8) :
    ((shaStateBytes st).drop (4 * i.val)).take 4 = toLEBytes 4 (st.get i) := by
  rw [shaStateBytes_eq_append]
  fin_cases i <;>
    simp [Bytes.toLEBytes_4_eq_list]

theorem read32_word_of_shaStateBytes (m : Memory) (a : BitVec 64) (st : ShaState)
    (h : m.readBytes a 32 = shaStateBytes st) (i : Fin 8) :
    m.read32 (a + BitVec.ofNat 64 (4 * i.val)) = st.get i := by
  apply read32_of_readBytes_toLEBytes_4
  have hlen : (shaStateBytes st).length = 32 := shaStateBytes_length st
  have hslice := Bytes.readBytes_slice_of_readBytes_eq m a (shaStateBytes st)
    (by rw [hlen]; exact h) (4 * i.val) 4 (by rw [hlen]; omega)
  rw [hslice, shaStateBytes_slice_word]

theorem read32_words_of_shaStateBytes (m : Memory) (a : BitVec 64) (st : ShaState)
    (h : m.readBytes a 32 = shaStateBytes st) :
    m.read32 a = st.get 0 ∧
    m.read32 (a + 4#64) = st.get 1 ∧
    m.read32 (a + 8#64) = st.get 2 ∧
    m.read32 (a + 12#64) = st.get 3 ∧
    m.read32 (a + 16#64) = st.get 4 ∧
    m.read32 (a + 20#64) = st.get 5 ∧
    m.read32 (a + 24#64) = st.get 6 ∧
    m.read32 (a + 28#64) = st.get 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using read32_word_of_shaStateBytes m a st h 0
  · simpa using read32_word_of_shaStateBytes m a st h 1
  · simpa using read32_word_of_shaStateBytes m a st h 2
  · simpa using read32_word_of_shaStateBytes m a st h 3
  · simpa using read32_word_of_shaStateBytes m a st h 4
  · simpa using read32_word_of_shaStateBytes m a st h 5
  · simpa using read32_word_of_shaStateBytes m a st h 6
  · simpa using read32_word_of_shaStateBytes m a st h 7

theorem readShaState_of_shaStateBytes (m : Memory) (a : BitVec 64) (st : ShaState)
    (h : m.readBytes a 32 = shaStateBytes st) :
    readShaState m a = st := by
  apply List.Vector.ext
  intro i
  simp only [readShaState, List.Vector.get_ofFn]
  exact read32_word_of_shaStateBytes m a st h i

theorem chunks64_single_foldl (F : ShaState → List (BitVec 8) → ShaState) (st : ShaState)
    (bs : List (BitVec 8)) (h : bs.length = 64) :
    (chunks64 bs).foldl F st = F st bs := by
  have h1 : chunks64 bs = [bs] := by
    unfold chunks64
    rw [h]
    change [(bs.drop 0).take 64] = [bs]
    simp [List.take_of_length_le (by omega : bs.length ≤ 64)]
  rw [h1, List.foldl_cons, List.foldl_nil]

theorem compress256Hook_eq (F : ShaState → List (BitVec 8) → ShaState) {s : State}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64) :
    compress256Hook F s =
      (s.setMem (s.mem.writeBytes stPtr (shaStateBytes (F st blk)))).setPC lr := by
  dsimp only [compress256Hook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (shaStateBytes ((chunks64 (s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat))).foldl
        F (readShaState s.mem (s.readReg64 .x0)))))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2]
  change (s.setMem (s.mem.writeBytes stPtr
    (shaStateBytes ((chunks64 (s.mem.readBytes blkPtr 64)).foldl F (readShaState s.mem stPtr))))).setPC lr = _
  rw [readShaState_of_shaStateBytes s.mem stPtr st hst, hblk, chunks64_single_foldl F st blk hlen]

theorem memsetHook_eq {s : State} {dst lr : BitVec 64} {len : ℕ}
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr) :
    memsetHook s =
      (s.setMem (s.mem.writeBytes dst (List.replicate len 0#8))).setPC lr := by
  dsimp only [memsetHook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (List.replicate (s.readReg64 .x2).toNat ((s.readReg64 .x1).truncate 8)))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2]

theorem memcpyHook_eq {s : State} {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs) :
    memcpyHook s =
      (s.setMem (s.mem.writeBytes dst bs)).setPC lr := by
  dsimp only [memcpyHook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hread]

theorem s2_compress256_step_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom (trTrapProgAt b C abs) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q) :
    RunsToFrom (trTrapProgAt b C abs) s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (trTrapProgAt b C abs).externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273212_trap b C abs
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_compress256_step (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q) :
    RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (tripleRatchetProgAt b C ctl abs).externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273212 b C ctl abs
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memset_step_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : ℕ}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memset"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom (trTrapProgAt b C abs) s₀
      ((s.setMem (s.mem.writeBytes dst (List.replicate len 0#8))).setPC lr) Q) :
    RunsToFrom (trTrapProgAt b C abs) s₀ s Q := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst (List.replicate len 0#8).length = true := by
    rw [List.length_replicate]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (trTrapProgAt b C abs).externAt? s.pc = some memsetHook := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_272972_trap b C abs
  have hstate := memsetHook_eq hx0 hx1 hx2 hlr
  have hkeep : s.mem.KeepsFrozen (memsetHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memsetHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memset_step (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : ℕ}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memset"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀
      ((s.setMem (s.mem.writeBytes dst (List.replicate len 0#8))).setPC lr) Q) :
    RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀ s Q := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst (List.replicate len 0#8).length = true := by
    rw [List.length_replicate]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (tripleRatchetProgAt b C ctl abs).externAt? s.pc = some memsetHook := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_272972 b C ctl abs
  have hstate := memsetHook_eq hx0 hx1 hx2 hlr
  have hkeep : s.mem.KeepsFrozen (memsetHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memsetHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memcpy_step_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom (trTrapProgAt b C abs) s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q) :
    RunsToFrom (trTrapProgAt b C abs) s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (trTrapProgAt b C abs).externAt? s.pc = some memcpyHook := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273012_trap b C abs
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memcpy_step (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q) :
    RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (tripleRatchetProgAt b C ctl abs).externAt? s.pc = some memcpyHook := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273012 b C ctl abs
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## `Frame`, `HmacSt`, and `hmacWith_short` -/

/-- `m'` agrees with `m` (bytes and permissions) outside the regions `rs`. -/
def Frame (m m' : Memory) (rs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a : BitVec 64, (∀ r ∈ rs, OutsideRegion r.1 r.2 a) → m'.read8 a = m.read8 a) ∧
    m'.perm = m.perm ∧
    (∀ a : BitVec 64, (∀ r ∈ rs, OutsideRegion r.1 r.2 a) → m'.isLazyFree a = m.isLazyFree a) ∧
    (∀ a : BitVec 64, m.isLazyFree a = false → m'.isLazyFree a = false) ∧
    (∀ a : BitVec 64, m.isAnon a = true → m'.isAnon a = true)

abbrev RW (m : Memory) (a : BitVec 64) (n : ℕ) : Prop := Memory.RW m a n

/-- **`HmacSt m a F key msg`**: the `Hmac<Sha256>` (0x90 bytes) at `a` is the MAC state of key
`key` after absorbing `msg`, with `|msg| < 64`. -/
def HmacSt (m : Memory) (a : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : Prop :=
  msg.length < 64 ∧
  m.readBytes a msg.length = msg ∧
  m.read8 (a + 0x3f#64) = BitVec.ofNat 8 msg.length ∧
  m.readBytes (a + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key) ∧
  m.read64 (a + 0x60#64) = 1#64 ∧
  m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
  m.read64 (a + 0x88#64) = 1#64

/-- The last (only) message block of the inner hash for `|msg| < 56` after the key block:
`msg ‖ 0x80 ‖ 0… ‖ BE64(8·(64 + |msg|))`, 64 bytes. -/
def innerLastBlock (msg : List (BitVec 8)) : List (BitVec 8) :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + msg.length)))

/-- The outer block for a 32-byte inner digest `d`: `d ‖ 0x80 ‖ 0×23 ‖ BE64(768)`. -/
def outerBlock (d : List (BitVec 8)) : List (BitVec 8) :=
  d ++ [0x80] ++ List.replicate 23 0 ++ toBEBytes 8 (BitVec.ofNat 64 768)

@[scoped simp] private theorem chunks64_length (bs : List (BitVec 8)) :
    (chunks64 bs).length = bs.length / 64 := by
  simp [chunks64]

@[scoped simp] private theorem chunks64_getElem (bs : List (BitVec 8)) (i : ℕ)
    (hi : i < (chunks64 bs).length) :
    (chunks64 bs)[i] = (bs.drop (64 * i)).take 64 := by
  simp [chunks64]

private theorem chunks64_of_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [← List.length_eq_zero_iff, chunks64_length]
  omega

private theorem chunks64_append_64 {a b : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 (a ++ b) = a :: chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]
  · cases i with
    | zero =>
      simp [ha]
    | succ j =>
      simp only [chunks64_getElem, List.getElem_cons_succ]
      have hdrop : 64 * (j + 1) = a.length + 64 * j := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

private theorem chunks64_single {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  conv_lhs => rw [← List.append_nil a]
  rw [chunks64_append_64 ha, chunks64_of_lt (by simp)]

@[scoped simp] theorem toBEBytes_length (n : ℕ) {w : ℕ} (x : BitVec w) :
    (toBEBytes n x).length = n := by
  simp [toBEBytes]

@[scoped simp] theorem sha256With_length (F : ShaState → List (BitVec 8) → ShaState)
    (m : List (BitVec 8)) :
    (sha256With F m).length = 32 :=
  digestBytes_length _

private theorem sha256With_two_blocks (F : ShaState → List (BitVec 8) → ShaState)
    (m a b : List (BitVec 8)) (hpad : sha256Pad m = a ++ b)
    (ha : a.length = 64) (hb : b.length = 64) :
    sha256With F m = digestBytes (F (F sha256IV a) b) := by
  unfold sha256With digestBytes
  rw [hpad, chunks64_append_64 ha, chunks64_single hb]
  rfl

/-- Single-block inner/outer compression form of `hmacWith` for `|key| ≤ 64` and `|msg| < 56`. -/
theorem hmacWith_short (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8))
    (hk : key.length ≤ 64) (hm : msg.length < 56) :
    hmacWith F key msg =
      digestBytes (F (hmacOuterInit F key)
        (outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg))))) := by
  unfold hmacWith
  have hk_not_gt : ¬ (64 < key.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  change sha256With F ((hmacKeyBlock key).map (· ^^^ 0x5c) ++
    sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ msg)) = _
  have hkb_len : (hmacKeyBlock key).length = 64 := by
    simp [hmacKeyBlock]; omega
  have hipad_len : ((hmacKeyBlock key).map (· ^^^ 0x36)).length = 64 := by
    simp [hkb_len]
  have hopad_len : ((hmacKeyBlock key).map (· ^^^ 0x5c)).length = 64 := by
    simp [hkb_len]
  have hinner_blk_len : (innerLastBlock msg).length = 64 := by
    simp [innerLastBlock]; omega
  have hinner_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x36) ++ msg) =
      (hmacKeyBlock key).map (· ^^^ 0x36) ++ innerLastBlock msg := by
    unfold sha256Pad innerLastBlock
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x36) ++ msg).length = 64 + msg.length := by
      simp [hkb_len]
    have hmod : (119 - (64 + msg.length) % 64) % 64 = 55 - msg.length := by omega
    rw [hlen, hmod]
    simp only [List.append_assoc]
  have hinner : sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ msg) =
      digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)) :=
    sha256With_two_blocks F _ _ _ hinner_pad hipad_len hinner_blk_len
  rw [hinner]
  set d := digestBytes (F (hmacInnerInit F key) (innerLastBlock msg))
  have hd_len : d.length = 32 := digestBytes_length _
  have houter_blk_len : (outerBlock d).length = 64 := by
    simp [outerBlock, hd_len]
  have houter_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d) =
      (hmacKeyBlock key).map (· ^^^ 0x5c) ++ outerBlock d := by
    unfold sha256Pad outerBlock
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d).length = 96 := by
      simp [hkb_len, hd_len]
    rw [hlen]
    simp only [List.append_assoc]
  exact sha256With_two_blocks F _ _ _ houter_pad hopad_len houter_blk_len

@[scoped simp] theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith
  exact sha256With_length F _

theorem rw_of_perm_eq {m₁ m₂ : Memory} {a : BitVec 64} {n : ℕ} {P Q : Prop}
    (hperm : m₂.perm = m₁.perm ∧ P ∧ (∀ x, m₁.isLazyFree x = false → m₂.isLazyFree x = false) ∧ Q)
    (hrw : m₁.RW a n) : m₂.RW a n :=
  Memory.RW.of_perm_eq hperm.1 hperm.2.2.1 hrw

theorem fsp_aligned {sp : BitVec 64} (h : (sp &&& 0b1111#64) = 0#64) :
    ((sp - 144#64) &&& 15#64) = 0#64 := by
  change (sp &&& 15#64) = 0#64 at h
  bv_bits

theorem Frame.refl (m : Memory) (rs : List (BitVec 64 × ℕ)) : Frame m m rs :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h⟩

theorem Frame.trans {m₁ m₂ m₃ : Memory} {rs : List (BitVec 64 × ℕ)}
    (h1 : Frame m₁ m₂ rs) (h2 : Frame m₂ m₃ rs) : Frame m₁ m₃ rs :=
  ⟨fun a hout => (h2.1 a hout).trans (h1.1 a hout),
   h2.2.1.trans h1.2.1,
   fun a hout => (h2.2.2.1 a hout).trans (h1.2.2.1 a hout),
   fun a ha => h2.2.2.2.1 a (h1.2.2.2.1 a ha),
   fun a ha => h2.2.2.2.2 a (h1.2.2.2.2 a ha)⟩

theorem Frame.mono {m₁ m₂ : Memory} {rs₁ rs₂ : List (BitVec 64 × ℕ)}
    (h : Frame m₁ m₂ rs₁)
    (hsub : ∀ a, (∀ r ∈ rs₂, OutsideRegion r.1 r.2 a) → (∀ r ∈ rs₁, OutsideRegion r.1 r.2 a)) :
    Frame m₁ m₂ rs₂ :=
  ⟨fun a ha => h.1 a (hsub a ha),
   h.2.1,
   fun a ha => h.2.2.1 a (hsub a ha),
   h.2.2.2.1,
   h.2.2.2.2⟩

theorem Frame.read8_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {a : BitVec 64}
    (hout : ∀ r ∈ rs, OutsideRegion r.1 r.2 a) :
    m₂.read8 a = m₁.read8 a :=
  hf.1 a hout

theorem Frame.readBytes_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {addr : BitVec 64} {len : ℕ}
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (fun r hr => (hd r hr).outside hin hlen)

theorem Frame.read64_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {addr : BitVec 64}
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := hf.readBytes_eq hd (by decide)
  rw [Bytes.readBytes_8_eq, Bytes.readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

structure MprImpl (Q P : Prop) : Prop where
  mpr : P → Q

theorem Frame.rw_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (RW m₂ addr len) (RW m₁ addr len) :=
  ⟨Memory.RW.of_perm_eq hf.2.1 hf.2.2.2.1⟩

theorem Frame.readable_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (m₂.Readable addr len) (m₁.Readable addr len) :=
  ⟨Memory.Readable.of_perm_eq hf.2.1 hf.2.2.2.1⟩

theorem Frame.trans_agreesOutside {m₁ m₂ m₃ : Memory} {rs : List (BitVec 64 × ℕ)}
    {base : BitVec 64} {len : ℕ}
    (hf : Frame m₁ m₂ rs) (hmem : (base, len) ∈ rs) (hag : AgreesOutside m₂ m₃ base len) :
    Frame m₁ m₃ rs :=
  ⟨fun a hout => (hag.1 a (hout (base, len) hmem)).trans (hf.1 a hout),
   hag.2.1.trans hf.2.1,
   fun a hout => (hag.2.2.1 a (hout (base, len) hmem)).trans (hf.2.2.1 a hout),
   fun a ha => hag.2.2.2.1 a (hf.2.2.2.1 a ha),
   fun a ha => hag.2.2.2.2 a (hf.2.2.2.2 a ha)⟩

theorem AgreesOutside.mono_sub {m₁ m₂ : Memory} {rbase base : BitVec 64} {rlen len : ℕ}
    (hag : AgreesOutside m₁ m₂ base len) (hsub : (base - rbase).toNat + len ≤ rlen) :
    AgreesOutside m₁ m₂ rbase rlen := by
  have hout (a : BitVec 64) (ha : OutsideRegion rbase rlen a) : OutsideRegion base len a := by
    clear * - ha hsub; unfold OutsideRegion at ha ⊢; bv_omega
  exact ⟨fun a ha => hag.1 a (hout a ha), hag.2.1,
    fun a ha => hag.2.2.1 a (hout a ha), hag.2.2.2.1,
    hag.2.2.2.2⟩

theorem Frame.trans_agreesOutside_sub {m₁ m₂ m₃ : Memory} {rs : List (BitVec 64 × ℕ)}
    {rbase base : BitVec 64} {rlen len : ℕ}
    (hf : Frame m₁ m₂ rs) (hmem : (rbase, rlen) ∈ rs)
    (hsub : (base - rbase).toNat + len ≤ rlen)
    (hag : AgreesOutside m₂ m₃ base len) :
    Frame m₁ m₃ rs :=
  Frame.trans_agreesOutside hf hmem (AgreesOutside.mono_sub hag hsub)

def Memory.splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) : Memory :=
  ⟨fun a => if InRegion b n a then mf.cells a else m0.cells a⟩

@[simp] theorem Memory.cells_splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) (a : BitVec 64) :
    (Memory.splice m0 mf b n).cells a = if InRegion b n a then mf.cells a else m0.cells a := rfl

@[simp] theorem Memory.read8_splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) (a : BitVec 64) :
    (Memory.splice m0 mf b n).read8 a = if InRegion b n a then mf.read8 a else m0.read8 a := by
  by_cases h : InRegion b n a <;> simp [Memory.read8, Memory.splice, h]

@[simp] theorem Memory.perm_splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) (a : BitVec 64) :
    (Memory.splice m0 mf b n).perm a = if InRegion b n a then mf.perm a else m0.perm a := by
  by_cases h : InRegion b n a <;> simp [Memory.perm, Memory.splice, h]

@[simp] theorem Memory.isLazyFree_splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) (a : BitVec 64) :
    (Memory.splice m0 mf b n).isLazyFree a = if InRegion b n a then mf.isLazyFree a else m0.isLazyFree a := by
  by_cases h : InRegion b n a <;> simp [Memory.isLazyFree, Memory.splice, h]

@[simp] theorem Memory.isAnon_splice (m0 mf : Memory) (b : BitVec 64) (n : Nat) (a : BitVec 64) :
    (Memory.splice m0 mf b n).isAnon a = if InRegion b n a then mf.isAnon a else m0.isAnon a := by
  by_cases h : InRegion b n a <;> simp [Memory.isAnon, Memory.splice, h]

theorem Frame.splice_agreesOutside_left {m0 mf : Memory} {rs : List (BitVec 64 × ℕ)}
    {b : BitVec 64} {n : ℕ} (hf : Frame m0 mf rs) :
    AgreesOutside m0 (Memory.splice m0 mf b n) b n := by
  have hnot (a : BitVec 64) (ha : OutsideRegion b n a) : ¬ InRegion b n a :=
    (outsideRegion_iff_not_inRegion b n a).mp ha
  refine ⟨fun a ha => by simp [hnot a ha], ?_, fun a ha => by simp [hnot a ha], fun a => ?_, fun a => ?_⟩
  · funext a; rw [Memory.perm_splice]; split
    · exact congrFun hf.2.1 a
    · rfl
  · rw [Memory.isLazyFree_splice]; split
    · exact hf.2.2.2.1 a
    · exact id
  · rw [Memory.isAnon_splice]; split
    · exact hf.2.2.2.2 a
    · exact id

theorem Frame.splice_agreesOutside_two {m0 mf : Memory} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    (hf : Frame m0 mf [(b1, n1), (b2, n2)]) :
    AgreesOutside (Memory.splice m0 mf b2 n2) mf b1 n1 := by
  have hout (a : BitVec 64) (ha1 : OutsideRegion b1 n1 a) (hnot2 : ¬ InRegion b2 n2 a) :
      ∀ r ∈ [(b1, n1), (b2, n2)], OutsideRegion r.1 r.2 a := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha1
    · exact (outsideRegion_iff_not_inRegion b2 n2 a).mpr hnot2
  refine ⟨fun a ha1 => ?_, ?_, fun a ha1 => ?_, fun a => ?_, fun a => ?_⟩
  · rw [Memory.read8_splice]; split
    · rfl
    · rename_i hnot2; exact hf.1 a (hout a ha1 hnot2)
  · funext a; rw [Memory.perm_splice]; split
    · rfl
    · exact congrFun hf.2.1 a
  · rw [Memory.isLazyFree_splice]; split
    · rfl
    · rename_i hnot2; exact hf.2.2.1 a (hout a ha1 hnot2)
  · rw [Memory.isLazyFree_splice]; split
    · exact id
    · exact hf.2.2.2.1 a
  · rw [Memory.isAnon_splice]; split
    · exact id
    · exact hf.2.2.2.2 a

theorem Frame.splice_frame_three {m0 mf : Memory} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    (hf : Frame m0 mf [(b1, n1), (b2, n2), (b3, n3)]) :
    Frame (Memory.splice m0 mf b3 n3) mf [(b1, n1), (b2, n2)] := by
  have hout (a : BitVec 64) (ha12 : ∀ r ∈ [(b1, n1), (b2, n2)], OutsideRegion r.1 r.2 a)
      (hnot3 : ¬ InRegion b3 n3 a) :
      ∀ r ∈ [(b1, n1), (b2, n2), (b3, n3)], OutsideRegion r.1 r.2 a := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ha12 (b1, n1) (by simp)
    · exact ha12 (b2, n2) (by simp)
    · exact (outsideRegion_iff_not_inRegion b3 n3 a).mpr hnot3
  refine ⟨fun a ha12 => ?_, ?_, fun a ha12 => ?_, fun a => ?_, fun a => ?_⟩
  · rw [Memory.read8_splice]; split
    · rfl
    · rename_i hnot3; exact hf.1 a (hout a ha12 hnot3)
  · funext a; rw [Memory.perm_splice]; split
    · rfl
    · exact congrFun hf.2.1 a
  · rw [Memory.isLazyFree_splice]; split
    · rfl
    · rename_i hnot3; exact hf.2.2.1 a (hout a ha12 hnot3)
  · rw [Memory.isLazyFree_splice]; split
    · exact id
    · exact hf.2.2.2.1 a
  · rw [Memory.isAnon_splice]; split
    · exact id
    · exact hf.2.2.2.2 a

/-- Saved callee-saved registers in the upper 80 bytes `[fsp + 0x40, fsp + 0x90)` of the frame. -/
def FinSaved (s0 : State) (fsp : BitVec 64) (m : Memory) : Prop :=
  m.read64 (fsp + 0x40#64) = s0.readReg64 .x29 ∧
  m.read64 (fsp + 0x48#64) = s0.readReg64 .lr ∧
  m.read64 (fsp + 0x50#64) = s0.readReg64 .x25 ∧
  m.read64 (fsp + 0x60#64) = s0.readReg64 .x24 ∧
  m.read64 (fsp + 0x68#64) = s0.readReg64 .x23 ∧
  m.read64 (fsp + 0x70#64) = s0.readReg64 .x22 ∧
  m.read64 (fsp + 0x78#64) = s0.readReg64 .x21 ∧
  m.read64 (fsp + 0x80#64) = s0.readReg64 .x20 ∧
  m.read64 (fsp + 0x88#64) = s0.readReg64 .x19

theorem FinSaved.of_agreesOutside {s0 : State} {fsp : BitVec 64} {m₁ m₂ : Memory}
    {base : BitVec 64} {len : ℕ}
    (hs : FinSaved s0 fsp m₁)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have sub8 (off : BitVec 64) (hoff : (off - (fsp + 0x40#64)).toNat + 8 ≤ 0x50) :
      DisjointRegions base len off 8 :=
    hd.sub_right off ⟨by decide, hoff⟩
  exact ⟨(hag.read64_eq (sub8 (fsp + 0x40#64) (by bv_omega))).trans h1,
         (hag.read64_eq (sub8 (fsp + 0x48#64) (by bv_omega))).trans h2,
         (hag.read64_eq (sub8 (fsp + 0x50#64) (by bv_omega))).trans h3,
         (hag.read64_eq (sub8 (fsp + 0x60#64) (by bv_omega))).trans h4,
         (hag.read64_eq (sub8 (fsp + 0x68#64) (by bv_omega))).trans h5,
         (hag.read64_eq (sub8 (fsp + 0x70#64) (by bv_omega))).trans h6,
         (hag.read64_eq (sub8 (fsp + 0x78#64) (by bv_omega))).trans h7,
         (hag.read64_eq (sub8 (fsp + 0x80#64) (by bv_omega))).trans h8,
         (hag.read64_eq (sub8 (fsp + 0x88#64) (by bv_omega))).trans h9⟩

theorem HmacSt.of_agreesOutside {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    {base : BitVec 64} {len : ℕ}
    (hst : HmacSt m₁ hm F key msg)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len hm 0x90) :
    HmacSt m₂ hm F key msg := by
  rcases hst with ⟨hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : msg.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · have hd' : DisjointRegions base len hm msg.length :=
        hd.sub_right hm ⟨by omega, by simp; omega⟩
      exact (hag.readBytes_eq hd' (by omega)).trans hmsg
  · have hout8 : OutsideRegion base len (hm + 0x3f#64) := by
      rcases hd with ⟨hd1, hd2⟩
      unfold OutsideRegion; bv_omega
    exact (hag.1 _ hout8).trans hpos
  · have hd' : DisjointRegions base len (hm + 0x40#64) 32 :=
      hd.sub_right (hm + 0x40#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hin
  · have hd' : DisjointRegions base len (hm + 0x60#64) 8 :=
      hd.sub_right (hm + 0x60#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hibl
  · have hd' : DisjointRegions base len (hm + 0x68#64) 32 :=
      hd.sub_right (hm + 0x68#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hout
  · have hd' : DisjointRegions base len (hm + 0x88#64) 8 :=
      hd.sub_right (hm + 0x88#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hobl

/-! ## Memory and `HmacSt` Copy Helpers -/

theorem zeroExtend64_truncate32_ofNat64 {n : ℕ} (h : n < 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem zeroExtend64_ofNat8 {n : ℕ} (h : n < 64) :
    (BitVec.ofNat 8 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (by omega : n < 256), Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]

theorem toLEBytes_8_read64 (m : Memory) (a : BitVec 64) :
    toLEBytes 8 (m.read64 a) = m.readBytes a 8 := by
  dsimp only [toLEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr,
    Memory.read64, Memory.readBytes]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  generalize m.read8 a = b0, m.read8 (a + 1#64) = b1, m.read8 (a + 2#64) = b2,
    m.read8 (a + 3#64) = b3, m.read8 (a + 4#64) = b4, m.read8 (a + 5#64) = b5,
    m.read8 (a + 6#64) = b6, m.read8 (a + 7#64) = b7
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩⟩⟩⟩⟩

@[scoped simp, arm64_norm]
theorem extractLsb'_56_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 56 8 = m.read8 (a + 7#64) := by
  dsimp only [Memory.read64]
  generalize m.read8 a = b0, m.read8 (a + 1#64) = b1, m.read8 (a + 2#64) = b2,
    m.read8 (a + 3#64) = b3, m.read8 (a + 4#64) = b4, m.read8 (a + 5#64) = b5,
    m.read8 (a + 6#64) = b6, m.read8 (a + 7#64) = b7
  bv_bits

theorem readBytes_16_eq_read64 (m : Memory) (a : BitVec 64) :
    m.readBytes a 16 =
      toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64)) := by
  rw [show (16 : ℕ) = 8 + 8 from rfl, Bytes.readBytes_add m a 8 8,
      ← toLEBytes_8_read64, ← toLEBytes_8_read64]

theorem readBytes_16_eq_of_read64_eq {m₁ m₂ : Memory} {a b : BitVec 64}
    (h0 : m₁.read64 a = m₂.read64 b)
    (h1 : m₁.read64 (a + 8#64) = m₂.read64 (b + 8#64)) :
    m₁.readBytes a 16 = m₂.readBytes b 16 := by
  rw [readBytes_16_eq_read64 m₁ a, readBytes_16_eq_read64 m₂ b, h0, h1]

theorem readBytes_32_eq_read64 (m : Memory) (a : BitVec 64) :
    m.readBytes a 32 =
      (toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64))) ++
      (toLEBytes 8 (m.read64 (a + 16#64)) ++ toLEBytes 8 (m.read64 (a + 24#64))) := by
  rw [show (32 : ℕ) = 16 + 16 from rfl, Bytes.readBytes_add m a 16 16,
      readBytes_16_eq_read64 m a, readBytes_16_eq_read64 m (a + BitVec.ofNat 64 16)]
  have h16 : a + BitVec.ofNat 64 16 = a + 16#64 := rfl
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_lin
  rw [h16, h24]

theorem readBytes_32_eq_of_read64_eq {m₁ m₂ : Memory} {a₁ a₂ : BitVec 64}
    (h0 : m₁.read64 a₁ = m₂.read64 a₂)
    (h1 : m₁.read64 (a₁ + 8#64) = m₂.read64 (a₂ + 8#64))
    (h2 : m₁.read64 (a₁ + 16#64) = m₂.read64 (a₂ + 16#64))
    (h3 : m₁.read64 (a₁ + 24#64) = m₂.read64 (a₂ + 24#64)) :
    m₁.readBytes a₁ 32 = m₂.readBytes a₂ 32 := by
  rw [readBytes_32_eq_read64 m₁ a₁, readBytes_32_eq_read64 m₂ a₂, h0, h1, h2, h3]

theorem read8_add_7_of_read64_eq {m₁ m₂ : Memory} {a b : BitVec 64}
    (h : m₁.read64 a = m₂.read64 b) :
    m₁.read8 (a + 7#64) = m₂.read8 (b + 7#64) := by
  rw [← extractLsb'_56_8_read64 m₁ a, ← extractLsb'_56_8_read64 m₂ b, h]

theorem HmacSt.of_copy_empty {m₀ m : Memory} {src dst : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (hsrc : HmacSt m₀ src F key [])
    (h56  : m.read64 (dst + 56#64)  = m₀.read64 (src + 56#64))
    (h64  : m.read64 (dst + 64#64)  = m₀.read64 (src + 64#64))
    (h72  : m.read64 (dst + 72#64)  = m₀.read64 (src + 72#64))
    (h80  : m.read64 (dst + 80#64)  = m₀.read64 (src + 80#64))
    (h88  : m.read64 (dst + 88#64)  = m₀.read64 (src + 88#64))
    (h96  : m.read64 (dst + 96#64)  = m₀.read64 (src + 96#64))
    (h104 : m.read64 (dst + 104#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (dst + 112#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (dst + 120#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (dst + 128#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (dst + 136#64) = m₀.read64 (src + 136#64)) :
    HmacSt m dst F key [] := by
  rcases hsrc with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hd : dst + 0x3f#64 = (dst + 56#64) + 7#64 := by bv_lin
    have hs : src + 0x3f#64 = (src + 56#64) + 7#64 := by bv_lin
    rw [hd, read8_add_7_of_read64_eq h56, ← hs, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64
          (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80)
          (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104
          (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120)
          (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

theorem HmacSt.of_copy_19 {m₀ m : Memory} {src dst : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (hsrc : HmacSt m₀ src F key msg)
    (h0   : m.read64 dst            = m₀.read64 src)
    (h8   : m.read64 (dst + 8#64)   = m₀.read64 (src + 8#64))
    (h16  : m.read64 (dst + 16#64)  = m₀.read64 (src + 16#64))
    (h24  : m.read64 (dst + 24#64)  = m₀.read64 (src + 24#64))
    (h32  : m.read64 (dst + 32#64)  = m₀.read64 (src + 32#64))
    (h40  : m.read64 (dst + 40#64)  = m₀.read64 (src + 40#64))
    (h48  : m.read64 (dst + 48#64)  = m₀.read64 (src + 48#64))
    (h56  : m.read64 (dst + 56#64)  = m₀.read64 (src + 56#64))
    (h64  : m.read64 (dst + 64#64)  = m₀.read64 (src + 64#64))
    (h72  : m.read64 (dst + 72#64)  = m₀.read64 (src + 72#64))
    (h80  : m.read64 (dst + 80#64)  = m₀.read64 (src + 80#64))
    (h88  : m.read64 (dst + 88#64)  = m₀.read64 (src + 88#64))
    (h96  : m.read64 (dst + 96#64)  = m₀.read64 (src + 96#64))
    (h104 : m.read64 (dst + 104#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (dst + 112#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (dst + 120#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (dst + 128#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (dst + 136#64) = m₀.read64 (src + 136#64)) :
    HmacSt m dst F key msg := by
  rcases hsrc with ⟨hlen, hmsg, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h64_eq : m.readBytes dst 64 = m₀.readBytes src 64 := by
      rw [show (64 : ℕ) = 32 + 32 from rfl,
          Bytes.readBytes_add m dst 32 32, Bytes.readBytes_add m₀ src 32 32,
          readBytes_32_eq_of_read64_eq h0 h8 h16 h24,
          readBytes_32_eq_of_read64_eq h32
            (by simpa [BitVec.add_assoc] using h40)
            (by simpa [BitVec.add_assoc] using h48)
            (by simpa [BitVec.add_assoc] using h56)]
    have hslice1 := Bytes.readBytes_slice_of_readBytes_eq m dst (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]; exact h64_eq) 0 msg.length
      (by rw [Memory.readBytes_length]; omega)
    have hslice2 := Bytes.readBytes_slice_of_readBytes_eq m₀ src (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]) 0 msg.length
      (by rw [Memory.readBytes_length]; omega)
    simpa [hmsg] using hslice1.trans hslice2.symm
  · have hd : dst + 0x3f#64 = (dst + 56#64) + 7#64 := by bv_lin
    have hs : src + 0x3f#64 = (src + 56#64) + 7#64 := by bv_lin
    rw [hd, read8_add_7_of_read64_eq h56, ← hs, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64
          (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80)
          (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104
          (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120)
          (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

/-- The 32-byte HMAC key used by `hkdfExtract`: `s.toList` if `salt = some s`, or 32 zero bytes. -/
def effectiveSalt (salt : Salt) : List (BitVec 8) :=
  (salt.map List.Vector.toList).getD (List.replicate 32 0#8)

/-! ## `finalize_fixed` Cut Invariants -/

namespace FinalizeFixedProof

/-- Bundled preconditions of `finalize_fixed` at entry state `s0` (`0x30680`). -/
structure FinPre (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  msg_lt       : msg.length < 56
  hmac_st      : HmacSt s0.mem (s0.readReg64 .x1) F key msg
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

/-- Common invariant after the prologue (`0x3069c .. 0x30824`). -/
structure FinCommon (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 0x40#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : Frame s0.mem s.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

/-- Postcondition of `finalize_fixed` at return (`s'.pc = s0.readReg64 .lr`). -/
def FinPost (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

/-- Packaged `RunsTo` contract for `Hmac<Sha256>::finalize_fixed` on `tripleRatchetProgAt`. -/
def FinalizeFixedRunsTo (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  ∀ {key msg : List (BitVec 8)} {s0 : State},
    FinPre b C.F key msg s0 →
    RunsTo (tripleRatchetProgAt b C ctl abs) s0 (FinPost C.F key msg s0)

end FinalizeFixedProof

/-! ## `IsBlock` for `hmacCoreAt` and Multi-Block `Frame` Updates -/

theorem isBlock_hmacCoreAt (F : ShaCompress) (a : BitVec 64) (key msg : List (BitVec 8))
    (hlt : msg.length < 64) :
    IsBlock (hmacCoreAt F a key msg) a 0x90 (fun m => HmacSt m a F key msg) := by
  unfold hmacCoreAt hmacStateAt
  have hb1 : IsBlock (a ↦ₛ msg) a msg.length (fun m => m.readBytes a msg.length = msg) :=
    (IsBlock.pointsToBytes_len rfl).cast rfl (fun _ => and_iff_right (by omega))
  have hb2 : IsBlock (memRegion (a + BitVec.ofNat 64 msg.length) (63 - msg.length))
      (a + BitVec.ofNat 64 msg.length) (63 - msg.length) (fun _ => True) :=
    IsBlock.memRegion _ _
  have hb12 := hb1.sepConj hb2 rfl (by omega)
  have hlen12 : msg.length + (63 - msg.length) = 63 := by omega
  rw [hlen12] at hb12
  have hb3 : IsBlock ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 msg.length)
      (a + BitVec.ofNat 64 63) 1 (fun m => m.read8 (a + 0x3f#64) = BitVec.ofNat 8 msg.length) :=
    IsBlock.pointsTo8 (a + 0x3f#64) (BitVec.ofNat 8 msg.length)
  have hb13 := hb12.sepConj hb3 rfl (by decide)
  have hb4 : IsBlock ((a + 0x40#64) ↦ₛ shaStateBytes (hmacInnerInit F key))
      (a + BitVec.ofNat 64 64) 32
      (fun m => m.readBytes (a + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)) :=
    (IsBlock.pointsToBytes_len (shaStateBytes_length _)).cast rfl fun m => by
      rw [shaStateBytes_length]
      exact and_iff_right (by decide)
  have hb14 := hb13.sepConj hb4 rfl (by decide)
  have hb5 : IsBlock ((a + 0x60#64) ↦₆₄ 1#64)
      (a + BitVec.ofNat 64 96) 8 (fun m => m.read64 (a + 0x60#64) = 1#64) :=
    IsBlock.pointsTo64 (a + 0x60#64) 1#64
  have hb15 := hb14.sepConj hb5 rfl (by decide)
  have hb6 : IsBlock ((a + 0x68#64) ↦ₛ shaStateBytes (hmacOuterInit F key))
      (a + BitVec.ofNat 64 104) 32
      (fun m => m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)) :=
    (IsBlock.pointsToBytes_len (shaStateBytes_length _)).cast rfl fun m => by
      rw [shaStateBytes_length]
      exact and_iff_right (by decide)
  have hb16 := hb15.sepConj hb6 rfl (by decide)
  have hb7 : IsBlock ((a + 0x88#64) ↦₆₄ 1#64)
      (a + BitVec.ofNat 64 136) 8 (fun m => m.read64 (a + 0x88#64) = 1#64) :=
    IsBlock.pointsTo64 (a + 0x88#64) 1#64
  have hb17 := hb16.sepConj hb7 rfl (by decide)
  have hassoc :
      (⌜msg.length < 64⌝ ∗
        (a ↦ₛ msg) ∗ memRegion (a + BitVec.ofNat 64 msg.length) (63 - msg.length) ∗
          ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 msg.length) ∗
          ((a + 0x40#64) ↦ₛ shaStateBytes (hmacInnerInit F key)) ∗
          ((a + 0x60#64) ↦₆₄ 1#64) ∗
          ((a + 0x68#64) ↦ₛ shaStateBytes (hmacOuterInit F key)) ∗
          ((a + 0x88#64) ↦₆₄ 1#64)) =
      (⌜msg.length < 64⌝ ∗
        (((((((a ↦ₛ msg) ∗ memRegion (a + BitVec.ofNat 64 msg.length) (63 - msg.length)) ∗
          ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 msg.length)) ∗
          ((a + 0x40#64) ↦ₛ shaStateBytes (hmacInnerInit F key))) ∗
          ((a + 0x60#64) ↦₆₄ 1#64)) ∗
          ((a + 0x68#64) ↦ₛ shaStateBytes (hmacOuterInit F key))) ∗
          ((a + 0x88#64) ↦₆₄ 1#64))) := by ac_rfl
  rw [hassoc]
  refine (IsBlock.pure_sepConj (fun _ => hb17)).cast rfl fun m => ?_
  dsimp only [HmacSt]
  exact ⟨fun ⟨hlt', ⟨⟨⟨⟨⟨⟨h1, _⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ => ⟨hlt', h1, h3, h4, h5, h6, h7⟩,
         fun ⟨hlt', h1, h3, h4, h5, h6, h7⟩ => ⟨hlt', ⟨⟨⟨⟨⟨⟨h1, trivial⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩⟩

theorem Frame.update_two_blocks {P1 P1' P2 P2' R : SepProp}
    {b1 b2 : BitVec 64} {n1 n2 : Nat} {Φ1 Φ1' Φ2 Φ2' : Memory → Prop}
    {m0 mf : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (h0 : m0 ⊨ P1 ∗ (P2 ∗ R))
    (hf : Frame m0 mf [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' mf) (hΦ2' : Φ2' mf) :
    mf ⊨ P1' ∗ (P2' ∗ R) := by
  let m_mid : Memory := Memory.splice m0 mf b2 n2
  have hag1 : AgreesOutside m0 m_mid b2 n2 := hf.splice_agreesOutside_left
  have hag2 : AgreesOutside m_mid mf b1 n1 := hf.splice_agreesOutside_two
  have h0' : m0 ⊨ P2 ∗ (P1 ∗ R) := by
    rw [sepConj_left_comm]; exact h0
  have hmid' : m_mid ⊨ P2' ∗ (P1 ∗ R) :=
    hb2.update hb2' (Nat.le_refl _) h0' hag1
      (hb2'.congr mf m_mid (fun a ha => by simp [m_mid, ha]) hΦ2')
  have hmid : m_mid ⊨ P1 ∗ (P2' ∗ R) := by
    rw [sepConj_left_comm]; exact hmid'
  exact hb1.update hb1' (Nat.le_refl _) hmid hag2 hΦ1'

theorem Frame.update_three_blocks {P1 P1' P2 P2' P3 P3' R : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : Nat} {Φ1 Φ1' Φ2 Φ2' Φ3 Φ3' : Memory → Prop}
    {m0 mf : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hb3 : IsBlock P3 b3 n3 Φ3) (hb3' : IsBlock P3' b3 n3 Φ3')
    (h0 : m0 ⊨ P1 ∗ (P2 ∗ (P3 ∗ R)))
    (hf : Frame m0 mf [(b1, n1), (b2, n2), (b3, n3)])
    (hΦ1' : Φ1' mf) (hΦ2' : Φ2' mf) (hΦ3' : Φ3' mf) :
    mf ⊨ P1' ∗ (P2' ∗ (P3' ∗ R)) := by
  let m_mid : Memory := Memory.splice m0 mf b3 n3
  have hag3 : AgreesOutside m0 m_mid b3 n3 := hf.splice_agreesOutside_left
  have hf12 : Frame m_mid mf [(b1, n1), (b2, n2)] := hf.splice_frame_three
  have h0_3 : m0 ⊨ P3 ∗ (P1 ∗ (P2 ∗ R)) := by ac_nf at h0 ⊢
  have hmid_3 : m_mid ⊨ P3' ∗ (P1 ∗ (P2 ∗ R)) :=
    hb3.update hb3' (Nat.le_refl _) h0_3 hag3
      (hb3'.congr mf m_mid (fun a ha => by simp [m_mid, ha]) hΦ3')
  have hmid : m_mid ⊨ P1 ∗ (P2 ∗ (P3' ∗ R)) := by ac_nf at hmid_3 ⊢
  exact Frame.update_two_blocks hb1 hb1' hb2 hb2' hmid hf12 hΦ1' hΦ2'

/-! ## Relocatable `[LibsignalPlacement]` Helpers for HKDF -/

abbrev lsMemsetSym : String := "memset"
abbrev lsMemcpySym : String := "memcpy"
abbrev lsCompress256Sym : String := "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"

/-- Minimal hook-table hypothesis for HKDF on a placed `H : LibsignalHooks`
(`memset`, `memcpy`, and `_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256`). -/
class HkdfPlacedHooks (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : H lsMemsetSym = some memsetHook
  memcpy : H lsMemcpySym = some memcpyHook
  compress256 : H lsCompress256Sym = some (compress256Hook F)

theorem ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem s2_compress256_step_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H] [hH : HkdfPlacedHooks C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.compress256]
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memset_step_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H] [hH : HkdfPlacedHooks C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : ℕ}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes dst (List.replicate len 0#8))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst (List.replicate len 0#8).length = true := by
    rw [List.length_replicate]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memsetHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.memset]
  have hstate := memsetHook_eq hx0 hx1 hx2 hlr
  have hkeep : s.mem.KeepsFrozen (memsetHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memsetHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_memcpy_step_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H] [hH : HkdfPlacedHooks C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memcpyHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.memcpy]
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

namespace RunsTo

theorem trans_keepsFrozen {prog : Program} {s : State} {P_mid Q : State → Prop}
    (h1 : RunsTo prog s P_mid)
    (h2 : ∀ s₁, P_mid s₁ → s.mem.KeepsFrozen s₁.mem → RunsTo prog s₁ Q) :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hQ, hL2⟩ := h2 s₁ hP hst1.keepsFrozen hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hQ, hL2⟩

/-- Transfer a `RunsTo` execution from block `j` (`calleeProg`) to block `i` (`callerProg`)
    when `LibsignalCodeLoaded lsmpl s.mem` holds at entry `s`. -/
theorem of_other_block [LibsignalPlacement] {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee : IsLsBlockProg calleeProg j H]
    {s : State} {P_post : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : RunsTo calleeProg s P_post)
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsTo callerProg s P_post := by
  intro hL_caller
  have hL_callee : calleeProg.CodeLoaded s.mem :=
    hcallee.eq_blockProgram ▸ hcl j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h hL_callee
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller : Steps callerProg s s' := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

end RunsTo

/-- Synthetic base `b` for Block `123` (`finalize_fixed`) so `FinPre finPlacedFakeB` and
all cut predicates `StateF0p`..`StateF5` align with `(blkPl_123).base + k#64`. -/
abbrev finPlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  (blkPl_123).base - bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")

/-- Synthetic base `b` for Block `54` (`extract`) so cut predicates align with `(blkPl_54).base + k#64`. -/
abbrev extPlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  (blkPl_54).base - bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")

/-- Synthetic base `b` for Block `53` (`expand_multi_info`) so cut predicates align with `(blkPl_53).base + k#64`. -/
abbrev expPlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  (blkPl_53).base - bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")

@[simp, arm64_norm]
theorem finPlacedFakeB_off_0 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") =
      (blkPl_123).base :=
  BitVec.sub_add_cancel _ _

@[simp, arm64_norm]
theorem finPlacedFakeB_off_28 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 28) =
      (blkPl_123).base + 28#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_76 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 76) =
      (blkPl_123).base + 76#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_176 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 176) =
      (blkPl_123).base + 176#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_180 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 180) =
      (blkPl_123).base + 180#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_304 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 304) =
      (blkPl_123).base + 304#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_308 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 308) =
      (blkPl_123).base + 308#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem finPlacedFakeB_off_420 [LibsignalPlacement] :
    finPlacedFakeB + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 420) =
      (blkPl_123).base + 420#64 := by
  dsimp only [finPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem extPlacedFakeB_off_0 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") =
      (blkPl_54).base :=
  BitVec.sub_add_cancel _ _

@[simp, arm64_norm]
theorem extPlacedFakeB_off_80 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) =
      (blkPl_54).base + 80#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem extPlacedFakeB_off_192 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 192) =
      (blkPl_54).base + 192#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem extPlacedFakeB_off_328 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 328) =
      (blkPl_54).base + 328#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem extPlacedFakeB_off_380 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) =
      (blkPl_54).base + 380#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem extPlacedFakeB_off_396 [LibsignalPlacement] :
    extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) =
      (blkPl_54).base + 396#64 := by
  dsimp only [extPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_0 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") =
      (blkPl_53).base :=
  BitVec.sub_add_cancel _ _

@[simp, arm64_norm]
theorem expPlacedFakeB_off_32 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 32) =
      (blkPl_53).base + 32#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_192 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 192) =
      (blkPl_53).base + 192#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_448 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 448) =
      (blkPl_53).base + 448#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_500 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 500) =
      (blkPl_53).base + 500#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_516 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 516) =
      (blkPl_53).base + 516#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_604 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 604) =
      (blkPl_53).base + 604#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_672 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 672) =
      (blkPl_53).base + 672#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_688 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688) =
      (blkPl_53).base + 688#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_712 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 712) =
      (blkPl_53).base + 712#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_816 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 816) =
      (blkPl_53).base + 816#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_1124 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1124) =
      (blkPl_53).base + 1124#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_1176 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1176) =
      (blkPl_53).base + 1176#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

namespace FinalizeFixedProof

/-- Packaged relocatable `RunsTo` contract of `finalize_fixed` on a placed program `prog`. -/
def FinalizeFixedPlacedRunsTo [LibsignalPlacement] (prog : Program) (C : Crypto) : Prop :=
  ∀ {key msg : List (BitVec 8)} {s0 : State},
    FinPre finPlacedFakeB C.F key msg s0 →
    RunsTo prog s0 (FinPost C.F key msg s0)

end FinalizeFixedProof

end CryptoVerification.LibsignalTripleRatchet
