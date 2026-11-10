/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Proofs.AesCbc.LibsignalAesCbcProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.WPFrozen

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalSession.CryptoHmacSha256

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC
open ProofLib.ProgramReflection
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalSessionRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Relational Symbolic Execution (`RunsTo`) -/

/-- Preservation of SIMD callee-saved registers `d8..d15` (`v8..v15` lower 64 bits). -/
def VCalleeSaved (s₀ s : State) : Prop :=
  ∀ v : BitVec 5, 8 ≤ v.toNat → s.readVReg64 v = s₀.readVReg64 v

theorem VCalleeSaved.refl (s : State) : VCalleeSaved s s :=
  fun _ _ => rfl

theorem VCalleeSaved.trans {s₁ s₂ s₃ : State}
    (h₁ : VCalleeSaved s₁ s₂) (h₂ : VCalleeSaved s₂ s₃) : VCalleeSaved s₁ s₃ :=
  fun v hv => (h₂ v hv).trans (h₁ v hv)

theorem VCalleeSaved_advancePC_step {s₀ s : State} (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ s.advancePC := h

theorem VCalleeSaved_setMem_step {s₀ s : State} {m : Memory} (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.setMem m) := h

theorem VCalleeSaved_setPC_step {s₀ s : State} {pc : BitVec 64} (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.setPC pc) := h

theorem VCalleeSaved_setPState_step {s₀ s : State} {f : PState} (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.setPState f) := h

theorem VCalleeSaved_writeReg64_step {s₀ s : State} {r : Reg} {val : BitVec 64}
    (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.writeReg64 r val) := h

theorem VCalleeSaved_writeReg32_step {s₀ s : State} {r : Reg} {val : BitVec 32}
    (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.writeReg32 r val) := h

theorem VCalleeSaved_writeVReg128_step {s₀ s : State} {k : BitVec 5} {val : BitVec 128}
    (hk : k.toNat < 8) (h : VCalleeSaved s₀ s) :
    VCalleeSaved s₀ (s.writeVReg128 k val) := by
  intro v hv
  have hne : v ≠ k := by intro heq; subst heq; omega
  simpa [State.readVReg64, hne] using h v hv

theorem trace_advancePC_step {s₀ s : State} (h : s.trace = s₀.trace) :
    s.advancePC.trace = s₀.trace := h

theorem trace_setMem_step {s₀ s : State} {m : Memory} (h : s.trace = s₀.trace) :
    (s.setMem m).trace = s₀.trace := h

theorem trace_setPC_step {s₀ s : State} {pc : BitVec 64} (h : s.trace = s₀.trace) :
    (s.setPC pc).trace = s₀.trace := h

theorem trace_setPState_step {s₀ s : State} {f : PState} (h : s.trace = s₀.trace) :
    (s.setPState f).trace = s₀.trace := h

theorem trace_writeReg64_step {s₀ s : State} {r : Reg} {val : BitVec 64}
    (h : s.trace = s₀.trace) :
    (s.writeReg64 r val).trace = s₀.trace := h

theorem trace_writeReg32_step {s₀ s : State} {r : Reg} {val : BitVec 32}
    (h : s.trace = s₀.trace) :
    (s.writeReg32 r val).trace = s₀.trace := h

theorem trace_writeVReg128_step {s₀ s : State} {k : BitVec 5} {val : BitVec 128}
    (h : s.trace = s₀.trace) :
    (s.writeVReg128 k val).trace = s₀.trace := h

def TraceEq (s₀ s : State) : Prop :=
  s.trace = s₀.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s₀

theorem TraceEq.refl (s : State) : TraceEq s s := ⟨rfl, rfl⟩

theorem TraceEq.advancePC_step {s₀ s : State} (h : TraceEq s₀ s) :
    TraceEq s₀ s.advancePC := h

theorem TraceEq.setMem_step {s₀ s : State} {m : Memory} (h : TraceEq s₀ s) :
    TraceEq s₀ (s.setMem m) := h

theorem TraceEq.setPC_step {s₀ s : State} {pc : BitVec 64} (h : TraceEq s₀ s) :
    TraceEq s₀ (s.setPC pc) := h

theorem TraceEq.setPState_step {s₀ s : State} {f : PState} (h : TraceEq s₀ s) :
    TraceEq s₀ (s.setPState f) := h

theorem TraceEq.writeReg64_step {s₀ s : State} {r : Reg} {val : BitVec 64}
    (h : TraceEq s₀ s) :
    TraceEq s₀ (s.writeReg64 r val) := h

theorem TraceEq.writeReg32_step {s₀ s : State} {r : Reg} {val : BitVec 32}
    (h : TraceEq s₀ s) :
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

/-- Symbolic execution from `s` in `prog` reaches some `s'` via `Steps`, preserving `trace`
relative to `s₀`, preserving `CodeLoaded`, and establishing `P s'`. -/
def RunsToFrom (prog : Program) (s₀ s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ s', Steps prog s s' ∧ s'.trace = s₀.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s₀ ∧
      P s' ∧ prog.CodeLoaded s'.mem

/-- Symbolic execution from `s` in `prog` reaches some `s'` via `Steps`, preserving `trace`
and `CodeLoaded`, and establishing `P s'`. -/
abbrev RunsTo (prog : Program) (s : State) (P : State → Prop) : Prop :=
  RunsToFrom prog s s P

namespace RunsTo

variable {prog : Program}

theorem refl {s₀ s : State} {P : State → Prop} (h : P s)
    (htr : TraceEq s₀ s := by
      repeat' (first
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | with_reducible exact TraceEq.refl _)) :
    RunsToFrom prog s₀ s P :=
  fun hL => ⟨s, .refl s, htr.1, htr.2, h, hL⟩

theorem mono {s : State} {P Q : State → Prop}
    (h : RunsTo prog s P) (himp : ∀ s', P s' → Q s') :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s', hst, htr, hvregs, hP, hL'⟩ := h hL
  exact ⟨s', hst, htr, hvregs, himp s' hP, hL'⟩

theorem trans {s : State} {P Q : State → Prop}
    (h1 : RunsTo prog s P)
    (h2 : ∀ s₁, P s₁ → RunsTo prog s₁ Q) :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hvregs1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hvregs2, hQ, hL2⟩ := h2 s₁ hP hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hvregs2.trans hvregs1, hQ, hL2⟩

@[simp, arm64_norm]
theorem lsProg_svc [LibsignalPlacement] {prog : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H] : prog.svc = Syscall.standard := by
  rw [hprog.eq_blockProgram]; rfl

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
  obtain ⟨s', hst, htr, hvregs, hP, hL''⟩ := h hL'
  exact ⟨s', .step hstep hst, htr, hvregs, hP, hL''⟩

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
  obtain ⟨s', hst, htr, hvregs, hP, hL''⟩ := h hL'
  exact ⟨s', .step hstep hst, htr, hvregs, hP, hL''⟩

/-- Convert `RunsTo` into `reaches_pc` (providing `KeepsFrozen`, `symtab`, `trace`, and `calleeSavedVRegs`). -/
theorem to_reaches_pc {target : BitVec 64} {s0 : State} {P Q : State → Prop}
    {oom : State → Prop}
    (h : RunsTo prog s0 P)
    (hpost : ∀ sf, P sf → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      sf.trace = s0.trace → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.pc = target ∧ sf.status = .Running ∧ Q sf) :
    reaches_pc prog target s0 Q oom := by
  intro hL
  obtain ⟨sf, hsteps, htr, hvregs, hP, _⟩ := h hL
  obtain ⟨hpc, hrun, hQ⟩ := hpost sf hP hsteps.keepsFrozen hsteps.symtab_eq htr hvregs
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hQ⟩⟩

end RunsTo

/-! ## Rebased Program and Extern Hook Lookups -/

noncomputable abbrev P (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

theorem sessionProg_eq_P {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (F : ShaState → List (BitVec 8) → ShaState) (alloc : String → Option (State → State)) :
    sessionProg img F alloc = P img.base F alloc :=
  libsignalSessionCode_ofImage himg

theorem hookMemcpy_eq_memcpyHook :
    ProofLib.hookMemcpy = memcpyHook := rfl

theorem truncate8_truncate32 (x : BitVec 64) :
    (x.truncate 32).truncate 8 = x.truncate 8 := by bv_kernel

theorem hookMemset_eq_memsetHook :
    ProofLib.hookMemset = memsetHook := by
  funext s
  simp only [ProofLib.hookMemset, memsetHook, ProofLib.retHook,
    returnToLinkRegister, State.readReg32, State.readReg64, truncate8_truncate32]
  rfl

/-- `memset` stub at `b + 0x47f28#64` (`294696`). -/
@[scoped simp, arm64_norm]
theorem P_externAt_272972 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) :
    (P b F alloc).externAt? (b + bv% (ls_off% "memset")) = some memsetHook := by
  rw [show (bv% (ls_off% "memset") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memset")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memset")), (ls_hook% "memset")]
  simp [Rust.withPanics, Rust.isPanicSymbol, sessionExterns, hookMemset_eq_memsetHook]

/-- `memcpy` stub at `b + 0x47f50#64` (`294736`). -/
@[scoped simp, arm64_norm]
theorem P_externAt_273012 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) :
    (P b F alloc).externAt? (b + bv% (ls_off% "memcpy")) = some memcpyHook := by
  rw [show (bv% (ls_off% "memcpy") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "memcpy")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "memcpy")), (ls_hook% "memcpy")]
  simp [Rust.withPanics, Rust.isPanicSymbol, sessionExterns, hookMemcpy_eq_memcpyHook]

/-- `sha2::sha256::compress256` stub at `b + 0x48018#64` (`294936`). -/
@[scoped simp, arm64_norm]
theorem P_externAt_273212 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) :
    (P b F alloc).externAt? (b + bv% (ls_off% "sha2::sha256::compress256")) = some (compress256Hook F) := by
  rw [show (bv% (ls_off% "sha2::sha256::compress256") : BitVec 64) = BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256")) from rfl,
    Program.externAt?_rebase_add (num% (ls_off% "sha2::sha256::compress256")), (ls_hook% "sha2::sha256::compress256")]
  simp [Rust.withPanics, Rust.isPanicSymbol, sessionExterns]

/-! ## Extern Hook Step Lemmas -/

theorem read32_of_readBytes_toLEBytes (m : Memory) (a : BitVec 64) (w : BitVec 32)
    (h : m.readBytes a 4 = toLEBytes 4 w) :
    m.read32 a = w := by
  have h4 : m.readBytes a 4 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]
    rfl
  rw [h4, toLEBytes_4_eq_list] at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  dsimp only [Memory.read32]
  simp only [BitVec.add_zero, h0, h1, h2, h3]
  bv_kernel

@[scoped simp]
theorem shaStateBytes_length (st : ShaState) :
    (shaStateBytes st).length = 32 := by
  rcases st with ⟨l, hl⟩
  simp [shaStateBytes, List.length_flatMap, toLEBytes, hl]

theorem readShaState_of_readBytes_shaStateBytes (m : Memory) (addr : BitVec 64) (st : ShaState)
    (h : m.readBytes addr 32 = shaStateBytes st) :
    readShaState m addr = st := by
  apply List.Vector.eq
  have hl : st.toList.length = 8 := st.2
  unfold shaStateBytes at h
  generalize st.toList = l at hl h ⊢
  rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  let bs := ([w0, w1, w2, w3, w4, w5, w6, w7] : List (BitVec 32)).flatMap (toLEBytes 4)
  have hbs_len : bs.length = 32 := rfl
  have hslice := fun (i : ℕ) (hi : 4 * i + 4 ≤ 32) =>
    readBytes_slice_of_readBytes_eq m addr bs (by rw [hbs_len]; exact h) (4 * i) 4 hi
  have hw0 : m.read32 (addr + BitVec.ofNat 64 (4 * 0)) = w0 :=
    read32_of_readBytes_toLEBytes m _ w0 (by simpa [bs, toLEBytes] using hslice 0 (by decide))
  have hw1 : m.read32 (addr + BitVec.ofNat 64 (4 * 1)) = w1 :=
    read32_of_readBytes_toLEBytes m _ w1 (by simpa [bs, toLEBytes] using hslice 1 (by decide))
  have hw2 : m.read32 (addr + BitVec.ofNat 64 (4 * 2)) = w2 :=
    read32_of_readBytes_toLEBytes m _ w2 (by simpa [bs, toLEBytes] using hslice 2 (by decide))
  have hw3 : m.read32 (addr + BitVec.ofNat 64 (4 * 3)) = w3 :=
    read32_of_readBytes_toLEBytes m _ w3 (by simpa [bs, toLEBytes] using hslice 3 (by decide))
  have hw4 : m.read32 (addr + BitVec.ofNat 64 (4 * 4)) = w4 :=
    read32_of_readBytes_toLEBytes m _ w4 (by simpa [bs, toLEBytes] using hslice 4 (by decide))
  have hw5 : m.read32 (addr + BitVec.ofNat 64 (4 * 5)) = w5 :=
    read32_of_readBytes_toLEBytes m _ w5 (by simpa [bs, toLEBytes] using hslice 5 (by decide))
  have hw6 : m.read32 (addr + BitVec.ofNat 64 (4 * 6)) = w6 :=
    read32_of_readBytes_toLEBytes m _ w6 (by simpa [bs, toLEBytes] using hslice 6 (by decide))
  have hw7 : m.read32 (addr + BitVec.ofNat 64 (4 * 7)) = w7 :=
    read32_of_readBytes_toLEBytes m _ w7 (by simpa [bs, toLEBytes] using hslice 7 (by decide))
  rw [readShaState, List.Vector.toList_ofFn]
  dsimp only [List.ofFn, Fin.foldr, Fin.foldr.loop, Fin.val_zero, Fin.val_succ]
  rw [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]

private theorem chunks64_single_of_len_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    chunks64 bs = [bs] := by
  simp [chunks64, h]

theorem compress256Hook_one_eq (F : ShaState → List (BitVec 8) → ShaState) {s : State}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st)
    (hblk : m₀.readBytes blkPtr 64 = blk) :
    compress256Hook F s =
      (s.setMem (m₀.writeBytes stPtr (shaStateBytes (F st blk)))).setPC lr := by
  have hblk_len : blk.length = 64 := by
    rw [← hblk, Memory.readBytes_length]
  dsimp only [compress256Hook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (shaStateBytes ((chunks64 (s.mem.readBytes (s.readReg64 .x1)
        (64 * (s.readReg64 .x2).toNat))).foldl F
        (readShaState s.mem (s.readReg64 .x0)))))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hmem]
  have hmul : 64 * (1#64 : BitVec 64).toNat = 64 := rfl
  rw [hmul, hblk, chunks64_single_of_len_64 hblk_len, List.foldl_cons, List.foldl_nil,
      readShaState_of_readBytes_shaStateBytes m₀ stPtr st hst]

theorem memcpyHook_sess_eq {s : State} {m₀ : Memory} {dst src lr : BitVec 64} {n : ℕ}
    {bs : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hread : m₀.readBytes src n = bs) :
    memcpyHook s = (s.setMem (m₀.writeBytes dst bs)).setPC lr := by
  dsimp only [memcpyHook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hmem, hread]

theorem memsetHook_sess_eq {s : State} {m₀ : Memory} {dst lr : BitVec 64} {val : BitVec 8}
    {n : ℕ}
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀) :
    memsetHook s = (s.setMem (m₀.writeBytes dst (List.replicate n val))).setPC lr := by
  dsimp only [memsetHook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (List.replicate (s.readReg64 .x2).toNat ((s.readReg64 .x1).truncate 8)))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hmem]

namespace RunsTo

theorem sess_memcpy_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memcpy"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hread : m₀.readBytes src len = bs)
    (hrw : m₀.RW dst len)
    (h : RunsToFrom (P b F alloc) s₀ ((s.setMem (m₀.writeBytes dst bs)).setPC lr) P_post) :
    RunsToFrom (P b F alloc) s₀ s P_post := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hmem, hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (P b F alloc).externAt? s.pc = some memcpyHook := by
    rw [hpc]; exact P_externAt_273012 b F alloc
  have hstate := memcpyHook_sess_eq hx0 hx1 hx2 hlr hmem hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes bs hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem sess_memset_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst lr : BitVec 64} {val : BitVec 8} {len : ℕ}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "memset"))
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hrw : m₀.RW dst len)
    (h : RunsToFrom (P b F alloc) s₀
      ((s.setMem (m₀.writeBytes dst (List.replicate len val))).setPC lr) P_post) :
    RunsToFrom (P b F alloc) s₀ s P_post := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst (List.replicate len val).length = true := by
    rw [hmem, List.length_replicate]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : (P b F alloc).externAt? s.pc = some memsetHook := by
    rw [hpc]; exact P_externAt_272972 b F alloc
  have hstate := memsetHook_sess_eq hx0 hx1 hx2 hlr hmem
  have hkeep : s.mem.KeepsFrozen (memsetHook s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memsetHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem sess_compress256_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st)
    (hblk : m₀.readBytes blkPtr 64 = blk)
    (hrw : m₀.RW stPtr 32)
    (h : RunsToFrom (P b F alloc) s₀
      ((s.setMem (m₀.writeBytes stPtr (shaStateBytes (F st blk)))).setPC lr) P_post) :
    RunsToFrom (P b F alloc) s₀ s P_post := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (F st blk)).length = true := by
    rw [hmem, shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (P b F alloc).externAt? s.pc = some (compress256Hook F) := by
    rw [hpc]; exact P_externAt_273212 b F alloc
  have hstate := compress256Hook_one_eq F hx0 hx1 hx2 hlr hmem hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook F s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

end RunsTo

/-! ## `sess_step` Tactic -/

macro "sess_step" : tactic =>
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

/-! ## Memory Frames and Callee-Saved Registers -/

theorem AgreesOutside.writeBytes_self (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    AgreesOutside m (m.writeBytes a bs) a bs.length :=
  ProofLib.agreesOutside_writeBytes m a bs

/-- `m'` agrees with `m` (bytes and permissions) outside the regions `rs`. -/
def Frame (m m' : Memory) (rs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a : BitVec 64, (∀ r ∈ rs, OutsideRegion r.1 r.2 a) → m'.read8 a = m.read8 a) ∧
    m'.perm = m.perm ∧
    (∀ a : BitVec 64, (∀ r ∈ rs, OutsideRegion r.1 r.2 a) → m'.isLazyFree a = m.isLazyFree a) ∧
    (∀ a : BitVec 64, m.isLazyFree a = false → m'.isLazyFree a = false) ∧
    (∀ a : BitVec 64, m.isAnon a = true → m'.isAnon a = true)

/-- The callee-saved registers `x19`–`x30` and `sp` are the same in `s` and `s'`. -/
def CalleeSaved (s s' : State) : Prop :=
  s'.sp = s.sp ∧
    ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .lr],
      s'.readReg64 r = s.readReg64 r

def RW (m : Memory) (a : BitVec 64) (n : ℕ) : Prop := Memory.RW m a n

theorem Frame.refl (m : Memory) (rs : List (BitVec 64 × ℕ)) : Frame m m rs :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h⟩

theorem Frame.trans {m₁ m₂ m₃ : Memory} {rs : List (BitVec 64 × ℕ)}
    (h₁₂ : Frame m₁ m₂ rs) (h₂₃ : Frame m₂ m₃ rs) : Frame m₁ m₃ rs :=
  ⟨fun a ha => (h₂₃.1 a ha).trans (h₁₂.1 a ha),
   h₂₃.2.1.trans h₁₂.2.1,
   fun a ha => (h₂₃.2.2.1 a ha).trans (h₁₂.2.2.1 a ha),
   fun a ha => h₂₃.2.2.2.1 a (h₁₂.2.2.2.1 a ha),
   fun a ha => h₂₃.2.2.2.2 a (h₁₂.2.2.2.2 a ha)⟩

theorem Frame.mono {m₁ m₂ : Memory} {rs₁ rs₂ : List (BitVec 64 × ℕ)}
    (h : Frame m₁ m₂ rs₁)
    (hsub : ∀ a, (∀ r ∈ rs₂, OutsideRegion r.1 r.2 a) → (∀ r ∈ rs₁, OutsideRegion r.1 r.2 a)) :
    Frame m₁ m₂ rs₂ :=
  ⟨fun a ha => h.1 a (hsub a ha),
   h.2.1,
   fun a ha => h.2.2.1 a (hsub a ha),
   h.2.2.2.1,
   h.2.2.2.2⟩

theorem AgreesOutside.mono_sub {m₁ m₂ : Memory} {b b' : BitVec 64} {n n' : ℕ}
    (hag : AgreesOutside m₁ m₂ b' n') (hsub : (b' - b).toNat + n' ≤ n) :
    AgreesOutside m₁ m₂ b n := by
  have hout (a : BitVec 64) (ha : OutsideRegion b n a) : OutsideRegion b' n' a := by
    clear * - ha hsub; unfold OutsideRegion at ha ⊢; bv_omega
  exact ⟨fun a ha => hag.1 a (hout a ha), hag.2.1,
    fun a ha => hag.2.2.1 a (hout a ha), hag.2.2.2.1,
    hag.2.2.2.2⟩

theorem Frame.trans_agreesOutside {m₀ m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    {b : BitVec 64} {n : ℕ}
    (hf : Frame m₀ m₁ rs) (hag : AgreesOutside m₁ m₂ b n) :
    Frame m₀ m₂ ((b, n) :: rs) := by
  have h1 (a : BitVec 64) (ha : ∀ r ∈ (b, n) :: rs, OutsideRegion r.1 r.2 a) :
      OutsideRegion b n a := ha (b, n) (by simp)
  have h2 (a : BitVec 64) (ha : ∀ r ∈ (b, n) :: rs, OutsideRegion r.1 r.2 a) :
      ∀ r ∈ rs, OutsideRegion r.1 r.2 a := fun r hr => ha r (List.mem_cons_of_mem _ hr)
  exact ⟨fun a ha => (hag.1 a (h1 a ha)).trans (hf.1 a (h2 a ha)),
    hag.2.1.trans hf.2.1,
    fun a ha => (hag.2.2.1 a (h1 a ha)).trans (hf.2.2.1 a (h2 a ha)),
    fun a ha => hag.2.2.2.1 a (hf.2.2.2.1 a ha),
    fun a ha => hag.2.2.2.2 a (hf.2.2.2.2 a ha)⟩

theorem Frame.trans_agreesOutside_sub {m₀ m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    {b b' : BitVec 64} {n n' : ℕ}
    (hf : Frame m₀ m₁ rs) (hmem : (b, n) ∈ rs)
    (hsub : (b' - b).toNat + n' ≤ n) (hag : AgreesOutside m₁ m₂ b' n') :
    Frame m₀ m₂ rs := by
  refine (hf.trans_agreesOutside (AgreesOutside.mono_sub hag hsub)).mono (fun a ha r hr => ?_)
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact ha (b, n) hmem
  · exact ha r hr'

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
  rw [readBytes_getElem _ _ _ i h1, readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (fun r hr => (hd r hr).outside hin hlen)

theorem Frame.read64_eq {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) {addr : BitVec 64}
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := hf.readBytes_eq hd (by decide)
  rw [readBytes_8_eq, readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

structure MprImpl (Q P : Prop) : Prop where
  mpr : P → Q

theorem Frame.readable_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (m₂.Readable addr len) (m₁.Readable addr len) :=
  ⟨Memory.Readable.of_perm_eq hf.2.1 hf.2.2.2.1⟩

theorem Frame.rw_iff {m₁ m₂ : Memory} {rs : List (BitVec 64 × ℕ)}
    (hf : Frame m₁ m₂ rs) (addr : BitVec 64) (len : ℕ) :
    MprImpl (RW m₂ addr len) (RW m₁ addr len) :=
  ⟨Memory.RW.of_perm_eq hf.2.1 hf.2.2.2.1⟩

theorem write64_zero_pair_eq_writeBytes (m : Memory) (a : BitVec 64) :
    (m.write64 a 0#64).write64 (a + 8#64) 0#64 = m.writeBytes a (List.replicate 16 0#8) := by
  rw [write64_eq_writeBytes, write64_eq_writeBytes]
  have happ := (writeBytes_append m a (toLEBytes 8 0#64) (toLEBytes 8 0#64)).symm
  rw [toLEBytes_length] at happ
  rw [happ]
  rfl

/-! ## `Hmac<Sha256>` Memory Layout and Short-Message Equation -/

/-- The 64-byte HMAC key block `k₀ = key ‖ 0…0` (for `|key| ≤ 64`). -/
def keyBlock (key : List (BitVec 8)) : List (BitVec 8) :=
  key ++ List.replicate (64 - key.length) 0

/-- Inner / outer state after the key block: `F IV (k₀ ⊕ 0x36…)` / `F IV (k₀ ⊕ 0x5c…)`. -/
def innerState (F : ShaState → List (BitVec 8) → ShaState) (key : List (BitVec 8)) : ShaState :=
  F sha256IV ((keyBlock key).map (· ^^^ 0x36))

def outerState (F : ShaState → List (BitVec 8) → ShaState) (key : List (BitVec 8)) : ShaState :=
  F sha256IV ((keyBlock key).map (· ^^^ 0x5c))

/-- `Hmac<Sha256>` (`0x90` B) memory representation at `a` after absorbing `msg` (`msg.length < 64`)
under `key`. -/
def HmacSt (m : Memory) (a : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : Prop :=
  msg.length < 64 ∧
  m.readBytes a msg.length = msg ∧
  m.read8 (a + 0x3f#64) = BitVec.ofNat 8 msg.length ∧
  m.readBytes (a + 0x40#64) 32 = shaStateBytes (innerState F key) ∧
  m.read64 (a + 0x60#64) = 1#64 ∧
  m.readBytes (a + 0x68#64) 32 = shaStateBytes (outerState F key) ∧
  m.read64 (a + 0x88#64) = 1#64

/-- The last (only) message block of the inner hash for `|msg| < 56` after the key block:
`msg ‖ 0x80 ‖ 0… ‖ BE64(8·(64 + |msg|))`, 64 bytes. -/
def innerLastBlock (msg : List (BitVec 8)) : List (BitVec 8) :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + msg.length)))

/-- The digest bytes of a state: each word big-endian (`sha256With`'s output). -/
def digestBytes (h : ShaState) : List (BitVec 8) :=
  h.toList.flatMap (toBEBytes 4)

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

@[scoped simp] theorem digestBytes_length (h : ShaState) :
    (digestBytes h).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [digestBytes, List.length_flatMap, hl]

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

/-- Short-message (`key.length ≤ 64`, `msg.length < 56`) two-compression expansion of `hmacWith`. -/
theorem hmacWith_short (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8))
    (hk : key.length ≤ 64) (hm : msg.length < 56) :
    hmacWith F key msg =
      digestBytes (F (outerState F key)
        (outerBlock (digestBytes (F (innerState F key) (innerLastBlock msg))))) := by
  unfold hmacWith
  have hk_not_gt : ¬ (64 < key.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  change sha256With F ((keyBlock key).map (· ^^^ 0x5c) ++
    sha256With F ((keyBlock key).map (· ^^^ 0x36) ++ msg)) = _
  have hkb_len : (keyBlock key).length = 64 := by
    simp [keyBlock]; omega
  have hipad_len : ((keyBlock key).map (· ^^^ 0x36)).length = 64 := by
    simp [hkb_len]
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c)).length = 64 := by
    simp [hkb_len]
  have hinner_blk_len : (innerLastBlock msg).length = 64 := by
    simp [innerLastBlock]; omega
  have hinner_pad : sha256Pad ((keyBlock key).map (· ^^^ 0x36) ++ msg) =
      (keyBlock key).map (· ^^^ 0x36) ++ innerLastBlock msg := by
    unfold sha256Pad innerLastBlock
    have hlen : ((keyBlock key).map (· ^^^ 0x36) ++ msg).length = 64 + msg.length := by
      simp [hkb_len]
    have hmod : (119 - (64 + msg.length) % 64) % 64 = 55 - msg.length := by omega
    rw [hlen, hmod]
    simp only [List.append_assoc]
  have hinner : sha256With F ((keyBlock key).map (· ^^^ 0x36) ++ msg) =
      digestBytes (F (innerState F key) (innerLastBlock msg)) :=
    sha256With_two_blocks F _ _ _ hinner_pad hipad_len hinner_blk_len
  rw [hinner]
  set d := digestBytes (F (innerState F key) (innerLastBlock msg))
  have hd_len : d.length = 32 := digestBytes_length _
  have houter_blk_len : (outerBlock d).length = 64 := by
    simp [outerBlock, hd_len]
  have houter_pad : sha256Pad ((keyBlock key).map (· ^^^ 0x5c) ++ d) =
      (keyBlock key).map (· ^^^ 0x5c) ++ outerBlock d := by
    unfold sha256Pad outerBlock
    have hlen : ((keyBlock key).map (· ^^^ 0x5c) ++ d).length = 96 := by
      simp [hkb_len, hd_len]
    rw [hlen]
    simp only [List.append_assoc]
  exact sha256With_two_blocks F _ _ _ houter_pad hopad_len houter_blk_len

@[scoped simp] theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith
  exact sha256With_length F _

namespace Layout

theorem readBytes_writeBytes_eq (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (n : ℕ)
    (hn : bs.length = n) (hlen : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes a n = bs := by
  subst hn; exact ProofLib.readBytes_writeBytes_same m a bs hlen

theorem readBytes_writeBytes_of_disjoint (m : Memory) (a : BitVec 64) (bs : List (BitVec 8))
    (b : BitVec 64) (n : ℕ) (hd : DisjointRegions a bs.length b n) (hn : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes b n = m.readBytes b n :=
  (ProofLib.agreesOutside_writeBytes m a bs).readBytes_eq hd hn

end Layout

/-! ## Relocatable `[LibsignalPlacement]` Helpers (Blocks 92 and 114) -/

abbrev lsMemcpySym : String := "memcpy"
abbrev lsMemsetSym : String := "memset"
abbrev lsCompress256Sym : String := "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"
abbrev lsSha256IVSym : String := "libsignal_protocol:.rodata.cst32+0x100"
abbrev lsSha256IVAddr [LibsignalPlacement] : BitVec 64 := lsρ lsSha256IVSym

/-- Synthetic base `b` satisfying `b + bv% (ls_str% "kyber_pre_key_pu" + 256) = lsSha256IVAddr`,
reusing fixed-base `NfsMemInv` and `NfsRegInv` lemmas in `[LibsignalPlacement]` proofs. -/
abbrev nfsPlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  lsSha256IVAddr - bv% (ls_str% "kyber_pre_key_pu" + 256)

@[simp, arm64_norm]
theorem nfsPlacedFakeB_add_iv [LibsignalPlacement] :
    nfsPlacedFakeB + bv% (ls_str% "kyber_pre_key_pu" + 256) = lsSha256IVAddr :=
  BitVec.sub_add_cancel _ _

theorem ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

namespace RunsTo

theorem trans_keepsFrozen {prog : Program} {s : State} {P_mid Q : State → Prop}
    (h1 : RunsTo prog s P_mid)
    (h2 : ∀ s₁, P_mid s₁ → s.mem.KeepsFrozen s₁.mem → RunsTo prog s₁ Q) :
    RunsTo prog s Q := by
  intro hL
  obtain ⟨s₁, hst1, htr1, hvregs1, hP, hL1⟩ := h1 hL
  obtain ⟨s₂, hst2, htr2, hvregs2, hQ, hL2⟩ := h2 s₁ hP hst1.keepsFrozen hL1
  exact ⟨s₂, hst1.trans hst2, htr2.trans htr1, hvregs2.trans hvregs1, hQ, hL2⟩

/-- Transfer `RunsTo` from `calleeProg` (block `j`) to `callerProg` (block `i`) under `LibsignalCodeLoaded`. -/
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
  obtain ⟨s', hst_callee, htr, hvregs, hP, _⟩ := h hL_callee
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller : Steps callerProg s s' := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hvregs, hP, hst_caller.codeLoaded hL_caller⟩

/-- Relaxable `ADRP`+`ADD` pair step at `+0x28` of Block 114 loading `lsSha256IVAddr` into `x22`. -/
theorem pairStep_114_0x28 [LibsignalPlacement]
    {H : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    (hpc : s.pc = (blkPl_114).base + 40#64)
    (hrun : s.status = .Running)
    (hnext : RunsToFrom (lsProg_114 H) s₀
      ((s.writeReg64 (.gpr 22#5) lsSha256IVAddr).setPC ((blkPl_114).base + 48#64)) P_post) :
    RunsToFrom (lsProg_114 H) s₀ s P_post := by
  let s₁ := (s.writeReg64 (.gpr 22#5) lsSha256IVAddr).setPC ((blkPl_114).base + 48#64)
  have hwp : SepWP (lsProg_114 H) ((blkPl_114).base + 48#64) s emp (fun sf _ => sf = s₁) := by
    refine blkPC_114_pairStep_0x28 (blkPl_114).base H rfl hpc hrun ?_
    simpa [s₁, arm64_norm, lsSha256IVAddr, lsSha256IVSym] using
      (SepWP.done (prog := lsProg_114 H) (s := s₁) (P := emp) (post := fun sf _ => sf = s₁)
        rfl (by simpa [s₁, State.setPC, State.writeReg64] using hrun) rfl)
  intro hL
  have hreaches := SepWP.reaches_of_sepWP hwp (R := emp) (by simp) hL
  obtain ⟨sf, hst1, ⟨_, _, rfl⟩ | ⟨_, hoom⟩⟩ := hreaches
  · obtain ⟨s', hst2, htr, hvregs, hP, hL'⟩ := hnext hL
    exact ⟨s', hst1.trans hst2, htr, hvregs, hP, hL'⟩
  · exact hoom.elim

theorem placed_memcpy_step [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hread : m₀.readBytes src len = bs)
    (hrw : m₀.RW dst len)
    (h : RunsToFrom prog s₀ ((s.setMem (m₀.writeBytes dst bs)).setPC lr) P_post)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s P_post := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hmem, hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memcpyHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_memcpy]
  have hstate := memcpyHook_sess_eq hx0 hx1 hx2 hlr hmem hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes bs hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem placed_memset_step [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memset : H lsMemsetSym = some memsetHook)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst lr : BitVec 64} {val : BitVec 8} {len : ℕ}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hrw : m₀.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (m₀.writeBytes dst (List.replicate len val))).setPC lr) P_post)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s P_post := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst (List.replicate len val).length = true := by
    rw [hmem, List.length_replicate]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memsetHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_memset]
  have hstate := memsetHook_sess_eq hx0 hx1 hx2 hlr hmem
  have hkeep : s.mem.KeepsFrozen (memsetHook s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memsetHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem placed_compress256_step [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {F : ShaState → List (BitVec 8) → ShaState}
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st)
    (hblk : m₀.readBytes blkPtr 64 = blk)
    (hrw : m₀.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (m₀.writeBytes stPtr (shaStateBytes (F st blk)))).setPC lr) P_post)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s P_post := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (F st blk)).length = true := by
    rw [hmem, shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_compress]
  have hstate := compress256Hook_one_eq F hx0 hx1 hx2 hlr hmem hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook F s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

end RunsTo

end CryptoVerification.LibsignalSession.CryptoHmacSha256
