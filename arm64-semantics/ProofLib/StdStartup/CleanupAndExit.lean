/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm

/-!
# Post-Main `std::rt::cleanup` and `musl` `exit` Contracts

Symbolic `SepWP` contracts for `<futex::Once>::call`, post-`main` `std::rt::cleanup`,
`unique_thread_exit`, and `musl` `exit` through `_Exit`.
-/
set_option autoImplicit false
@[expose] public section
namespace ProofLib.StdStartup
open Arm64 ProofLib

/-! ## Parametric Instruction Constructors and Fixed-Word Slices -/
local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term => `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term => `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdrbLo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStrbLo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .B8 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))

def errnoLocationWords : List (BitVec 32) := [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]
def stdoutClosureWords : List (BitVec 32) := [0xf940000a#32, 0xa9402149#32, 0xf900015f#32, 0xb4000109#32, 0x6f00e400#32, 0x5280002a#32, 0x3900012a#32, 0xa9027d0a#32, 0x3900c11f#32, 0xad000100#32, 0xd65f03c0#32, 0xd4200020#32]
def stdoutDummyBytes : List (BitVec 8) := List.replicate 32 0#8 ++ unpack64 1#64 ++ List.replicate 16 0#8

def StdFieldsPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart
theorem StdFieldsPreserved.rfl (s : State) : StdFieldsPreserved s s := ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩
theorem StdFieldsPreserved.trans {s0 s1 s2 : State} (h01 : StdFieldsPreserved s0 s1) (h12 : StdFieldsPreserved s1 s2) : StdFieldsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1, h12.2.2.2.2.2.trans h01.2.2.2.2.2⟩
theorem StdStatePreserved.toFields {s0 sf : State} (h : StdStatePreserved s0 sf) : StdFieldsPreserved s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

@[local simp] private theorem stdFields_w64 (s0 s : State) (r : Reg) (v : BitVec 64) : StdFieldsPreserved s0 (s.writeReg64 r v) ↔ StdFieldsPreserved s0 s := by cases r <;> simp [State.writeReg64, StdFieldsPreserved]
@[local simp] private theorem stdFields_w32 (s0 s : State) (r : Reg) (v : BitVec 32) : StdFieldsPreserved s0 (s.writeReg32 r v) ↔ StdFieldsPreserved s0 s := by simp [State.writeReg32]
@[local simp] private theorem stdFields_wReg (s0 s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) : StdFieldsPreserved s0 (s.writeReg w r v) ↔ StdFieldsPreserved s0 s := by cases w <;> simp [State.writeReg]
@[local simp] private theorem stdFields_wV128 (s0 s : State) (vr : VReg) (v : BitVec 128) : StdFieldsPreserved s0 (s.writeVReg128 vr v) ↔ StdFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem stdFields_pstate (s0 s : State) (p : PState) : StdFieldsPreserved s0 (s.setPState p) ↔ StdFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem stdFields_advPC (s0 s : State) : StdFieldsPreserved s0 s.advancePC ↔ StdFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem stdFields_setPC (s0 s : State) (pc : BitVec 64) : StdFieldsPreserved s0 (s.setPC pc) ↔ StdFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem stdFields_setMem (s0 s : State) (m : Memory) : StdFieldsPreserved s0 (s.setMem m) ↔ StdFieldsPreserved s0 s := Iff.rfl
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
local macro "std_rfl" : term => `(by simp [StdFieldsPreserved.rfl])

theorem errnoLocation_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : P.hasWords L.errnoLocationAddr errnoLocationWords) (hpc : s.pc = L.errnoLocationAddr) (hrun : s.status = .Running) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf → sf.readReg64 .x0 = s.tpidrEl0 - 0xa4#64 → StdFieldsPreserved s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hcode' : P.hasCode L.errnoLocationAddr errnoLocationWords := hcode; wp_steps
  exact hnext _ (by simp (config := { decide := true }) only [arm64_norm]) (by simp only [arm64_norm, hrun]) rfl (by simp (config := { decide := true }) only [arm64_norm]) (by simp (config := { decide := true }) only [arm64_norm]) std_rfl

theorem stdoutClosure_wp {P : Program} {closureAddr target_pc ret_pc dataPtr pairPtr notInitPtr stdoutAddr : BitVec 64} {oldFlag : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : P.hasWords closureAddr stdoutClosureWords) (hpc : s.pc = closureAddr) (hrun : s.status = .Running) (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = dataPtr) (hflag_nz : notInitPtr ≠ 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf ((dataPtr ↦₆₄ pairPtr) ∗ (pairPtr ↦₆₄ 0#64) ∗ ((pairPtr + 8#64) ↦₆₄ stdoutAddr) ∗ (notInitPtr ↦₈ 1#8) ∗ (stdoutAddr ↦ₛ stdoutDummyBytes) ∗ F) post oom) :
    SepWP P target_pc s ((dataPtr ↦₆₄ pairPtr) ∗ (pairPtr ↦₆₄ notInitPtr) ∗ ((pairPtr + 8#64) ↦₆₄ stdoutAddr) ∗ (notInitPtr ↦₈ oldFlag) ∗ (stdoutAddr ↦ₛ List.replicate 56 0#8) ∗ F) post oom := by
  have hcode' : P.hasCode closureAddr stdoutClosureWords := hcode
  have hsplit (v : BitVec 64) (bs : List (BitVec 8)) (hbs : bs = unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 v ++ (unpack64 0#64 ++ ([0#8] ++ List.replicate 7 0#8))))))) :
      (stdoutAddr ↦ₛ bs) = (stdoutAddr ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x08#64) ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x10#64) ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x18#64) ↦₆₄ 0#64) ∗
        ((stdoutAddr + 0x20#64) ↦₆₄ v) ∗ ((stdoutAddr + 0x28#64) ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x30#64) ↦₈ 0#8) ∗ ((stdoutAddr + 0x31#64) ↦ₛ List.replicate 7 0#8) := by
    rw [hbs]; simp only [pointsToBytes_append, pointsToBytes_singleton, ← pointsTo64_eq_pointsToBytes, unpack64_length, List.length_cons, List.length_nil]
    simp (config := { decide := true }) only [BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd]
  rw [hsplit 0#64 _ (by decide)]; wp_steps
  exact SepWP.congr_pre (by rw [hsplit 1#64 _ (by decide)]) (hnext _ (by simp (config := { decide := true }) only [arm64_norm]) (by simp only [arm64_norm, hrun]) rfl (by simp (config := { decide := true }) only [arm64_norm]) std_rfl)

/-! ## Uncontended `INCOMPLETE` `<futex::Once>::call` and Uninitialized-`STDOUT` Cleanup -/

private theorem bv64_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_lin
local macro "norm_jmp" : tactic => `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
private theorem pointsTo8_combine32_sub (sp o0 o1 o2 o3 : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R = ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3; simpa only [sepConj_assoc, show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin, show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin, show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin] using congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)
private theorem pointsTo32_split8_sub (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32) (R : SepProp) (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R = ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗ ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [pointsTo8_combine32_sub sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3, show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by bv_bits]
private theorem stackAt_split (sp : BitVec 64) (a b : Nat) (h : a + b ≤ 2 ^ 64 := by decide) : stackAt sp (a + b) = stackAt (sp - BitVec.ofNat 64 a) b ∗ stackAt sp a := by
  rw [stackAt_split_bottom sp a b h]; unfold stackAt; rw [BitVec.sub_sub, BitVec.ofNat_add]
private theorem combine_cell_byte4_sat (sp o8 o4 o3 o2 o1 : BitVec 64) {lo : BitVec 32} {b0 b1 b2 b3 : BitVec 8} {m : Memory} {P R : SepProp} (hm : m ⊨ P)
    (hf : P = (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) ∗ R := by sep_focus)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl) (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) : m ⊨ (((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) ∗ R) := by
  rwa [hf, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, pointsTo8_combine32_sub sp o4 o3 o2 o1 b0 b1 b2 b3 R h1 h2 h3, pointsTo32_combine64_sub sp o8 o4 lo _ R h4] at hm
local macro "unpack_cells " k:num : tactic => `(tactic| (simp only [Nat.reduceMul]; cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate $k (apply SepWP.exists_left; intro _)))
local macro "repack_cells" : tactic => `(tactic| (simp only [Nat.reduceMul]; cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))
local macro "repack_cells_split " hm:ident "," sp:term "," o8:term "," o4:term "," o3:term "," o2:term "," o1:term : tactic => `(tactic| (replace $hm := combine_cell_byte4_sat $sp $o8 $o4 $o3 $o2 $o1 $hm; repack_cells))

inductive CodeChunk where
  | words   (addr : BitVec 64) (ws : List (BitVec 32))
  | instrs0 (base : BitVec 64) (is : List Instr)
  | instrs  (base : BitVec 64) (off : Nat) (is : List Instr)
def CodeChunk.holds (P : Program) : CodeChunk → Prop
  | .words a ws => P.hasWords a ws | .instrs0 b is => hasInstrs P b is | .instrs b o is => hasInstrs P (b + BitVec.ofNat 64 o) is
def CodeChunks (P : Program) : List CodeChunk → Prop
  | [] => True | [c] => c.holds P | c :: cs => c.holds P ∧ CodeChunks P cs
private def fetchAtAcc (P : Program) (base : BitVec 64) : Nat → List Instr → Prop → Prop
  | _, [], acc => acc | off, x :: xs, acc => P.fetch (base + BitVec.ofNat 64 off) = some x ∧ fetchAtAcc P base (off + 4) xs acc
private theorem fetchAtAcc_of_fn {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr), (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) → fetchAtAcc P base off is acc
  | _, [], _ => hacc | off, _ :: xs, h => ⟨by simpa using h 0 (Nat.zero_lt_succ _), fetchAtAcc_of_fn hacc (off + 4) xs fun i hi => by simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩
private def CodeChunk.stepAcc (P : Program) (acc : Prop) : CodeChunk → Prop
  | .words a ws => P.hasCode a ws ∧ acc | .instrs0 b is => fetchAtAcc P b 0 is acc | .instrs b o is => fetchAtAcc P b o is acc
private def CodeStepFacts (P : Program) : List CodeChunk → Prop
  | [] => True | c :: cs => c.stepAcc P (CodeStepFacts P cs)
private theorem CodeChunk.toStepAcc {P : Program} {acc : Prop} (hacc : acc) : ∀ {c : CodeChunk}, c.holds P → c.stepAcc P acc
  | .words _ _, h => ⟨h, hacc⟩ | .instrs0 _ _, h => fetchAtAcc_of_fn hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => fetchAtAcc_of_fn hacc o _ fun i hi => by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi
private theorem CodeChunks.toStepFacts {P : Program} : ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeStepFacts P cs
  | [], _ => trivial | [_], h => CodeChunk.toStepAcc trivial h | _ :: _ :: _, ⟨h1, h2⟩ => CodeChunk.toStepAcc (CodeChunks.toStepFacts h2) h1
local macro "unpack_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := CodeChunks.toStepFacts $h; simp only [$chunks:ident, CodeStepFacts, CodeChunk.stepAcc, fetchAtAcc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))
local macro "unpack_cs " h:ident : tactic => `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic => `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])

private theorem step_ldar32_words {prog : Program} {target_pc : BitVec 64} (addr : BitVec 64) (words : List (BitVec 32))
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : BitVec 32} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (i : Nat) (next_pc : BitVec 64) (halign : MemWidth.isAligned .W32 ea = true) (rt' : Reg := .gpr 8#5) (hw : prog.hasCode addr words := by with_reducible assumption)
    (hget : words[i]? = some w := by rfl) (hdec : decode w = some (.ldarStlr .W32 true rn rt) := by rfl)
    (hrt : rt = rt' := by decide) (hrn : rn ≠ .sp := by decide) (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin) (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (haddr : s.readReg64 rn = ea := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin) (hload : SepLoad32 ea P v := by wp_sep_access_fast)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt' (v.zeroExtend 64)).setPC next_pc) P post oom) : SepWP prog target_pc s P post oom := by
  subst hrt hpc_next; have hsp : checkRegSPAligned s rn = true := by cases rn <;> simp_all [checkRegSPAligned]
  apply SepWP.weaken_pre_frame (P' := ⌜s.mem.read32 ea = v ∧ s.mem.canRead ea 4 = true⌝ ∗ P)
  · intro R hm; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hload.load hm, hload.readable hm⟩, hm⟩
  · apply SepWP.pure_elim; rintro ⟨hread, hcan⟩
    refine SepWP.step_pure (s' := (s.writeReg64 rt (v.zeroExtend 64)).setPC (addr + BitVec.ofNat 64 (4 * (i + 1)))) hpc hrun (Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec) ?_ rfl hnext
    have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
    have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
    rw [hs_eq]; simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg, State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

def onceCallEntryWords : List (BitVec 32) :=
  [0xd101c3ff#32, 0xa9027bfd#32, 0xf9001bf9#32, 0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910083fd#32, 0x910023e8#32, 0x88dffc17#32, 0xaa0303f5#32, 0xaa0203f4#32, 0x2a0103f6#32, 0xaa0003f3#32,
   0x91002118#32, 0x14000002#32, 0x88dffe77#32, 0x120006f9#32, 0x121e02e8#32, 0x7100073f#32, 0x5400018d#32, 0x71000b3f#32, 0x54000041#32, 0x34000816#32, 0x32000101#32, 0x2a1703e0#32, 0xaa1303e2#32]
def onceCallChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.words L.onceCallAddr onceCallEntryWords, .instrs L.onceCallAddr 0x68 [iBl (L.onceCallAddr + 0x68#64) L.cas4AcqAddr], .words (L.onceCallAddr + 0x6c#64) [0x6b17001f#32, 0x54000440#32],
   .words (L.onceCallAddr + 0xf8#64) [0x71000b3f#32, 0xf94012a9#32, 0x910023e1#32, 0x1a9f17e8#32, 0xaa1403e0#32, 0xb9000bff#32, 0x390033e8#32, 0xd63f0120#32, 0xb9400be0#32, 0xaa1303e1#32],
   .instrs L.onceCallAddr 0x120 [iBl (L.onceCallAddr + 0x120#64) L.swp4RelAddr], .words (L.onceCallAddr + 0x124#64) [0x361000c0#32],
   .words (L.onceCallAddr + 0x13c#64) [0xa9464ff4#32, 0xf9401bf9#32, 0xa94557f6#32, 0xa9445ff8#32, 0xa9427bfd#32, 0x9101c3ff#32, 0xd65f03c0#32]]
def OnceCallCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (onceCallChunks L)

theorem onceCall_incomplete_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 onceAddr dataPtr vtableAddr shimAddr closureAddr : BitVec 64}
    {haveLse : BitVec 8} {s : State} {Pre Post F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : OnceCallCode P L) (hcas : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr)) (hswp : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.onceCallAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = onceAddr) (hx2 : s.readReg64 .x2 = dataPtr) (hx3 : s.readReg64 .x3 = vtableAddr) (halign : MemWidth.isAligned .W32 onceAddr = true)
    (hclosure : ∀ sc : State, ∀ G : SepProp, sc.pc = closureAddr → sc.status = .Running → sc.sp = sp0 - 0x70#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = L.onceCallAddr + 0x118#64 → sc.readReg64 .x0 = dataPtr → StdFieldsPreserved s sc →
      (∀ sr : State, sr.pc = L.onceCallAddr + 0x118#64 → sr.status = .Running → sr.sp = sc.sp → CalleeSavedPreserved sc sr → StdFieldsPreserved sc sr → SepWP P target_pc sr ((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Post ∗ G) post oom) →
      SepWP P target_pc sc ((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Pre ∗ G) post oom)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf ((onceAddr ↦₃₂ 0#32) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo vtableAddr shimAddr closureAddr ∗ stackAt sp0 112 ∗ Post ∗ F) post oom) :
    SepWP P target_pc s ((onceAddr ↦₃₂ 3#32) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo vtableAddr shimAddr closureAddr ∗ stackAt sp0 112 ∗ Pre ∗ F) post oom := by
  subst hsp; unpack_code onceCallChunks hc; unfold StdVtableRo; rw [stackAt_eq_cells s.sp 14]; unpack_cells 14
  rw [pointsTo64_split32_sub s.sp 104#64 100#64, pointsTo32_split8_sub s.sp 100#64 99#64 98#64 97#64]
  wp_steps; refine step_ldar32_words L.onceCallAddr onceCallEntryWords 8 (L.onceCallAddr + 36#64) halign (rt' := .gpr 23#5) (hnext := ?_); wp_steps; wp_steps
  refine call_stdCas4 hcas (haveLse := haveLse) (ptr := onceAddr) (v0 := 3#32) (exp := 3#32) (new := 1#32)
    (ret_pc := L.onceCallAddr + 0x6c#64) (F := ?_) (by sep_frame) (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (halign := halign)
  simp only [beq_self_eq_true, ↓reduceIte]
  have ⟨hx19_1, hx20_1, hx21_1, hx23_1, hx25_1⟩ : s1.readReg64 .x19 = onceAddr ∧ s1.readReg64 .x20 = dataPtr ∧ s1.readReg64 .x21 = vtableAddr ∧
      BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 ∧ BitVec.truncate 32 (s1.readReg64 (.gpr 25#5)) = 3#32 :=
    ⟨by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm], by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm], by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm],
     by have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this, by have := hcs1.readReg32_x25; simp [wp_norm, arm64_norm] at this; exact this⟩
  have hsp1_eq : s1.sp = s.sp - 0x70#64 := by rw [hsp1]; exact wp_a
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x70#64 hsp_align
  have hstd_s1 : StdFieldsPreserved s s1 := StdFieldsPreserved.trans std_rfl hstd1.toFields; wp_steps; wp_steps
  refine SepWP.weaken_pre (P' := (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ Pre ∗ ?G) (by sep_frame)
    (hclosure _ ?G wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1_eq]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      wp_a wp_a (StdFieldsPreserved.trans hstd_s1 std_rfl) fun s2 hpc2 hrun2 hsp2 hcs2 hstd2 => ?_)
  have hx19_2 : s2.readReg64 .x19 = onceAddr := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
  have hsp2_eq : s2.sp = s.sp - 0x70#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
  have hsp2_al : s2.spAligned = true := by simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 0x70#64 hsp_align
  wp_steps
  refine call_stdSwp4 hswp (haveLse := haveLse) (ptr := onceAddr) (v0 := 1#32) (new := 0#32) (ret_pc := L.onceCallAddr + 0x124#64) (F := ?_) (by sep_frame) (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_) (halign := halign)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_3
  have hsp3_eq : s3.sp = s.sp - 0x70#64 := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3_eq]; exact s.spAligned_sub 0x70#64 hsp_align
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame (fun _ hm => by unfold StdVtableRo; rw [stackAt_eq_cells s.sp 14]; repack_cells_split hm, s.sp, 104#64, 100#64, 99#64, 98#64, 97#64)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a (by unpack_cs hcs1; unpack_cs hcs2; unpack_cs hcs3; close_cs)
      (StdFieldsPreserved.trans hstd_s1 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd2 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd3.toFields std_rfl))))))

def stdoutInitEntryWords : List (BitVec 32) := [0x88dffd08#32, 0x35000048#32, 0xd65f03c0#32, 0xd10103ff#32, 0xa9037bfd#32, 0x9100c3fd#32]
def stdoutOnceLockChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.instrs0 L.stdoutOnceLockInitAddr [iAdrp .x8 L.stdoutOnceLockInitAddr (L.stdoutGlobalAddr + 0x38#64), iAddLo12 .x8 .x8 (L.stdoutGlobalAddr + 0x38#64)], .words (L.stdoutOnceLockInitAddr + 0x08#64) stdoutInitEntryWords,
   .instrs L.stdoutOnceLockInitAddr 0x20 [iAdrp .x8 (L.stdoutOnceLockInitAddr + 0x20#64) L.stdoutGlobalAddr, iAddLo12 .x8 .x8 L.stdoutGlobalAddr], .words (L.stdoutOnceLockInitAddr + 0x28#64) [0xd10007a9#32, 0xa900a3e0#32],
   .instrs L.stdoutOnceLockInitAddr 0x30 [iAdrp .x3 (L.stdoutOnceLockInitAddr + 0x30#64) L.stdoutVtableAddr, iAddLo12 .x3 .x3 L.stdoutVtableAddr],
   .words (L.stdoutOnceLockInitAddr + 0x38#64) [0xf9000fe9#32, 0x910023e9#32, 0x9100e100#32, 0xd10043a2#32, 0x52800021#32, 0xf81f03a9#32],
   .instrs L.stdoutOnceLockInitAddr 0x50 [iBl (L.stdoutOnceLockInitAddr + 0x50#64) L.onceCallAddr], .words (L.stdoutOnceLockInitAddr + 0x54#64) [0xa9437bfd#32, 0x910103ff#32, 0xd65f03c0#32],
   .words L.stdoutCleanupClosureAddr stdoutClosureWords]
def StdoutOnceLockCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (stdoutOnceLockChunks L)

theorem stdoutOnceLockInit_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 notInitPtr : BitVec 64} {oldFlag haveLse : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : StdoutOnceLockCode P L) (honce : OnceCallCode P L) (hcas : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr)) (hswp : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.stdoutOnceLockInitAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = notInitPtr) (hflag_nz : notInitPtr ≠ 0#64) (halign : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf (((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ (L.stdoutGlobalAddr ↦ₛ stdoutDummyBytes) ∗ (notInitPtr ↦₈ 1#8) ∗
        (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt sp0 176 ∗ F) post oom) :
    SepWP P target_pc s (((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗ (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗ (notInitPtr ↦₈ oldFlag) ∗
      (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt sp0 176 ∗ F) post oom := by
  subst hsp; unpack_code stdoutOnceLockChunks hc; rw [stackAt_split_cells s.sp 112 8 (by decide)]; unpack_cells 8
  wp_steps; refine step_ldar32_words (L.stdoutOnceLockInitAddr + 0x08#64) stdoutInitEntryWords 0 (L.stdoutOnceLockInitAddr + 12#64) halign (hnext := ?_); wp_steps; wp_steps; wp_steps
  have hp8 : s.sp - 48#64 = (s.sp - 56#64) + 8#64 := by bv_lin
  rw [hp8]; refine SepWP.weaken_pre (P' := ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt (s.sp - 64#64) 112 ∗
      (((s.sp - 32#64) ↦₆₄ (s.sp - 56#64)) ∗ ((s.sp - 56#64) ↦₆₄ notInitPtr) ∗ (((s.sp - 56#64) + 8#64) ↦₆₄ L.stdoutGlobalAddr) ∗
       (notInitPtr ↦₈ oldFlag) ∗ (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8)) ∗ ?F1) (by sep_frame) ?_
  refine onceCall_incomplete_wp (ret_pc := L.stdoutOnceLockInitAddr + 0x54#64) (sp0 := s.sp - 64#64) (dataPtr := s.sp - 32#64)
    (Post := ((s.sp - 32#64) ↦₆₄ (s.sp - 56#64)) ∗ ((s.sp - 56#64) ↦₆₄ 0#64) ∗ (((s.sp - 56#64) + 8#64) ↦₆₄ L.stdoutGlobalAddr) ∗ (notInitPtr ↦₈ 1#8) ∗ (L.stdoutGlobalAddr ↦ₛ stdoutDummyBytes))
    honce hcas hswp wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by simp [State.spAligned, wp_norm, arm64_norm]; simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x40#64 hsp_align)
    wp_a wp_a wp_a wp_a halign (fun sc G hpc_c hrun_c _ _ hlr_c hx0_c _ hret_c => SepWP.weaken_pre (by sep_frame)
      (stdoutClosure_wp (pairPtr := s.sp - 56#64) (stdoutAddr := L.stdoutGlobalAddr) (oldFlag := oldFlag) (F := (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ G)
        (show P.hasCode _ _ by with_reducible assumption) hpc_c hrun_c hlr_c hx0_c hflag_nz fun sr hpc_r hrun_r hsp_r hcs_r hstd_r => SepWP.weaken_pre (by sep_frame) (hret_c sr hpc_r hrun_r hsp_r hcs_r hstd_r)))
    fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 => ?_
  rw [← hp8]; have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1]; exact s.spAligned_sub 64#64 hsp_align
  wp_steps; refine SepWP.weaken_pre_frame (fun _ _ => by rw [stackAt_split_cells s.sp 112 8 (by decide)]; repack_cells)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a (by unpack_cs hcs1; close_cs) (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd1 std_rfl)))

def cleanupClosureChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.words L.cleanupClosureAddr [0xd101c3ff#32, 0xa9017bfd#32, 0xa9026ffc#32, 0xa90367fa#32, 0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32,
     0x910043fd#32, 0xf9400008#32, 0x39400109#32, 0x3900011f#32, 0x7100053f#32, 0x540014e1#32, 0x381fc3bf#32],
   .instrs L.cleanupClosureAddr 0x38 [iAdrp .x8 (L.cleanupClosureAddr + 0x38#64) (L.stdoutGlobalAddr + 0x38#64), iAddLo12 .x8 .x8 (L.stdoutGlobalAddr + 0x38#64)],
   .words (L.cleanupClosureAddr + 0x40#64) [0x88dffd08#32, 0x35001468#32], .words (L.cleanupClosureAddr + 0x2d0#64) [0xd10013a0#32],
   .instrs L.cleanupClosureAddr 0x2d4 [iBl (L.cleanupClosureAddr + 0x2d4#64) L.stdoutOnceLockInitAddr], .words (L.cleanupClosureAddr + 0x2d8#64) [0x385fc3a8#32, 0x3607eba8#32, 0x17ffffef#32],
   .words (L.cleanupClosureAddr + 0x29c#64) [0xa9464ff4#32, 0xa94557f6#32, 0xa9445ff8#32, 0xa94367fa#32, 0xa9426ffc#32, 0xa9417bfd#32, 0x9101c3ff#32, 0xd65f03c0#32]]
def CleanupClosureCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (cleanupClosureChunks L)

theorem cleanupClosure_uninit_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 dataPtr flagPtr : BitVec 64}
    {haveLse : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : CleanupClosureCode P L) (hinit : StdoutOnceLockCode P L) (honce : OnceCallCode P L)
    (hcas : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr)) (hswp : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.cleanupClosureAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hsp_lo : 112 ≤ sp0.toNat) (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = dataPtr) (halign : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf ((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗ ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
        (L.stdoutGlobalAddr ↦ₛ stdoutDummyBytes) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt sp0 288 ∗ F) post oom) :
    SepWP P target_pc s ((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 1#8) ∗ ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
      (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt sp0 288 ∗ F) post oom := by
  subst hsp; unpack_code cleanupClosureChunks hc; rw [stackAt_split_cells s.sp 176 14 (by decide)]; unpack_cells 14
  rw [pointsTo64_split32_sub s.sp 104#64 100#64, pointsTo32_split8_sub s.sp 100#64 99#64 98#64 97#64]
  wp_steps; refine step_ldar32_words (L.cleanupClosureAddr + 0x40#64) [0x88dffd08#32, 0x35001468#32] 0 (L.cleanupClosureAddr + 68#64) halign (hnext := ?_); wp_steps; wp_steps
  refine SepWP.weaken_pre (P' := ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗ (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
      ((s.sp - 100#64) ↦₈ 0#8) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt (s.sp - 112#64) 176 ∗ ?F1) (by sep_frame) ?_
  refine stdoutOnceLockInit_wp (ret_pc := L.cleanupClosureAddr + 0x2d8#64) (sp0 := s.sp - 112#64) (notInitPtr := s.sp - 100#64) hinit honce hcas hswp wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm]; simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align) wp_a wp_a (by bv_omega) halign fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 => ?_
  have hx29_1 : s1.readReg64 (.gpr 29#5) = s.sp - 96#64 := by have := hcs1.readReg64_x29; simp [wp_norm, arm64_norm, bv_lin_norm] at this; rw [this]; try bv_lin
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1]; exact s.spAligned_sub 112#64 hsp_align
  wp_steps; wp_steps; refine SepWP.weaken_pre_frame (fun _ hm => by rw [stackAt_split_cells s.sp 176 14 (by decide)]; repack_cells_split hm, s.sp, 104#64, 100#64, 99#64, 98#64, 97#64)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a (by unpack_cs hcs1; close_cs) (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd1 std_rfl)))

abbrev StdCleanupOnceGlobals (L : StdBinaryLayout) (haveLse : BitVec 8) (st : BitVec 32) (bs : List (BitVec 8)) : SepProp :=
  (L.cleanupOnceAddr ↦₃₂ st) ∗ ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ st) ∗ (L.stdoutGlobalAddr ↦ₛ bs) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
  StdVtableRo L.cleanupVtableAddr L.cleanupVtableShimAddr L.cleanupClosureAddr ∗ StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr

theorem onceCall_cleanup_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 dataPtr flagPtr : BitVec 64}
    {haveLse : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (honce : OnceCallCode P L) (hclean : CleanupClosureCode P L) (hinit : StdoutOnceLockCode P L)
    (hcas : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr)) (hswp : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.onceCallAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true) (hsp_lo : 400 ≤ sp0.toNat) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = L.cleanupOnceAddr) (hx2 : s.readReg64 .x2 = dataPtr) (hx3 : s.readReg64 .x3 = L.cleanupVtableAddr)
    (hal_clean : MemWidth.isAligned .W32 L.cleanupOnceAddr = true) (hal_out : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf (StdCleanupOnceGlobals L haveLse 0#32 stdoutDummyBytes ∗ (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 0#8) ∗ stackAt sp0 400 ∗ F) post oom) :
    SepWP P target_pc s (StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗ (dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 1#8) ∗ stackAt sp0 400 ∗ F) post oom := by
  subst hsp; rw [stackAt_split s.sp 112 288]
  refine SepWP.weaken_pre (P' := (L.cleanupOnceAddr ↦₃₂ 3#32) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ StdVtableRo L.cleanupVtableAddr L.cleanupVtableShimAddr L.cleanupClosureAddr ∗ stackAt s.sp 112 ∗
      ((dataPtr ↦₆₄ flagPtr) ∗ (flagPtr ↦₈ 1#8) ∗ ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗ (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
       StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗ stackAt (s.sp - 112#64) 288) ∗ F) (by sep_frame) ?_
  refine onceCall_incomplete_wp honce hcas hswp hpc hrun rfl hsp_align hlr hx0 hx2 hx3 hal_clean
    (fun sc G hpc_c hrun_c hsp_c hsp_alc hlr_c hx0_c _ hret_c => SepWP.weaken_pre (by sep_frame)
      (cleanupClosure_uninit_wp hclean hinit honce hcas hswp hpc_c hrun_c hsp_c hsp_alc (by bv_omega) hlr_c hx0_c hal_out
        fun sr hpc_r hrun_r hsp_r hcs_r hstd_r => SepWP.weaken_pre (by sep_frame) (hret_c sr hpc_r hrun_r (hsp_r.trans hsp_c.symm) hcs_r hstd_r)))
    fun sf hpc_f hrun_f hsp_f hcs_f hstd_f => SepWP.weaken_pre (by rw [stackAt_split s.sp 112 288]; sep_frame) (hnext sf hpc_f hrun_f hsp_f hcs_f hstd_f)

/-! ## `c_main` Post-`main` Cleanup and Return (`Unit` and `ExitCode` Variants) -/
def cMainPostUnitChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.words (L.beginShortBacktraceAddr + 0x0c#64) [0xa8c17bfd#32, 0xd65f03c0#32], .instrs L.cMainAddr 0x1f4 [iAdrp .x8 (L.cMainAddr + 0x1f4#64) L.cleanupOnceAddr, iAddLo12 .x8 .x8 L.cleanupOnceAddr],
   .words (L.cMainAddr + 0x1fc#64) [0x88dffd08#32, 0x350005e8#32], .words (L.cMainAddr + 0x2bc#64) [0x52800028#32, 0x910073a9#32],
   .instrs L.cMainAddr 0x2c4 [iAdrp .x0 (L.cMainAddr + 0x2c4#64) L.cleanupOnceAddr, iAddLo12 .x0 .x0 L.cleanupOnceAddr, iAdrp .x3 (L.cMainAddr + 0x2cc#64) L.cleanupVtableAddr, iAddLo12 .x3 .x3 L.cleanupVtableAddr],
   .words (L.cMainAddr + 0x2d4#64) [0x910023e2#32, 0x2a1f03e1#32, 0x390073a8#32, 0xf90007e9#32], .instrs L.cMainAddr 0x2e4 [iBl (L.cMainAddr + 0x2e4#64) L.onceCallAddr],
   .words (L.cMainAddr + 0x2e8#64) [0x17ffffc7#32], .instrs L.cMainAddr 0x204 [iBl (L.cMainAddr + 0x204#64) L.errnoLocationAddr], .words (L.cMainAddr + 0x208#64) [0xaa0003f3#32],
   .instrs L.cMainAddr 0x20c [iAdrp .x2 (L.cMainAddr + 0x20c#64) L.exitingThreadIdAddr, iAddLo12 .x2 .x2 L.exitingThreadIdAddr],
   .words (L.cMainAddr + 0x214#64) [0xaa1f03e0#32, 0xaa1303e1#32], .instrs L.cMainAddr 0x21c [iBl (L.cMainAddr + 0x21c#64) L.cas8AcqAddr],
   .words (L.cMainAddr + 0x220#64) [0xf100001f#32, 0x540000e1#32, 0xa9454ff4#32, 0xf9401bf7#32, 0xa94457f6#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32]]
def CMainPostUnitCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (cMainPostUnitChunks L)

def cMainPostExitChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.words (L.beginShortBacktraceAddr + 0x0c#64) [0xa8c17bfd#32, 0xd65f03c0#32], .instrs L.cMainAddr 0x208 [iAdrp .x8 (L.cMainAddr + 0x208#64) L.cleanupOnceAddr, iAddLo12 .x8 .x8 L.cleanupOnceAddr],
   .words (L.cMainAddr + 0x210#64) [0x2a0003f3#32, 0x88dffd08#32, 0x35000608#32], .words (L.cMainAddr + 0x2d8#64) [0x52800028#32, 0xd10013a9#32],
   .instrs L.cMainAddr 0x2e0 [iAdrp .x0 (L.cMainAddr + 0x2e0#64) L.cleanupOnceAddr, iAddLo12 .x0 .x0 L.cleanupOnceAddr, iAdrp .x3 (L.cMainAddr + 0x2e8#64) L.cleanupVtableAddr, iAddLo12 .x3 .x3 L.cleanupVtableAddr],
   .words (L.cMainAddr + 0x2f0#64) [0x910003e2#32, 0x2a1f03e1#32, 0x381fc3a8#32, 0xf90003e9#32], .instrs L.cMainAddr 0x300 [iBl (L.cMainAddr + 0x300#64) L.onceCallAddr],
   .words (L.cMainAddr + 0x304#64) [0x17ffffc6#32], .instrs L.cMainAddr 0x21c [iBl (L.cMainAddr + 0x21c#64) L.errnoLocationAddr], .words (L.cMainAddr + 0x220#64) [0xaa0003f4#32],
   .instrs L.cMainAddr 0x224 [iAdrp .x2 (L.cMainAddr + 0x224#64) L.exitingThreadIdAddr, iAddLo12 .x2 .x2 L.exitingThreadIdAddr],
   .words (L.cMainAddr + 0x22c#64) [0xaa1f03e0#32, 0xaa1403e1#32], .instrs L.cMainAddr 0x234 [iBl (L.cMainAddr + 0x234#64) L.cas8AcqAddr],
   .words (L.cMainAddr + 0x238#64) [0xf100001f#32, 0x54000101#32, 0x12001e60#32, 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32]]
def CMainPostExitCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (cMainPostExitChunks L)

local macro "repack_cmain_496 " hm:ident "," sp:term "," splitBase:term "," o8:term "," o4:term "," o3:term "," o2:term "," o1:term : tactic => `(tactic| (
  dsimp only [StdCleanupOnceGlobals] at $hm ⊢; replace $hm := combine_cell_byte4_sat $splitBase $o8 $o4 $o3 $o2 $o1 $hm
  rw [stackAt_split ($sp + 0x60#64) 48 448, show $sp + 0x60#64 - 48#64 = $sp + 0x30#64 by bv_lin, stackAt_split_cells ($sp + 0x30#64) 432 2 (by decide), stackAt_eq_cells ($sp + 0x60#64) 6]; cells_unfold
  rw [show $sp + 0x30#64 - 16#64 = $sp + 0x20#64 by bv_lin, show $sp + 0x30#64 - 8#64 = $sp + 0x28#64 by bv_lin, stackAt_split ($sp + 0x20#64) 32 400, show $sp + 0x20#64 - 32#64 = $sp by bv_lin, stackAt_eq_cells ($sp + 0x20#64) 4]
  cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))

theorem cMain_post_unit_wp {P : Program} {L : StdBinaryLayout} {target_pc sp_cmain saved_fp ret_stage2 : BitVec 64}
    {haveLse : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : CMainPostUnitCode P L) (honce : OnceCallCode P L) (hclean : CleanupClosureCode P L) (hinit : StdoutOnceLockCode P L)
    (herr : P.hasWords L.errnoLocationAddr errnoLocationWords) (hcas4 : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr)) (hcas8 : subroutine_ok P L.cas8AcqAddr (stdCas8Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.beginShortBacktraceAddr + 0x0c#64) (hrun : s.status = .Running) (hsp : s.sp = sp_cmain - 0x10#64) (hsp_align : s.spAligned = true) (hsp_lo : 400 ≤ sp_cmain.toNat)
    (hal_clean : MemWidth.isAligned .W32 L.cleanupOnceAddr = true) (hal_out : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true) (hal_exit : MemWidth.isAligned .X64 L.exitingThreadIdAddr = true)
    (hnext : ∀ sf : State, sf.pc = ret_stage2 → sf.status = .Running → sf.sp = sp_cmain + 0x60#64 → sf.spAligned = true → sf.readReg64 .x0 = 0#64 → StdFieldsPreserved s sf →
      SepWP P target_pc sf (StdCleanupOnceGlobals L haveLse 0#32 stdoutDummyBytes ∗ (L.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗ stackAt (sp_cmain + 0x60#64) 496 ∗ F) post oom) :
    SepWP P target_pc s (((sp_cmain - 0x10#64) ↦₆₄ (sp_cmain + 0x20#64)) ∗ ((sp_cmain - 0x08#64) ↦₆₄ (L.cMainAddr + 0x1f4#64)) ∗ stackAt (sp_cmain - 0x10#64) 384 ∗
      stackAt (sp_cmain + 0x20#64) 32 ∗ ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗ ((sp_cmain + 0x28#64) ↦₆₄ ret_stage2) ∗ stackAt (sp_cmain + 0x60#64) 48 ∗
      StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗ (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗ F) post oom := by
  unpack_code cMainPostUnitChunks hc; have hal_cm : (sp_cmain &&& 15#64 == 0#64) = true := by have := hsp_align; simp only [State.spAligned, hsp, beq_iff_eq] at this ⊢; bv_bits
  wp_steps; refine SepWP.weaken_pre_frame (P' := stackAt sp_cmain 400 ∗ stackAt (sp_cmain + 0x20#64) 32 ∗ ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗
      ((sp_cmain + 0x28#64) ↦₆₄ ret_stage2) ∗ stackAt (sp_cmain + 0x60#64) 48 ∗ StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗ (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗ F)
    (fun _ _ => by rw [stackAt_split_cells sp_cmain 384 2 (by decide)]; repack_cells) ?_
  rw [stackAt_eq_cells (sp_cmain + 0x20#64) 4, stackAt_eq_cells (sp_cmain + 0x60#64) 6]; unpack_cells 10; simp only [sepConj_assoc]
  rw [pointsTo64_split32_sub (sp_cmain + 0x60#64) 40#64 36#64, pointsTo32_split8_sub (sp_cmain + 0x60#64) 36#64 35#64 34#64 33#64]
  wp_steps; refine step_ldar32_words (L.cMainAddr + 0x1fc#64) [0x88dffd08#32, 0x350005e8#32] 0 (L.cMainAddr + 512#64) hal_clean (hnext := ?_); wp_steps; wp_steps; wp_steps
  try rw [show sp_cmain + 60#64 = sp_cmain + 0x60#64 - 36#64 by bv_lin]
  refine SepWP.weaken_pre (P' := StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗
      (((sp_cmain + 0x20#64) - 24#64) ↦₆₄ ((sp_cmain + 0x60#64) - 36#64)) ∗ (((sp_cmain + 0x60#64) - 36#64) ↦₈ 1#8) ∗ stackAt sp_cmain 400 ∗ ?F1) (by sep_frame) ?_
  refine onceCall_cleanup_wp (ret_pc := L.cMainAddr + 0x2e8#64) (sp0 := sp_cmain) (dataPtr := (sp_cmain + 0x20#64) - 24#64) (flagPtr := (sp_cmain + 0x60#64) - 36#64)
    honce hclean hinit hcas4 hswp4 wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm]; simp only [beq_iff_eq] at hal_cm ⊢; bv_bits) hsp_lo wp_a wp_a wp_a wp_a hal_clean hal_out fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 => ?_
  have hstd_s1 : StdFieldsPreserved s s1 := StdFieldsPreserved.trans std_rfl hstd1; wp_steps; wp_steps
  refine errnoLocation_wp (L := L) (ret_pc := L.cMainAddr + 0x208#64) herr wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a fun s2 hpc2 hrun2 hsp2 _ hx0_2 hstd2 => ?_
  have hsp2_eq : s2.sp = sp_cmain := by simpa [wp_norm, arm64_norm, hsp1] using hsp2
  simp only [State.setPC, State.writeReg64, show s1.tpidrEl0 = s.tpidrEl0 from hstd_s1.2.2.1] at hx0_2; wp_steps; wp_steps; wp_steps; wp_steps
  refine call_stdCas8 hcas8 (haveLse := haveLse) (ptr := L.exitingThreadIdAddr) (v0 := 0#64) (exp := 0#64) (new := s.tpidrEl0 - 0xa4#64)
    (ret_pc := L.cMainAddr + 0x220#64) (F := ?_) (by sep_frame) (fun s3 hpc3 hrun3 hsp3 _ hx0_3 hstd3 => ?_) (halign := hal_exit)
  simp only [beq_self_eq_true, ↓reduceIte]; have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
  have hsp3_eq : s3.sp = sp_cmain := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3_eq]; exact hal_cm
  wp_steps; refine SepWP.weaken_pre_frame (fun _ hm => by repack_cmain_496 hm, sp_cmain, (sp_cmain + 0x60#64), 40#64, 36#64, 35#64, 34#64, 33#64)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a (by simp only [State.spAligned, wp_norm, arm64_norm, beq_iff_eq]; simp only [beq_iff_eq] at hal_cm; bv_bits)
      (by simp [wp_norm, arm64_norm, hx0_3']) (StdFieldsPreserved.trans hstd_s1 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd2 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd3.toFields std_rfl))))))

theorem cMain_post_exitCode_wp {P : Program} {L : StdBinaryLayout} {target_pc sp_cmain saved_fp ret_stage2 : BitVec 64}
    {haveLse : BitVec 8} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : CMainPostExitCode P L) (honce : OnceCallCode P L) (hclean : CleanupClosureCode P L) (hinit : StdoutOnceLockCode P L)
    (herr : P.hasWords L.errnoLocationAddr errnoLocationWords) (hcas4 : subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr)) (hcas8 : subroutine_ok P L.cas8AcqAddr (stdCas8Spec L.haveLseAtomicsAddr))
    (hpc : s.pc = L.beginShortBacktraceAddr + 0x0c#64) (hrun : s.status = .Running) (hsp : s.sp = sp_cmain - 0x10#64) (hsp_align : s.spAligned = true) (hsp_lo : 400 ≤ sp_cmain.toNat)
    (hal_clean : MemWidth.isAligned .W32 L.cleanupOnceAddr = true) (hal_out : MemWidth.isAligned .W32 (L.stdoutGlobalAddr + 0x38#64) = true) (hal_exit : MemWidth.isAligned .X64 L.exitingThreadIdAddr = true)
    (hnext : ∀ sf : State, sf.pc = ret_stage2 → sf.status = .Running → sf.sp = sp_cmain + 0x60#64 → sf.spAligned = true → sf.readReg64 .x0 = ((s.readReg32 .x0).truncate 8).zeroExtend 64 → StdFieldsPreserved s sf →
      SepWP P target_pc sf (StdCleanupOnceGlobals L haveLse 0#32 stdoutDummyBytes ∗ (L.exitingThreadIdAddr ↦₆₄ (s.tpidrEl0 - 0xa4#64)) ∗ stackAt (sp_cmain + 0x60#64) 496 ∗ F) post oom) :
    SepWP P target_pc s (((sp_cmain - 0x10#64) ↦₆₄ (sp_cmain + 0x20#64)) ∗ ((sp_cmain - 0x08#64) ↦₆₄ (L.cMainAddr + 0x208#64)) ∗ stackAt (sp_cmain - 0x10#64) 384 ∗
      stackAt (sp_cmain + 0x20#64) 32 ∗ ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗ ((sp_cmain + 0x28#64) ↦₆₄ ret_stage2) ∗ stackAt (sp_cmain + 0x60#64) 48 ∗
      StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗ (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗ F) post oom := by
  unpack_code cMainPostExitChunks hc; have hal_cm : (sp_cmain &&& 15#64 == 0#64) = true := by have := hsp_align; simp only [State.spAligned, hsp, beq_iff_eq] at this ⊢; bv_bits
  wp_steps; refine SepWP.weaken_pre_frame (P' := stackAt sp_cmain 400 ∗ stackAt (sp_cmain + 0x20#64) 32 ∗ ((sp_cmain + 0x20#64) ↦₆₄ saved_fp) ∗
      ((sp_cmain + 0x28#64) ↦₆₄ ret_stage2) ∗ stackAt (sp_cmain + 0x60#64) 48 ∗ StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗ (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗ F)
    (fun _ _ => by rw [stackAt_split_cells sp_cmain 384 2 (by decide)]; repack_cells) ?_
  rw [stackAt_eq_cells (sp_cmain + 0x20#64) 4, stackAt_eq_cells (sp_cmain + 0x60#64) 6]; unpack_cells 10; simp only [sepConj_assoc]
  rw [pointsTo64_split32_sub (sp_cmain + 0x20#64) 8#64 4#64, pointsTo32_split8_sub (sp_cmain + 0x20#64) 4#64 3#64 2#64 1#64]
  wp_steps; wp_steps; refine step_ldar32_words (L.cMainAddr + 0x210#64) [0x2a0003f3#32, 0x88dffd08#32, 0x35000608#32] 1 (L.cMainAddr + 536#64) hal_clean (hnext := ?_); wp_steps; wp_steps; wp_steps
  try rw [show sp_cmain + 28#64 = sp_cmain + 0x20#64 - 4#64 by bv_lin]
  refine SepWP.weaken_pre (P' := StdCleanupOnceGlobals L haveLse 3#32 (List.replicate 56 0#8) ∗
      (((sp_cmain + 0x20#64) - 32#64) ↦₆₄ ((sp_cmain + 0x20#64) - 4#64)) ∗ (((sp_cmain + 0x20#64) - 4#64) ↦₈ 1#8) ∗ stackAt sp_cmain 400 ∗ ?F1) (by sep_frame) ?_
  refine onceCall_cleanup_wp (ret_pc := L.cMainAddr + 0x304#64) (sp0 := sp_cmain) (dataPtr := (sp_cmain + 0x20#64) - 32#64) (flagPtr := (sp_cmain + 0x20#64) - 4#64)
    honce hclean hinit hcas4 hswp4 wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm]; simp only [beq_iff_eq] at hal_cm ⊢; bv_bits) hsp_lo wp_a wp_a wp_a wp_a hal_clean hal_out fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 => ?_
  have hx19_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 19#5)) = BitVec.truncate 32 (s.readReg64 (.gpr 0#5)) := by have := hcs1.readReg32_x19; simp [wp_norm, arm64_norm] at this; exact this
  have hstd_s1 : StdFieldsPreserved s s1 := StdFieldsPreserved.trans std_rfl hstd1; wp_steps; wp_steps
  refine errnoLocation_wp (L := L) (ret_pc := L.cMainAddr + 0x220#64) herr wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hstd2 => ?_
  have hx19_2 : BitVec.truncate 32 (s2.readReg64 (.gpr 19#5)) = BitVec.truncate 32 (s.readReg64 (.gpr 0#5)) := by have := hcs2.readReg32_x19; simp [wp_norm, arm64_norm] at this; exact this.trans hx19_1
  have hsp2_eq : s2.sp = sp_cmain := by simpa [wp_norm, arm64_norm, hsp1] using hsp2
  simp only [State.setPC, State.writeReg64, show s1.tpidrEl0 = s.tpidrEl0 from hstd_s1.2.2.1] at hx0_2; wp_steps; wp_steps; wp_steps; wp_steps
  refine call_stdCas8 hcas8 (haveLse := haveLse) (ptr := L.exitingThreadIdAddr) (v0 := 0#64) (exp := 0#64) (new := s.tpidrEl0 - 0xa4#64)
    (ret_pc := L.cMainAddr + 0x238#64) (F := ?_) (by sep_frame) (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_) (halign := hal_exit)
  simp only [beq_self_eq_true, ↓reduceIte]; have hx0_3' : s3.readReg64 (.gpr 0#5) = 0#64 := hx0_3
  have hx19_3 : BitVec.truncate 32 (s3.readReg64 (.gpr 19#5)) = BitVec.truncate 32 (s.readReg64 (.gpr 0#5)) := by have := hcs3.readReg32_x19; simp [wp_norm, arm64_norm] at this; exact this.trans hx19_2
  have hsp3_eq : s3.sp = sp_cmain := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3_eq]; exact hal_cm
  wp_steps; refine SepWP.weaken_pre_frame (fun _ hm => by repack_cmain_496 hm, sp_cmain, (sp_cmain + 0x20#64), 8#64, 4#64, 3#64, 2#64, 1#64)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a (by simp only [State.spAligned, wp_norm, arm64_norm, beq_iff_eq]; simp only [beq_iff_eq] at hal_cm; bv_bits)
      (by simp [wp_norm, arm64_norm]; bv_bits) (StdFieldsPreserved.trans hstd_s1 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd2 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd3.toFields std_rfl))))))

/-! ## `musl` `exit` through `libc_exit_fini`, `__stdio_exit_needed`, and `_Exit` -/
def sysExitWords : List (BitVec 32) := [0x93407c01#32, 0xd2800bc8#32, 0xaa0103e0#32, 0xd4000001#32]
def muslExitChunks (L : StdBinaryLayout) : List CodeChunk :=
  [.instrs L.libcStartMainStage2Addr 0x38 [iBl (L.libcStartMainStage2Addr + 0x38#64) L.exitAddr], .words L.exitAddr [0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0x2a0003f3#32],
   .instrs L.exitAddr 0x10 [iBl (L.exitAddr + 0x10#64) L.dummyExitAddr, iBl (L.exitAddr + 0x14#64) L.libcExitFiniAddr, iBl (L.exitAddr + 0x18#64) L.stdioExitNeededAddr],
   .words (L.exitAddr + 0x1c#64) [0x2a1303e0#32], .instrs L.exitAddr 0x20 [iBl (L.exitAddr + 0x20#64) L.sysExitAddr], .words L.dummyExitAddr [0xd65f03c0#32],
   .words L.libcExitFiniAddr [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32],
   .instrs L.libcExitFiniAddr 0x0c [iAdrp .x19 (L.libcExitFiniAddr + 0x0c#64) (L.gotAddr + 0x60#64), iAdrp .x20 (L.libcExitFiniAddr + 0x10#64) (L.gotAddr + 0x68#64),
     iLdr64Lo12 .x19 .x19 (L.gotAddr + 0x60#64), iLdr64Lo12 .x20 .x20 (L.gotAddr + 0x68#64)],
   .words (L.libcExitFiniAddr + 0x1c#64) [0xeb14027f#32, 0x54000089#32, 0xf85f8e60#32, 0xd63f0000#32, 0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32],
   .instrs L.libcExitFiniAddr 0x38 [iB (L.libcExitFiniAddr + 0x38#64) L.finiFnAddr], .instrs0 L.doFiniAddr [iAdrp .x1 L.doFiniAddr L.finalizedAddr, iLdrbLo12 .x0 .x1 L.finalizedAddr],
   .words (L.doFiniAddr + 0x08#64) [0x35000340#32], .instrs L.doFiniAddr 0x0c [iAdrp .x0 (L.doFiniAddr + 0x0c#64) (L.gotAddr + 0x20#64)], .words (L.doFiniAddr + 0x10#64) [0x52800022#32],
   .instrs L.doFiniAddr 0x14 [iStrbLo12 .x2 .x1 L.finalizedAddr, iLdr64Lo12 .x0 .x0 (L.gotAddr + 0x20#64)], .words (L.doFiniAddr + 0x1c#64) [0xb40001a0#32],
   .instrs L.doFiniAddr 0x50 [iAdrp .x0 (L.doFiniAddr + 0x50#64) (L.gotAddr + 0x28#64), iLdr64Lo12 .x0 .x0 (L.gotAddr + 0x28#64)],
   .words (L.doFiniAddr + 0x58#64) [0xb40000c0#32], .words (L.doFiniAddr + 0x70#64) [0xd65f03c0#32],
   .words L.finiFnAddr [0xa9bf7bfd#32, 0x910003fd#32, 0xa8c17bfd#32, 0xd65f03c0#32], .words L.oflLockFnAddr [0xa9bf7bfd#32],
   .instrs L.oflLockFnAddr 0x04 [iAdrp .x0 (L.oflLockFnAddr + 0x04#64) L.oflLockAddr, iAddLo12 .x0 .x0 L.oflLockAddr], .words (L.oflLockFnAddr + 0x0c#64) [0x910003fd#32],
   .instrs L.oflLockFnAddr 0x10 [iBl (L.oflLockFnAddr + 0x10#64) L.lockFnAddr], .words (L.oflLockFnAddr + 0x14#64) [0xa8c17bfd#32],
   .instrs L.oflLockFnAddr 0x18 [iAdrp .x0 (L.oflLockFnAddr + 0x18#64) L.oflHeadAddr, iAddLo12 .x0 .x0 L.oflHeadAddr], .words (L.oflLockFnAddr + 0x20#64) [0xd65f03c0#32],
   .instrs0 L.lockFnAddr [iAdrp .x3 L.lockFnAddr L.libcAddr, iAddLo12 .x2 .x3 L.libcAddr], .words (L.lockFnAddr + 0x08#64) [0xaa0003e4#32, 0x320107e1#32, 0x39400c42#32, 0x13001c42#32, 0x34000402#32],
   .words (L.lockFnAddr + 0x98#64) [0xd65f03c0#32], .words L.stdioExitNeededAddr [0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32],
   .instrs L.stdioExitNeededAddr 0x0c [iBl (L.stdioExitNeededAddr + 0x0c#64) L.oflLockFnAddr], .words (L.stdioExitNeededAddr + 0x10#64) [0xf9400013#32, 0xaa1303e0#32, 0xb4000093#32],
   .instrs L.stdioExitNeededAddr 0x28 [iAdrp .x0 (L.stdioExitNeededAddr + 0x28#64) L.stdinUsedAddr, iLdr64Lo12 .x0 .x0 L.stdinUsedAddr,
     iBl (L.stdioExitNeededAddr + 0x30#64) L.closeFileAddr, iAdrp .x0 (L.stdioExitNeededAddr + 0x34#64) L.stdoutUsedAddr,
     iLdr64Lo12 .x0 .x0 L.stdoutUsedAddr, iBl (L.stdioExitNeededAddr + 0x3c#64) L.closeFileAddr, iAdrp .x0 (L.stdioExitNeededAddr + 0x40#64) L.stderrUsedAddr],
   .words (L.stdioExitNeededAddr + 0x44#64) [0xf9400bf3#32, 0xa8c27bfd#32], .instrs L.stdioExitNeededAddr 0x4c [iLdr64Lo12 .x0 .x0 L.stderrUsedAddr, iB (L.stdioExitNeededAddr + 0x50#64) L.closeFileAddr],
   .words L.closeFileAddr [0xb4000400#32, 0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32, 0xb9408c01#32, 0x36f802a1#32, 0xf9401661#32, 0xf9401e60#32, 0xeb00003f#32, 0x540000c0#32],
   .words (L.closeFileAddr + 0x40#64) [0xa9408261#32, 0xeb00003f#32, 0x54000160#32], .words (L.closeFileAddr + 0x74#64) [0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0xd65f03c0#32],
   .words L.sysExitAddr sysExitWords]
def MuslExitCode (P : Program) (L : StdBinaryLayout) : Prop := CodeChunks P (muslExitChunks L)

theorem libcExitFini_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MuslExitCode P L) (hpc : s.pc = L.libcExitFiniAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hfini_bnd : L.finiArrayAddr.toNat + 8 < 2 ^ 64) (hgot_al : MemWidth.isAligned .X64 L.gotAddr = true) (_hfini_al : MemWidth.isAligned .X64 L.finiArrayAddr = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf ((L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
        ((L.gotAddr + 0x60#64) ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗ ((L.gotAddr + 0x68#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ 1#8) ∗ stackAt sp0 32 ∗ F) post oom) :
    SepWP P target_pc s ((L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
      ((L.gotAddr + 0x60#64) ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗ ((L.gotAddr + 0x68#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ 0#8) ∗ stackAt sp0 32 ∗ F) post oom := by
  subst hsp; unpack_code muslExitChunks hc
  have hls1 : BitVec.ule (L.finiArrayAddr + 0x08#64) L.finiArrayAddr = false := by simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ⟨hal20, hal28, hal60, hal68⟩ : MemWidth.isAligned .X64 (L.gotAddr + 0x20#64) = true ∧ MemWidth.isAligned .X64 (L.gotAddr + 0x28#64) = true ∧
      MemWidth.isAligned .X64 (L.gotAddr + 0x60#64) = true ∧ MemWidth.isAligned .X64 (L.gotAddr + 0x68#64) = true := by
    simp only [MemWidth.isAligned, beq_iff_eq] at hgot_al ⊢; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits
  rw [stackAt_eq_cells s.sp 4]; unpack_cells 4; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp; wp_steps
  refine SepWP.weaken_pre_frame (fun _ _ => by rw [stackAt_eq_cells s.sp 4]; repack_cells) (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs) std_rfl)

/-- Symbolic execution of `close_file(L.stderrFileAddr)` when `stderr` buffer is clean (`wpos == wbase`, `rpos == rend`). -/
theorem closeFile_stderr_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MuslExitCode P L) (hpc : s.pc = L.closeFileAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = L.stderrFileAddr) (hstderr_nz : L.stderrFileAddr ≠ 0#64) (hstderr_al : MemWidth.isAligned .X64 L.stderrFileAddr = true)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf → SepWP P target_pc sf (StdStderrFile L ∗ stackAt sp0 32 ∗ F) post oom) :
    SepWP P target_pc s (StdStderrFile L ∗ stackAt sp0 32 ∗ F) post oom := by
  subst hsp; unpack_code muslExitChunks hc; have hnzb : (L.stderrFileAddr == 0#64) = false := beq_false_of_ne hstderr_nz
  have ⟨hal08, hal10, hal28, hal38, hal8c⟩ : MemWidth.isAligned .X64 (L.stderrFileAddr + 0x08#64) = true ∧ MemWidth.isAligned .X64 (L.stderrFileAddr + 0x10#64) = true ∧
      MemWidth.isAligned .X64 (L.stderrFileAddr + 0x28#64) = true ∧ MemWidth.isAligned .X64 (L.stderrFileAddr + 0x38#64) = true ∧ MemWidth.isAligned .W32 (L.stderrFileAddr + 0x8c#64) = true := by
    simp only [MemWidth.isAligned, beq_iff_eq] at hstderr_al ⊢; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
  dsimp only [StdStderrFile, StdBinaryLayout.stderrFileAtoms, rwAtomListSep, RwAtom.toSepProp]; rw [stackAt_eq_cells s.sp 4]; unpack_cells 4; wp_steps; wp_steps; wp_steps
  refine SepWP.weaken_pre_frame (fun _ _ => by dsimp only [StdStderrFile, StdBinaryLayout.stderrFileAtoms, rwAtomListSep, RwAtom.toSepProp]; rw [stackAt_eq_cells s.sp 4]; repack_cells)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs) std_rfl)

theorem stdioExitNeeded_wp {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MuslExitCode P L) (hpc : s.pc = L.stdioExitNeededAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (_hal_ofl : MemWidth.isAligned .X64 L.oflHeadAddr = true) (_hal_stdin : MemWidth.isAligned .X64 L.stdinUsedAddr = true)
    (_hal_stdout : MemWidth.isAligned .X64 L.stdoutUsedAddr = true) (_hal_stderr_u : MemWidth.isAligned .X64 L.stderrUsedAddr = true)
    (hal_stderr : MemWidth.isAligned .X64 L.stderrFileAddr = true) (hstderr_nz : L.stderrFileAddr ≠ 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf (((L.libcAddr + 3#64) ↦₈ᵣ 0#8) ∗ (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
        (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗ (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L ∗ stackAt sp0 48 ∗ F) post oom) :
    SepWP P target_pc s (((L.libcAddr + 3#64) ↦₈ᵣ 0#8) ∗ (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
      (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗ (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L ∗ stackAt sp0 48 ∗ F) post oom := by
  subst hsp; unpack_code muslExitChunks hc; have hstk : stackAt s.sp 48 = stackAt s.sp 32 ∗ stackAt (s.sp - 32#64) 16 := by rw [stackAt_split s.sp 32 16, sepConj_comm]
  rw [stackAt_eq_cells s.sp 6]; unpack_cells 6; wp_steps; norm_jmp; wp_steps; wp_steps; norm_jmp; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp; wp_steps
  by_cases h_alias : L.stdoutUsedAddr == L.stdinUsedAddr <;> (
    first | (simp only [h_alias, ↓reduceIte, emp_sepConj] at hnext ⊢; rw [← beq_iff_eq.mp h_alias])
          | (simp only [Bool.not_eq_true] at h_alias; simp only [h_alias, Bool.false_eq_true, ↓reduceIte] at hnext ⊢)
    wp_steps; norm_jmp; wp_steps; wp_steps; wp_steps; norm_jmp; try rw [beq_iff_eq.mp h_alias]
    refine SepWP.weaken_pre_frame (P' := StdStderrFile L ∗ stackAt s.sp 32 ∗ (stackAt (s.sp - 32#64) 16 ∗ ((L.libcAddr + 3#64) ↦₈ᵣ 0#8) ∗
        (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗ (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗ (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ F))
      (fun _ _ => by first | (have : (_ == _) = true := h_alias; simp only [h_alias, ↓reduceIte, emp_sepConj]) | simp only [h_alias, Bool.false_eq_true, ↓reduceIte]
                     rw [← sepConj_assoc (stackAt s.sp 32), ← hstk, stackAt_eq_cells s.sp 6]; repack_cells) ?_
    refine closeFile_stderr_wp (ret_pc := ret_pc) (sp0 := s.sp) hc wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simp [State.spAligned, wp_norm, arm64_norm, bv_lin_norm]; simpa [State.spAligned] using hsp_align) wp_a wp_a hstderr_nz hal_stderr
      fun sf hpc_f hrun_f hsp_f hcs_f hstd_f => SepWP.weaken_pre
        (by first | (have : (_ == _) = true := h_alias; simp only [h_alias, ↓reduceIte, emp_sepConj]) | simp only [h_alias, Bool.false_eq_true, ↓reduceIte]
            rw [← sepConj_assoc (stackAt s.sp 32), ← hstk]; sep_frame)
        (hnext sf hpc_f hrun_f hsp_f (by unpack_cs hcs_f; close_cs) (StdFieldsPreserved.trans std_rfl hstd_f)))

abbrev StdMuslExitGlobals (L : StdBinaryLayout) (finalized : BitVec 8) : SepProp :=
  (L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
  ((L.gotAddr + 0x60#64) ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗ ((L.gotAddr + 0x68#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ finalized) ∗
  ((L.libcAddr + 3#64) ↦₈ᵣ 0#8) ∗ (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗ (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗ (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L

theorem muslExit_to_svc_wp {P : Program} {L : StdBinaryLayout} {target_pc sp0 : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MuslExitCode P L) (hpc : s.pc = L.libcStartMainStage2Addr + 0x38#64) (hrun : s.status = .Running) (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hfini_bnd : L.finiArrayAddr.toNat + 8 < 2 ^ 64) (hgot_al : MemWidth.isAligned .X64 L.gotAddr = true) (hfini_al : MemWidth.isAligned .X64 L.finiArrayAddr = true)
    (hal_ofl : MemWidth.isAligned .X64 L.oflHeadAddr = true) (hal_stdin : MemWidth.isAligned .X64 L.stdinUsedAddr = true) (hal_stdout : MemWidth.isAligned .X64 L.stdoutUsedAddr = true)
    (hal_stderr_u : MemWidth.isAligned .X64 L.stderrUsedAddr = true) (hal_stderr : MemWidth.isAligned .X64 L.stderrFileAddr = true) (hstderr_nz : L.stderrFileAddr ≠ 0#64)
    (hnext : ∀ sf : State, sf.pc = L.sysExitAddr + 0x0c#64 → sf.status = .Running → sf.sp = sp0 - 0x20#64 → sf.spAligned = true →
      sf.readReg64 .x8 = 94#64 → sf.readReg64 .x0 = (s.readReg32 .x0).signExtend 64 → StdFieldsPreserved s sf → SepWP P target_pc sf (StdMuslExitGlobals L 1#8 ∗ stackAt sp0 80 ∗ F) post oom) :
    SepWP P target_pc s (StdMuslExitGlobals L 0#8 ∗ stackAt sp0 80 ∗ F) post oom := by
  subst hsp; unpack_code muslExitChunks hc; dsimp only [StdMuslExitGlobals]; rw [stackAt_split_cells s.sp 48 4 (by decide)]; unpack_cells 4
  wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps; wp_steps; norm_jmp; rw [stackAt_split (s.sp - 32#64) 32 16]
  refine SepWP.weaken_pre (P' := (L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 0x20#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 0x28#64) ↦₆₄ 0#64) ∗
      ((L.gotAddr + 0x60#64) ↦₆₄ (L.finiArrayAddr + 0x08#64)) ∗ ((L.gotAddr + 0x68#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ 0#8) ∗ stackAt (s.sp - 32#64) 32 ∗ ?F1) (by sep_frame) ?_
  refine libcExitFini_wp (ret_pc := L.exitAddr + 0x18#64) (sp0 := s.sp - 32#64) hc wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
    (by simp [State.spAligned, wp_norm, arm64_norm]; simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align) wp_a hfini_bnd hgot_al hfini_al fun s1 hpc1 hrun1 hsp1 hcs1 hstd1 => ?_
  have hx19_1 : s1.readReg64 .x19 = (s.readReg32 .x0).zeroExtend 64 := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hstd_s1 : StdFieldsPreserved s s1 := StdFieldsPreserved.trans std_rfl hstd1; wp_steps; norm_jmp
  refine SepWP.weaken_pre (P' := ((L.libcAddr + 3#64) ↦₈ᵣ 0#8) ∗ (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
      (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗ (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L ∗ stackAt (s.sp - 32#64) 48 ∗ ?F2)
    (by rw [stackAt_split (s.sp - 32#64) 32 16]; sep_frame) ?_
  refine stdioExitNeeded_wp (ret_pc := L.exitAddr + 0x1c#64) (sp0 := s.sp - 32#64) hc wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp1]; simpa [State.spAligned, beq_iff_eq] using hsp_align) wp_a hal_ofl hal_stdin hal_stdout hal_stderr_u hal_stderr hstderr_nz fun s2 hpc2 hrun2 hsp2 hcs2 hstd2 => ?_
  have hx19_2 : s2.readReg64 (.gpr 19#5) = (s.readReg32 .x0).zeroExtend 64 := by have := hcs2.readReg64_x19; simp [wp_norm, arm64_norm, hx19_1] at this; exact this
  wp_steps; norm_jmp; wp_steps 3; refine SepWP.weaken_pre_frame (fun _ _ => by dsimp only [StdMuslExitGlobals]; rw [stackAt_split_cells s.sp 48 4 (by decide)]; repack_cells)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hsp2]; try bv_lin) (by simp [State.spAligned, wp_norm, arm64_norm, hsp2]; simpa [State.spAligned, beq_iff_eq] using hsp_align) wp_a
      (by simp [wp_norm, arm64_norm]; simpa [Arm64.evalBitfield] using BitVec.sbfm_sxtw_eq_signExtend 0#64 (BitVec.setWidth 64 (BitVec.setWidth 32 (s.readReg64 (.gpr 0#5)))))
      (StdFieldsPreserved.trans hstd_s1 (StdFieldsPreserved.trans std_rfl (StdFieldsPreserved.trans hstd2 std_rfl))))

set_option linter.literalFetch false in
theorem MuslExitCode.fetch_sysExit_svc {P : Program} {L : StdBinaryLayout} (hc : MuslExitCode P L) : P.fetch (L.sysExitAddr + 0x0c#64) = some (.system false 0#16) := by
  unpack_code muslExitChunks hc; exact Program.fetch_of_hasCode_decodeAt 3 (hex := sysExitWords) (by with_reducible assumption) (by simp only [wp_norm]) (by decide)

/-! ## Combined `StdCleanupCode` Bundle and `WordTree` Validator -/
structure StdCleanupCode (P : Program) (L : StdBinaryLayout) : Prop where
  onceCall : OnceCallCode P L
  stdout   : StdoutOnceLockCode P L
  cleanup  : CleanupClosureCode P L
  errnoLoc : P.hasWords L.errnoLocationAddr errnoLocationWords
  cMain    : if L.userMainReturnsExitCode then CMainPostExitCode P L else CMainPostUnitCode P L
  muslExit : MuslExitCode P L

section WordTreeCheck
open ProofLib.ProgramReflection
def checkCleanupWordsAt (base : BitVec 64) (t : WordTree) (addr : BitVec 64) (ws : List (BitVec 32)) : Bool := decide ((addr - base).toNat + 4 * ws.length ≤ 2 ^ 64) && checkWordsAt t (addr - base).toNat ws
def checkCleanupInstrsAt (base : BitVec 64) (t : WordTree) (addr : BitVec 64) (is : List Instr) : Bool := (base + BitVec.ofNat 64 (addr - base).toNat == addr) && decide ((addr - base).toNat + 4 * is.length < 2 ^ 64) && checkInstrsAt t (addr - base).toNat is
def checkCodeChunk (base : BitVec 64) (t : WordTree) : CodeChunk → Bool
  | .words a ws => checkCleanupWordsAt base t a ws | .instrs0 b is => checkCleanupInstrsAt base t b is | .instrs b o is => checkCleanupInstrsAt base t (b + BitVec.ofNat 64 o) is
private theorem codeChunks_of_all {P : Program} {b : BitVec 64} {t : WordTree} (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) : ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial | [_], h => hc (by simpa using h) | _ :: _ :: _, h => by rw [List.all_cons, Bool.and_eq_true] at h; exact ⟨hc h.1, codeChunks_of_all hc h.2⟩
/-- $O(k \log N)$ boolean validator discharging `StdCleanupCode P L` from a `WordTree`. -/
def checkCleanupCode (L : StdBinaryLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  [onceCallChunks L, stdoutOnceLockChunks L, cleanupClosureChunks L, [.words L.errnoLocationAddr errnoLocationWords],
   if L.userMainReturnsExitCode then cMainPostExitChunks L else cMainPostUnitChunks L, muslExitChunks L].all (fun cs => cs.all (checkCodeChunk base t))
theorem stdCleanupCode_of_wordTree {P : Program} {L : StdBinaryLayout} {t : WordTree} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl) (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl) (hok : checkCleanupCode L P.base t = true) : StdCleanupCode P L := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h; exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h; exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkCleanupCode at hok; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok; rcases hok with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨codeChunks_of_all hc h1, codeChunks_of_all hc h2, codeChunks_of_all hc h3, @hc (.words _ _) (by simpa using h4), ?_, codeChunks_of_all hc h6⟩
  by_cases hec : L.userMainReturnsExitCode <;> simp only [hec, Bool.false_eq_true, ↓reduceIte] at h5 ⊢ <;> exact codeChunks_of_all hc h5
end WordTreeCheck
end ProofLib.StdStartup
