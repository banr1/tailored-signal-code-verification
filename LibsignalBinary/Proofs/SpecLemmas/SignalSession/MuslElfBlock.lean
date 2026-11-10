/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslStart
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# musl Startup Block from `_start` to `main`

Packages `MuslStart.musl_start_ofImage` (hops 1–7 from `_start` at `B` to `main = B - 89668`)
as a single `Steps` transition `musl_start_block` on `Program.ofImage img E` over the
initial stack table, program headers, 60 zero stack words below `sp0 - 48`, and musl's
writable statics (`muslRwWords`) at `B + 0x2000`.
-/

namespace CryptoVerification.SignalSession.MuslElf

open Arm64 ProofLib CryptoVerification.SignalSession.MuslExit
  CryptoVerification.SignalSession.MuslStart

/-- `k` consecutive 8-byte cells starting at `a`. -/
def cellsW (a : BitVec 64) : Nat → SepProp
  | 0 => emp
  | k + 1 => (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ cellsW (a + 8#64) k

theorem memRegion_cellsW (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cellsW a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cellsW]

theorem sat_of_entails_frame {m : Memory} {P Q F : SepProp} (hm : m ⊨ P) (h : P ⊢ Q ∗ F) :
    m ⊨ Q := by
  have h1 := Satisfies.mono h hm
  rw [sepConj_comm] at h1
  exact Satisfies.drop_left h1

theorem pointsTo64_eq_8 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₈ v.extractLsb' 0 8) ∗
      (pointsTo8 (a + 1#64) (v.extractLsb' 8 8) ∗ pointsTo8 (a + 2#64) (v.extractLsb' 16 8) ∗
       pointsTo8 (a + 3#64) (v.extractLsb' 24 8) ∗ pointsTo8 (a + 4#64) (v.extractLsb' 32 8) ∗
       pointsTo8 (a + 5#64) (v.extractLsb' 40 8) ∗ pointsTo8 (a + 6#64) (v.extractLsb' 48 8) ∗
       pointsTo8 (a + 7#64) (v.extractLsb' 56 8))) := by
  unfold pointsTo64; rw [BitVec.add_zero]

/-- Initial contents of musl's writable statics at `B + 0x2000 .. B + 0x2258` (600 bytes). -/
def muslRwWords (h0 g3 g4 ia F : BitVec 64) : List (BitVec 64) :=
  [h0, 0#64, g3, g4, ia, ia, F, F] ++ List.replicate 67 0#64

set_option maxHeartbeats 3200000 in
theorem musl_start_block {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    (E : String → Option (State → State)) {B : BitVec 64} {code : List (BitVec 8)}
    (hend : img.base.toNat + img.code.length ≤ B.toNat) (hnw : B.toNat + 0xb90 ≤ 2 ^ 64)
    (hf : MuslStartFetch ({ code } : Program) 0#64) (hB : B &&& 0xfff#64 = 0#64)
    {s : State} (hL : ({ base := B, code } : Program).CodeLoaded s.mem)
    (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex : BitVec 64) (a32 ah32 : BitVec 32)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64)
    (hp : p ≠ 0#64) (hph : ph + 504#64 ≠ 0#64)
    (h0 g3 g4 ia F : BitVec 64) (hh0 : h0.extractLsb' 0 32 = 0x20000#32)
    {R : SepProp}
    (hm : s.mem ⊨ StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
      StartArgv0 p ∗ StartPhdrs ph ∗ ((B + 0x2000#64) ↦₆₄* muslRwWords h0 g3 g4 ia F) ∗
      ((s.sp - 480#64) ↦₆₄* List.replicate 60 0#64) ∗ R) :
    ∃ sm, Steps (Program.ofImage img E) s sm ∧ sm.pc = B - 85504#64 ∧ sm.status = .Running ∧
      Hop7Regs B s.sp (s.sp + 8#64) (a32.zeroExtend 64) s.fs s.trace sm ∧
      (sm.mem ⊨ StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
        StartArgv0 p ∗ ((B + 0x2030#64) ↦₆₄ F) ∗ ((B + 0x2038#64) ↦₆₄ F) ∗
        memRegion (s.sp - 480#64) 432 ∗ R) := by
  unfold muslRwWords at hm
  simp (disch := decide) only [List.cons_append, List.nil_append, List.replicate_succ,
    List.replicate_zero, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub] at hm
  rw [pointsTo64_split32 (B + 8192#64) h0, hh0, pointsTo64_split32 (B + 8352#64) 0#64,
    pointsTo64_split32 (B + 8360#64) 0#64, pointsTo64_eq_8 (B + 8680#64) 0#64] at hm
  obtain ⟨sm, hsteps, hpc', hrun', hinv, hpost⟩ := musl_start_ofImage (R := _) himg E hend hnw hf hL
    (fun Q hfQ hsvc => musl_start Q B hfQ hsvc hB s hpc hrun hal hsp16 envp p ph pg ab af ae uid gid plat hw
      clk rnd hw2 ex a32 ah32 henvp hp hph g3 g4 ia
      0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
      0#64 0#64 0#64
      0#64 0#64 0#64 0#64 ((0#64).extractLsb' 0 8) ((0#64).extractLsb' 0 32)
      ((0#64).extractLsb' 0 32)
      0#64 0#64 0#64 0#64 0#64 0#64 0#64
      0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
      0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
      0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64)
    (by sep_frame)
  refine ⟨sm, hsteps, hpc', hrun', hinv, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨x1, x2, x3, x4, hpost⟩ := hpost
  rw [show memRegion (s.sp - 480#64) 432 = memRegion (s.sp - 480#64) (8 * 54) from rfl,
    memRegion_cellsW _ 54 (by decide)]
  simp (disch := decide) only [cellsW, sepConj_emp, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  apply sat_of_entails_frame hpost
  sep_frame

end CryptoVerification.SignalSession.MuslElf
