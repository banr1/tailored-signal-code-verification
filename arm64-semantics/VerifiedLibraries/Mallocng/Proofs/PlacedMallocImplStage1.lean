/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage1a
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl` Join Epilogue

Proves `mallocImpl_join_epilogue`, the shared exit sequence (`__unlock`, `get_stride`, `enframe`,
and `RET`) used by the fast path, `alloc_slot` slow path, and large `mmap` path in
`__libc_malloc_impl`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `get_stride` and `enframe` Head/Mask Step Lemmas -/

private theorem getStride_bv_helpers :
    (∀ b : BitVec 8, BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b) = BitVec.zeroExtend 64 b) ∧
    (∀ h : BitVec 16, BitVec.zeroExtend 64 (BitVec.zeroExtend 32 h) = BitVec.zeroExtend 64 h) ∧
    (∀ b : BitVec 8, BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b)) = BitVec.zeroExtend 64 b) ∧
    (∀ h : BitVec 16, BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 h)) = BitVec.zeroExtend 64 h) ∧
    (∀ u : BitVec 64, (u == 0#64) = true → (u != 0#64) = false) ∧
    (∀ u : BitVec 64, (u == 0#64) = false → (u != 0#64) = true) :=
  ⟨fun _ => by bv_bits, fun _ => by bv_bits, fun _ => by bv_bits, fun _ => by bv_bits,
   fun _ h => by revert h; bv_bits, fun _ h => by revert h; bv_bits⟩

private theorem getStride_ldr8_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {G : SepProp} {metaPtr packedWord cycVal : BitVec 64}
    {metaBytes : List (BitVec 8)} {req idx : Nat}
    (hMetaLen : metaBytes.length = 40)
    (hPk : pack64 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8) (metaBytes.getD 34 0#8) (metaBytes.getD 35 0#8)
      (metaBytes.getD 36 0#8) (metaBytes.getD 37 0#8) (metaBytes.getD 38 0#8) (metaBytes.getD 39 0#8) = packedWord)
    (hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true)
    (_hB0N : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 != 0#64) = false)
    (hpc : s.pc = b + miOff_after_unlock) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx) (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_tst_mask) s ((metaPtr ↦ₛ metaBytes) ∗ G)
      (fun s1 P1 =>
        (s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 4#5) = packedWord ∧
         s1.readReg64 (.gpr 19#5) = cycVal ∧ s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
         s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ (metaPtr ↦ₛ metaBytes) ∗ G))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  dsimp only [miOff_after_unlock, miOff_tst_mask] at hpc ⊢
  have hReadPk : ByteSlice.readLE metaBytes 32 8 = packedWord := by
    rw [← ByteSlice.pack64_eq_readLE_8]; dsimp only [Nat.reduceAdd]; exact hPk
  have hHide : Nonempty (PLift ((BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true ∧
    ByteSlice.readLE metaBytes 32 8 = packedWord)) := ⟨⟨⟨hB0, hReadPk⟩⟩⟩
  clear hPk hB0 hReadPk
  wp_step
  wp_step
  obtain ⟨⟨hB0, hReadPk⟩⟩ := hHide
  conv => arg 3; rw [hB0]
  clear hB0
  have hHide2 : Nonempty (PLift (ByteSlice.readLE metaBytes 32 8 = packedWord)) := ⟨⟨hReadPk⟩⟩
  clear hReadPk
  wp_steps 2
  obtain ⟨⟨hReadPk⟩⟩ := hHide2
  apply SepWP.done; · rfl
  · exact hrun
  · exact ⟨⟨rfl, rfl, rfl, hProc, untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
      by simp [hReadPk], by simpa using hx19, by simpa using hx20, by simpa using hx21,
      by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩

private theorem getStride_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {metaPtr packedWord cycVal : BitVec 64}
    {metaBytes : List (BitVec 8)} {stride lastIdx sc req idx : Nat}
    (hMetaLen : metaBytes.length = 40)
    (hPk : pack64 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8) (metaBytes.getD 34 0#8) (metaBytes.getD 35 0#8)
      (metaBytes.getD 36 0#8) (metaBytes.getD 37 0#8) (metaBytes.getD 38 0#8) (metaBytes.getD 39 0#8) = packedWord)
    (hTst0 : (((metaBytes.getD 32 0#8).zeroExtend 32).zeroExtend 64 &&& 0x1f#64 == 0#64) = decide (lastIdx = 0))
    (hZ : lastIdx = 0 → ((packedWord &&& 0xfffffffffffff000#64) == 0#64) = false ∧
      (packedWord &&& 0xfffffffffffff000#64) - 0x10#64 = BitVec.ofNat 64 stride)
    (hNZ : lastIdx ≠ 0 → sc < 48 ∧
      (((pack16 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8)).zeroExtend 32).zeroExtend 64 >>> 6) &&& 0x3f#64 =
        BitVec.ofNat 64 sc ∧
      (BitVec.ofNat 64 sc <<< 1) = BitVec.ofNat 64 (2 * sc) ∧
      (((BitVec.ofNat 16 (sizeClass sc)).zeroExtend 32).zeroExtend 64 &&& 0xffff#64) <<< 4 = BitVec.ofNat 64 stride)
    (hpc : s.pc = b + miOff_after_unlock) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx) (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_44) s
      ((metaPtr ↦ₛ metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 4#5) = BitVec.ofNat 64 stride ∧ s1.readReg64 (.gpr 19#5) = cycVal ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
         s1.readReg64 (.gpr 22#5) = metaPtr ∧ s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ (metaPtr ↦ₛ metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ F))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hScLen : sizeClassBytes.length = 96 := sizeClassBytes_length
  by_cases hL0 : lastIdx = 0
  · obtain ⟨hMNe0, hStrEq⟩ := hZ hL0
    clear hZ hNZ
    have hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true := by
      rw [← getStride_bv_helpers.1]; simpa only [hL0, decide_true] using hTst0
    have hB0N : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 != 0#64) = false :=
      getStride_bv_helpers.2.2.2.2.1 _ hB0
    clear hTst0
    refine SepWP.seq_entails_emp
      (getStride_ldr8_step hb hMetaLen hPk hB0 hB0N hpc hrun hProc hcsHi hx19 hx20 hx21 hx22 hx23) ?_
    rintro sm hpcm hrunm ⟨hspm, hbrkm, hpermm, hProcm, hcsm, hx4pk, hx19m, hx20m, hx21m, hx22m, hx23m⟩
    clear hPk hB0 hB0N
    dsimp only [miOff_tst_mask, miOff_enframe_44] at hpcm ⊢
    have hHide0 : Nonempty (PLift (((packedWord &&& 0xfffffffffffff000#64) == 0#64) = false ∧
      (packedWord &&& 0xfffffffffffff000#64) - 0x10#64 = BitVec.ofNat 64 stride)) := ⟨⟨⟨hMNe0, hStrEq⟩⟩⟩
    clear hMNe0 hStrEq
    wp_steps 2
    wp_if hBr2
    · obtain ⟨⟨hMNe0, _⟩⟩ := hHide0
      have hEq0 : packedWord &&& 0xfffffffffffff000#64 = 0#64 := hBr2
      rw [hEq0] at hMNe0; cases hMNe0
    · wp_steps 3
      obtain ⟨⟨_, hStrEq⟩⟩ := hHide0
      apply SepWP.done; · simp
      · simp [hrunm]
      · exact ⟨⟨by simp [hspm, hsp], by simp [hbrkm], by simp [arm64_norm, hpermm],
          by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcm,
          untouchedCS_step hcsm (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simp [hStrEq], by simp [hx19m], by simp [hx20m], by simp [hx21m],
          by simp [hx22m], by simp [hx23m]⟩, Entails.refl _⟩
  · dsimp only [miOff_after_unlock, miOff_enframe_44] at hpc ⊢
    obtain ⟨hSc48, hUbfx, hShl1, hStrEq⟩ := hNZ hL0
    have hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = false := by
      rw [← getStride_bv_helpers.1]; simpa only [hL0, decide_false] using hTst0
    clear hZ hNZ hPk hTst0
    have hUbfx1 : ((BitVec.zeroExtend 64 (pack16 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8))) >>> 6) &&& 0x3f#64 =
        BitVec.ofNat 64 sc := by rw [← getStride_bv_helpers.2.1]; exact hUbfx
    have hRead2 : (ByteSlice.readLE metaBytes 32 2 >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 sc := by
      rw [ByteSlice.readLE_two]; dsimp only [Nat.reduceAdd]; exact hUbfx1
    have hPackSc : pack16 (sizeClassBytes.getD (2 * sc) 0#8) (sizeClassBytes.getD (2 * sc + 1) 0#8) =
        BitVec.ofNat 16 (sizeClass sc) := pack16_sizeClassBytes hSc48
    generalize hScV : sizeClass sc = scVal at hPackSc hStrEq; clear hScV
    have hReadSc : ByteSlice.readLE sizeClassBytes (2 * sc) 2 =
        BitVec.zeroExtend 64 (BitVec.ofNat 16 scVal) := by
      rw [ByteSlice.readLE_two, hPackSc]
    have hStrEq1 : ((BitVec.zeroExtend 64 (BitVec.ofNat 16 scVal)) &&& 0xffff#64) <<< 4 =
        BitVec.ofNat 64 stride := by rw [← getStride_bv_helpers.2.1]; exact hStrEq
    generalize hScB : sizeClassBytes = scBytes at hScLen hPackSc hReadSc ⊢; clear hScB
    have hHideNZ : Nonempty (PLift ((BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = false)) :=
      ⟨⟨hB0⟩⟩
    clear hB0 hUbfx hStrEq
    wp_step
    wp_step
    obtain ⟨⟨hB0⟩⟩ := hHideNZ
    conv => arg 3; rw [hB0]
    clear hB0
    wp_steps
    apply SepWP.done; · simp
    · simp [hrun]
    · exact ⟨⟨by simp [hsp], by simp, by simp [arm64_norm],
        by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
        untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp,
        by simp [hx19], by simp [hx20], by simp [hx21],
        by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩

private theorem enframe_mask_bv_aux (x3 : BitVec 64) (w1 : BitVec 32) (hw1 : w1 &&& 255#32 = w1) :
    let x5 := x3 >>> 4
    let m32 := BitVec.truncate 32 (((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) |||
      (((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) >>> 4))
    let w1_raw : BitVec 32 :=
      if x5.ult (BitVec.zeroExtend 64 (w1 &&& m32)) = true then
        (w1 &&& m32) + BitVec.truncate 32 (~~~(BitVec.zeroExtend 64 (BitVec.truncate 32 x5)))
      else w1 &&& m32
    BitVec.truncate 32 (BitVec.zeroExtend 64 w1) = w1 ∧
    ((w1.signExtend 64).ule x5 = true → x5.ult (w1.signExtend 64) = false) ∧
    (w1 = BitVec.ofNat 32 w1.toNat → BitVec.zeroExtend 64 w1 = BitVec.ofNat 64 w1.toNat) ∧
    (¬ (w1.signExtend 64).ule x5 = true →
      w1_raw &&& 255#32 = w1_raw ∧
      x5.ult (w1_raw.signExtend 64) = false ∧
      (w1_raw = BitVec.ofNat 32 w1_raw.toNat → BitVec.zeroExtend 64 w1_raw = BitVec.ofNat 64 w1_raw.toNat)) := by
  dsimp only
  have hTrZ : ∀ a : BitVec 32, BitVec.truncate 32 (a.zeroExtend 64) = a := fun _ => by bv_omega
  refine ⟨hTrZ w1, by bv_bits, fun h => by rw [h]; bv_omega, fun hNotUle => ?_⟩
  have hGt : (x3 >>> 4).ult (w1.signExtend 64) = true := by revert hNotUle; bv_bits
  obtain ⟨hUltF, hAnd, _⟩ := enframeMaskReduce_spec x3 w1 hw1 hGt
  generalize hr3 : (((x3 >>> 4 ||| (x3 >>> 5)) ||| ((x3 >>> 4 ||| (x3 >>> 5)) >>> 2)) |||
    (((x3 >>> 4 ||| (x3 >>> 5)) ||| ((x3 >>> 4 ||| (x3 >>> 5)) >>> 2)) >>> 4)) = r3 at hUltF hAnd ⊢
  generalize hx5 : (x3 >>> 4) = x5 at hUltF hAnd ⊢
  have hNotX5 : BitVec.truncate 32 (~~~(BitVec.zeroExtend 64 (BitVec.truncate 32 x5))) = ~~~(x5.truncate 32) := by bv_bits
  rw [hNotX5]
  exact ⟨hAnd, hUltF, fun h => by rw [h]; bv_omega⟩

private theorem enframe_step_bv_simps :
    (∀ x1v : BitVec 64, x1v &&& 255#64 = x1v →
      BitVec.truncate 32 x1v &&& 255#32 = BitVec.truncate 32 x1v ∧
      x1v = BitVec.zeroExtend 64 (BitVec.truncate 32 x1v)) ∧
    (∀ u : BitVec 64, (u &&& 255#64) &&& 255#64 = u &&& 255#64) :=
  ⟨fun _ h => ⟨by revert h; bv_bits, by revert h; bv_bits⟩, fun _ => by bv_bits⟩

private theorem enframe_mask_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {P : SepProp} {start storage metaPtr : BitVec 64} {stride req idx : Nat}
    (hShr4 : BitVec.ofNat 64 (stride - 4 - req) >>> 4 = BitVec.ofNat 64 ((stride - 4 - req) / 16))
    (hW1Fit : ∀ w : BitVec 32, w &&& 255#32 = w →
      (BitVec.ofNat 64 ((stride - 4 - req) / 16)).ult (w.signExtend 64) = false →
      w.toNat ≤ 255 ∧ 16 * w.toNat + req ≤ stride - 4 ∧ w = BitVec.ofNat 32 w.toNat)
    (hpc : s.pc = b + miOff_enframe_90) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = start)
    (hx1_and : s.readReg64 (.gpr 1#5) &&& 255#64 = s.readReg64 (.gpr 1#5))
    (hx2 : s.readReg64 (.gpr 2#5) = storage) (hx3 : s.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (stride - 4 - req))
    (hx4 : s.readReg64 (.gpr 4#5) = 0#64) (hx5 : s.readReg64 (.gpr 5#5) = BitVec.ofNat 64 (stride - 4 - req) >>> 4)
    (hx6 : s.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_c4) s P
      (fun s1 P1 =>
        (∃ off : Nat, off ≤ 255 ∧ 16 * off + req ≤ stride - 4 ∧
          s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
          s1.readReg64 (.gpr 0#5) = start ∧ s1.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off ∧
          s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 4#5) = 0#64 ∧
          s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
          s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
          s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧ (P1 ⊢ P))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hShrF : Unit → _ := fun _ => hShr4; clear hShr4
  obtain ⟨hw1, hx1⟩ := enframe_step_bv_simps.1 _ hx1_and
  generalize hw1_def : BitVec.truncate 32 (s.readReg64 (.gpr 1#5)) = w1 at hw1 hx1
  clear hw1_def hx1_and
  have hAux : Unit → _ ∧ _ ∧ _ := fun _ => ⟨enframe_mask_bv_aux (BitVec.ofNat 64 (stride - 4 - req)) w1 hw1, hW1Fit, hw1⟩
  clear hW1Fit hw1
  wp_steps
  wp_if hHs
  · obtain ⟨⟨hTrW1, hUleImp, hZXNat, _⟩, hW1Fit, hw1⟩ := hAux ()
    have hUltF : (BitVec.ofNat 64 ((stride - 4 - req) / 16)).ult (w1.signExtend 64) = false := by
      rw [← hShrF ()]; exact hUleImp (by simpa only [hTrW1] using hHs)
    obtain ⟨h255, hFit, hW1Eq⟩ := hW1Fit w1 hw1 hUltF
    have hX1Eq := hx1.trans (hZXNat hW1Eq)
    clear hW1Eq
    apply SepWP.done; · simp
    · simp [hrun]
    · refine ⟨⟨w1.toNat, h255, hFit, by simp [hsp], rfl, rfl,
        procPres_setPC (procPres_setPState hProc),
        untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [hx0], by simp [hX1Eq], by simp [hx2], by simp [hx4],
        by simp [hx6], by simp [hx20], by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩
  · wp_steps
    wp_if hLoop
    · obtain ⟨⟨hTrW1, _, _, hMaskImp⟩, _, _⟩ := hAux ()
      obtain ⟨_, hUltF', _⟩ := hMaskImp (by simpa only [hTrW1] using hHs)
      exact False.elim (Bool.false_ne_true (hUltF'.symm.trans (by simpa only [hTrW1] using hLoop)))
    · obtain ⟨⟨hTrW1, _, _, hMaskImp⟩, hW1Fit, _⟩ := hAux ()
      obtain ⟨hw1', hUltF', hZXNat'⟩ := hMaskImp (by simpa only [hTrW1] using hHs)
      obtain ⟨h255, hFit, _⟩ := hW1Fit _ hw1' (by rw [← hShrF ()]; exact hUltF')
      clear hZXNat' hMaskImp hAux hW1Fit hTrW1
      apply SepWP.done; · exact State.pc_setPC ..
      · exact (State.status_setPC ..).trans ((State.status_setPState ..).trans (by simp [hrun]))
      · refine ⟨⟨_, h255, hFit,
          by simp [hsp], by simp, by simp [arm64_norm],
          by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
          untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simp [hx0], by simp, by simp [hx2], by simp [hx4], by simp [hx6],
          by simp [hx20], by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩

private theorem enframe_head_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {start storage metaPtr cycVal : BitVec 64}
    {slotBs metaBytes : List (BitVec 8)} {stride req idx : Nat}
    (hFit0 : req + 4 ≤ stride) (hSlotLen : slotBs.length = stride) (hMetaLen : metaBytes.length = 40)
    (hMemPk : pack64 (metaBytes.getD 16 0#8) (metaBytes.getD 17 0#8) (metaBytes.getD 18 0#8) (metaBytes.getD 19 0#8)
      (metaBytes.getD 20 0#8) (metaBytes.getD 21 0#8) (metaBytes.getD 22 0#8) (metaBytes.getD 23 0#8) + 16#64 = storage)
    (hSlot0 : (slotBs[0]?).getD 0#8 = 0#8)
    (hStrSubReq : (BitVec.ofNat 64 stride - BitVec.ofNat 64 req) - 4#64 = BitVec.ofNat 64 (stride - 4 - req))
    (hStrSub4 : BitVec.ofNat 64 stride - 4#64 = BitVec.ofNat 64 (stride - 4))
    (hMadd : storage + BitVec.ofNat 64 stride * BitVec.ofNat 64 idx = start)
    (hpc : s.pc = b + miOff_enframe_44) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx4 : s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 stride) (hx19 : s.readReg64 (.gpr 19#5) = cycVal)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_90) s
      (((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
          s1.readReg64 (.gpr 0#5) = start ∧
          s1.readReg64 (.gpr 1#5) &&& 255#64 = s1.readReg64 (.gpr 1#5) ∧
          s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (stride - 4 - req) ∧
          s1.readReg64 (.gpr 4#5) = 0#64 ∧ s1.readReg64 (.gpr 5#5) = BitVec.ofNat 64 (stride - 4 - req) >>> 4 ∧
          s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
          s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
          s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ ((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  obtain ⟨_, hAnd64⟩ := enframe_step_bv_simps
  have hReadMem : ByteSlice.readLE metaBytes 16 8 + 16#64 = storage := by
    rw [← ByteSlice.pack64_eq_readLE_8]; exact hMemPk
  have hSlot0D : slotBs.getD 0 0#8 = 0#8 := by rw [List.getD_eq_getElem?_getD, hSlot0]
  have hSlot1 : ByteSlice.readLE slotBs 0 1 = 0#64 := by rw [ByteSlice.readLE_one, hSlot0D]; rfl
  wp_steps
  wp_if hCbz4
  · wp_steps
    apply SepWP.done; · rfl
    · exact hrun
    · exact ⟨⟨by simpa using hsp, rfl, rfl, hProc, untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
        by simp, by simp [hAnd64], by simp, by simp, by simp, by simp, by simp,
        by simpa using hx20, by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩
  · wp_steps
    apply SepWP.done; · rfl
    · exact hrun
    · exact ⟨⟨by simpa using hsp, rfl, rfl, hProc, untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
        by simp, by simp [hAnd64], by simp, by simp, by simp, by simp, by simp,
        by simpa using hx20, by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩

/-! ## Shared Join Epilogue -/

private theorem at_bl_target_b09 [MallocngMultiPlacement] {b : BitVec 64}
    (_hb : BlkBase 9 b) (j : Nat) (off : BitVec 64) :
    mbase j = b + off + (mbase j - b - off) := by bv_arith

set_option maxHeartbeats 400000 in
theorem mallocImpl_join_epilogue [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req idx : Nat} {cycVal : BitVec 64}
    {st0 st1 : MallocngSt} {g : GroupDesc} {s0 s : State} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hCnt1 : totalLiveCount st1 = totalLiveCount st0)
    (hMetaLe1 : st1.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101)
    (hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize) (hFit0 : req + 4 ≤ g.stride)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc24M : g.sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hDelta : MallocngMappedDelta 16 (MallocngTightStepBound req bud.peakCount) s0.mem s.mem)
    (hpc : s.pc = mbase 9 + miOff_call_unlock) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = maddrs.lock)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ mallocImplSuccessPost24 γ tp brkStart bud ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  refine SepWP.mono (oom := fun _ => ⌜False⌝) (post := fun sf P_f =>
    sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
    MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ mallocImplSuccessBody24 γ tp brkStart bud ivs0 req s0 sf)) ?_ ?_
  · have hgw := hwf1.groups_wf g hg
    obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
    obtain ⟨hTst0, hZ, hNZ⟩ := getStride_props hgw
    obtain ⟨_, hStrSubReq, hStrSub4, hShr4, hMadd, hW1Fit, _⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
    have hSlot0 : ((readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride)[0]?).getD 0#8 = 0#8 := by
      have hSW := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
      have h0lt : 0 < (readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride).length := by
        rw [readBytesFromMap_length]; omega
      rw [List.getElem?_eq_getElem h0lt, Option.getD_some, readBytesFromMap_getElem _ _ _ 0 h0lt]
      simpa using hSW.1
    obtain ⟨hMemMeta, _, _, _, _, hPkMeta, _⟩ := metaBytes_ops g 0 0#32 .claimed
    have hExtSlot := slot_extract hwf1 hNoRes hg hIdx hClaimed
    have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
    let start := g.slotStart idx
    let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
    let rwTail := ByteMap st1.masterDom
      (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
    let roTail := (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
      (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
      (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
      (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)
    let coreRest := MallocngLiveAuth γ st1.liveMap ∗ (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
      (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
      MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1)
    let unlockFrame := MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail ∗ ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      coreRest ∗ MallocngRuntime maddrs tp
    have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail) := rfl
    have hPreInit : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
        MallocngRuntime maddrs tp) = ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) := by
      rw [hRoSplit]
      dsimp only [MallocngCoreStInflightA, unlockFrame, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb,
        (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, MallocngLiveAuth γ st1.liveMap = pGm, MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreInit]
    have hSpAl : s.spAligned = true := by
      dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
    wp_step
    have hunlock := placed_unlockNoop_perm_ok (P := blkPC_b09.rebase b (fun _ => none)) maddrs.lock
    rw [at_bl_target_b09 hb 23 miOff_call_unlock] at hunlock
    refine SepWP.call_subroutine_frame (F := unlockFrame) (x := ()) (ret_pc := b + miOff_after_unlock)
      hunlock rfl (by simp [arm64_norm, hrun]) (by simpa [State.spAligned, arm64_norm] using hSpAl)
      (by dsimp only [miOff_call_unlock, miOff_after_unlock, Reg.lr]; simp [arm64_norm])
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        dsimp only [withCL]
        rw [sepConj_comm]
        exact Entails.pure_right hcl (Entails.pure_right (by simpa [arm64_norm] using hx0) (Entails.refl _)))
      (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
      (fun su hpc_u hrun_u hsp_u hcs_u => ?_)
    dsimp only [withCL]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProc_u0, hbrk_u, hperm_u⟩
    apply SepWP.weaken_pre (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl unlockFrame))
    have hProc_u : MallocngProcPreserved s su :=
      ⟨hProc_u0.1, hProc_u0.2.1, hProc_u0.2.2.1, hProc_u0.2.2.2.1,
       hProc_u0.2.2.2.2.1, hProc_u0.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_writeReg64] using hProc_u0.2.2.2.2.2.2⟩
    have hsp_su : su.sp = s0.sp - 80#64 := hsp_u.trans hsp
    have hbrk_su : su.brk = s.brk := hbrk_u
    have hProc_su : MallocngProcPreserved s0 su := procPres_trans hProc hProc_u
    have hcs_su : MallocImplUntouchedCS s0 su :=
      untouchedCS_step hcsHi (hcs_u.2.2.2.2.2.2.2.1.trans (by simp))
        (hcs_u.2.2.2.2.2.2.2.2.1.trans (by simp)) (hcs_u.2.2.2.2.2.2.2.2.2.1.trans (by simp))
        (by simpa [calleeSavedVRegs] using hcs_u.2.2.2.2.2.2.2.2.2.2.2)
    have hPreG : ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
         (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) := by
      dsimp only [unlockFrame]
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreG]
    refine SepWP.seq_entails_emp
      (getStride_step hb (by simp [GroupDesc.metaBytes]) hPkMeta hTst0
        (fun h => ⟨(hZ h).2.1, (hZ h).2.2⟩) hNZ hpc_u hrun_u hsp_su hProc_su hcs_su
        (hcs_u.1.trans (by simpa using hx19)) (hcs_u.2.1.trans (by simpa using hx20))
        (hcs_u.2.2.1.trans (by simpa using hx21)) (hcs_u.2.2.2.1.trans (by simpa using hx22))
        (hcs_u.2.2.2.2.1.trans (by simpa using hx23))) ?_
    rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    have hPreH : ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
        (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) =
        (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
         ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) := by
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreH]
    refine SepWP.seq_entails_emp
      (enframe_head_step hb hFit0 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
        (by rw [hMemMeta]; rfl) hSlot0 hStrSubReq hStrSub4 hMadd
        hpc1 hrun1 hsp1 hProc1 hcs1 hx4_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1) ?_
    rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx20_2, hx22_2, hx23_2⟩
    refine SepWP.seq_entails_emp
      (enframe_mask_step hb hShr4 hW1Fit hpc2 hrun2 hsp2 hProc2 hcs2
        hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 hx5_2 hx6_2 hx20_2 hx22_2 hx23_2) ?_
    rintro s3 hpc3 hrun3 ⟨off, hOff255, hFit, hsp3, hbrk3, hperm3, hProc3, hcs3, hx0_3, hx1_3, hx2_3, hx4_3, hx6_3, hx20_3, hx22_3, hx23_3⟩
    have hBrk3 : s3.brk = s.brk := hbrk3.trans (hbrk2.trans (hbrk1.trans hbrk_su))
    have hPerm3 : s3.mem.perm = s.mem.perm := hperm3.trans (hperm2.trans (hperm1.trans hperm_u))
    have hwf3 : MallocngWFInflight 1 maddrs.base brkStart s3.brk bud.liveCost bud.peakCost st1 := hBrk3 ▸ hwf1
    have hNoOrph3 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s3.mem :=
      mallocngNoOrphanMappings_congr_perm rfl rfl rfl hPerm3 hNoOrph1
    have hPreF : (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) =
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStInflightA 1 γ maddrs brkStart s3.brk bud.liveCost bud.peakCost st1 ∗
         MallocngRuntime maddrs tp) := by
      rw [hRoSplit]
      dsimp only [MallocngCoreStInflightA, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf3⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb,
        (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, MallocngLiveAuth γ st1.liveMap = pGm, MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreF]
    subst hb_eq
    rw [← mallocngBlockProg_eq_b09]
    exact SepWP.mono (mallocImpl_enframe_finish hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph3 hwf3 hNoRes
      hg hIdx hClaimed hReqMax hFit0 hOff255 hFit hSc2 hSc24 hSc24M hSc63 hSc63_4115 hZeroMm htp0 hbrkS0
      hpc3 hrun3 hsp3 hsp_align hProc3 hcs3 hx0_3 hx1_3 hx2_3 hx4_3 hx6_3 hx20_3 hx22_3 hx23_3)
      (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.trans hBrk3, h3.trans hPerm3, h4, h5, h6⟩)
  · rintro sf P_f _ _ ⟨hsf_sp, _, hsf_perm, hsf_proc, hsf_cs, hPf⟩
    have hDeltaF : MallocngMappedDelta 16 (MallocngTightStepBound req bud.peakCount) s0.mem sf.mem :=
      mappedDelta_congr_perm_right hDelta hsf_perm
    refine ⟨Entails.trans hPf ?_, hsf_sp, hsf_cs⟩
    dsimp only [mallocImplSuccessPost24]
    exact Entails.pure_right ⟨hsf_proc, hDeltaF⟩ (Entails.refl _)

end VerifiedLibraries.Mallocng.Proofs
