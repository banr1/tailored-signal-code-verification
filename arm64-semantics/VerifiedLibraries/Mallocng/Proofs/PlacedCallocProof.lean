/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.Cost.TokSpecs
import VerifiedLibraries.Mallocng.Proofs.AllzeropProof
import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers
import VerifiedLibraries.Mallocng.Proofs.MemsetSym
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Placed `calloc` Verification

Verifies `mallocng` block `2` (`calloc`, `56` instructions) under any valid `Obj.MultiPlacement`,
parameterized over `DefaultMallocPlacedTokStmt B` (`callocPlaced_entry_tok_ok` and
`callocPlaced_entry_tight_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Pure Accounting, Overflow, and Zero-Slice Helpers -/

private theorem mappedDelta_congr_perm {k nb : Nat} {m0 m0' mf mf' : Memory}
    (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hd : MallocngMappedDelta k nb m0' mf') : MallocngMappedDelta k nb m0 mf := by
  obtain ⟨ivs, hlen, hsum, hcov⟩ := hd; refine ⟨ivs, hlen, hsum, fun a ha => ?_⟩
  rw [hf] at ha; rcases hcov a ha with hm0' | hiv
  · left; rwa [← h0]
  · right; exact hiv

private theorem noOrphanMappings_congr_perm {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m0' mf mf' : Memory} (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hno : MallocngNoOrphanMappings ivs0 ivsf m0' mf') : MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a ha hsrc; rw [hf] at ha; rw [← h0] at hsrc; exact hno a ha hsrc

private theorem procPreserved_trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

private theorem stackFrameAt_1024_split_48_704 (sp0 : BitVec 64) :
    stackFrameAt sp0 1024 =
      (stackFrameAt (sp0 - 48#64) 704 ∗ stackFrameAt (sp0 - 752#64) 272 ∗ cells (sp0 - 48#64) 6) := by
  rw [stackFrameAt_eq_memRegion sp0 1024, stackFrameAt_eq_memRegion (sp0 - 48#64) 704,
      stackFrameAt_eq_memRegion (sp0 - 752#64) 272]
  have hb1 : sp0 - 1024#64 + BitVec.ofNat 64 272 = sp0 - 752#64 := by bv_arith
  have hb2 : sp0 - 752#64 + BitVec.ofNat 64 704 = sp0 - 48#64 := by bv_arith
  have h1 : memRegion (sp0 - 1024#64) 1024 = (memRegion (sp0 - 1024#64) 272 ∗ memRegion (sp0 - 752#64) 752) := by
    rw [memRegion_split (sp0 - 1024#64) 272 752 (by omega), hb1]
  have h2 : memRegion (sp0 - 752#64) 752 = (memRegion (sp0 - 752#64) 704 ∗ memRegion (sp0 - 48#64) 48) := by
    rw [memRegion_split (sp0 - 752#64) 704 48 (by omega), hb2]
  have h3 : memRegion (sp0 - 48#64) 48 = cells (sp0 - 48#64) 6 := memRegion_cells _ 6 (by omega)
  have ha1 : sp0 - 48#64 - 704#64 = sp0 - 752#64 := by bv_arith
  have ha2 : sp0 - 752#64 - 272#64 = sp0 - 1024#64 := by bv_arith
  rw [h1, h2, h3, ha1, ha2]; ac_rfl

private theorem readBytes_of_prefixFilled' {m₀ mf : Memory} {dst c : BitVec 64} {n : Nat}
    (hfc : PrefixFilled m₀ mf dst c n n) : mf.readBytes dst n = List.replicate n (c.truncate 8) := by
  have go : ∀ k off, off + k ≤ n →
      mf.readBytes (dst + BitVec.ofNat 64 off) k = List.replicate k (c.truncate 8) := by
    intro k; induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro off hk; simp only [Memory.readBytes, List.replicate_succ]
      rw [hfc.2 off (by omega),
          show dst + BitVec.ofNat 64 off + 1#64 = dst + BitVec.ofNat 64 (off + 1) by bv_omega,
          ih (off + 1) (by omega)]
  simpa using go n 0 (by omega)

private theorem placed_memsetZero_perm_ok [MallocngMultiPlacement] {P : Program}
    (dst : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hbsLen : bs.length = n) (hn48 : n ≤ 2 ^ 48)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 21) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg32 .x1 = 0#32 ∧ (s0.readReg64 .x2).toNat = n⌝ ∗ (dst ↦ₛ bs)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm ∧
         sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ List.replicate n 0#8)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 21) (by decide) ?_ hext hsvc
  have hw := hasWords_blk_relocFree (i := 21) (by decide) (ws := memsetWordsSym) (by decide +kernel)
  have hc : (mallocngBlockProg mmpl 21 msvc).hasCode (mbase 21) memsetWordsSym := hw
  apply subroutine_ok_outcome_intro; intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx1_32, hx2⟩, hmem⟩ := hpre
  have htrunc : (s0.readReg64 .x1).truncate 8 = 0#8 := by
    have h32 : (s0.readReg64 .x1).truncate 32 = 0#32 := hx1_32
    revert h32; generalize s0.readReg64 .x1 = v; intro h32; bv_bits
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  by_cases hn96 : n ≤ 96
  · have hc_ns : ((mallocngBlockProg mmpl 21 msvc).withSvc mallocngFaultSvc).hasCode (mbase 21) memsetWordsSym :=
      Program.hasWords_withSvc hc
    have hwp := SepWP.lift_noSyscalls (prog := mallocngBlockProg mmpl 21 msvc) (oom := fun _ => ⌜False⌝) rfl rfl
      (memset_sepWP_le96 _ (mbase 21) hc_ns s0 dst (s0.readReg64 .x1) (s0.readReg64 .x2) bs
        hpc hrun hx0 rfl rfl (by omega) (by omega))
    refine reaches_pc_mono (SepWP.to_reaches_pc hwp hmem) ?_ (fun _ _ h => not_satisfies_false_sepConj h)
    rintro sf _ _ ⟨P_f, hmf, ⟨⟨hx0_f, hsp_f, hcs_f, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩, hent⟩, hperm⟩
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ List.replicate n 0#8) ∗ R := by
      have hm' := Satisfies.mono (sepConj_mono_left hent) hmf; rwa [htrunc, hx2] at hm'
    refine ⟨?_, hsp_f, hcs_f⟩; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hperm, hx0_f⟩, hpost_mem⟩
  · have hreg : s0.mem ⊨ memRegion dst n ∗ R := by
      have hent := (IsBlock.pointsToBytes dst bs).entails_memRegion; rw [hbsLen] at hent
      exact Satisfies.mono (sepConj_mono_left hent) hmem
    have hrw : s0.mem.RW dst (s0.readReg64 .x2).toNat := by
      rw [hx2]; exact (IsBlock.memRegion dst n).rw hreg
    refine memset_sym_large (mallocngBlockProg mmpl 21 msvc) (mbase 21) hc s0 _
      dst (s0.readReg64 .x1) (s0.readReg64 .x2) hpc hrun hx0 rfl rfl hrw (by omega) (by omega) ?_
    rintro sf _ _ hx0_f ⟨hcc, _hlr, hfs, htr, htpidr, hbrks, horc, hsym, hsig, hbrk⟩ hfc
    let zbs := List.replicate n 0#8
    have hzlen : zbs.length = n := List.length_replicate
    have hdst_bytes : sf.mem.readBytes dst zbs.length = zbs := by
      rw [hzlen]; have hrb := readBytes_of_prefixFilled' hfc; rwa [htrunc, hx2] at hrb
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ zbs) ∗ R :=
      (IsBlock.memRegion dst n).update (IsBlock.pointsToBytes dst zbs)
        (Nat.le_of_eq hzlen) hreg (by simpa [hx2] using hfc.1) ⟨by omega, hdst_bytes⟩
    refine ⟨?_, hcc⟩; simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs, htr, htpidr, hbrks, horc, hsym, hsig⟩, hbrk, hfc.perm_eq, hx0_f⟩, hpost_mem⟩

private theorem umulh_eq_zero_iff (a b : BitVec 64) :
    ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64 = 0#64 ↔ a.toNat * b.toNat < 2 ^ 64 := by
  have ha : a.toNat < 2 ^ 64 := a.isLt; have hb : b.toNat < 2 ^ 64 := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by
    have : a.toNat * b.toNat < (2 ^ 64) * (2 ^ 64) := Nat.mul_lt_mul'' ha hb; omega
  have h128 : (a.zeroExtend 128 * b.zeroExtend 128).toNat = a.toNat * b.toNat := by
    simp only [BitVec.zeroExtend, BitVec.toNat_mul, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 128), Nat.mod_eq_of_lt hprod]
  have hdiv_lt : (a.toNat * b.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  have htrunc : (((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64).toNat = (a.toNat * b.toNat) / 2 ^ 64 := by
    simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, h128, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv_lt]
  constructor
  · intro h0
    have ht : (((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64).toNat = 0 := by rw [h0]; rfl
    rw [htrunc] at ht; omega
  · intro hlt; apply BitVec.eq_of_toNat_eq; rw [htrunc]; exact Nat.div_eq_of_lt hlt

private theorem mul_toNat_of_no_overflow {a b : BitVec 64} (hlt : a.toNat * b.toNat < 2 ^ 64) :
    (b * a).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt hlt]

private theorem pointsToBytes_replicate_zero_split (p : BitVec 64) (m n : Nat) :
    (p ↦ₛ List.replicate (m + n) 0#8) = ((p ↦ₛ List.replicate m 0#8) ∗ ((p + BitVec.ofNat 64 m) ↦ₛ List.replicate n 0#8)) := by
  rw [List.replicate_add, pointsToBytes_append, List.length_replicate]

private def CalleeSaved21_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧ s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧ s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧ s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem calleeSaved21_28_trans {s0 s1 s2 : State}
    (h01 : CalleeSaved21_28 s0 s1) (hcs : CalleeSavedPreserved s1 s2) : CalleeSaved21_28 s0 s2 :=
  ⟨hcs.2.2.1.trans h01.1, hcs.2.2.2.1.trans h01.2.1, hcs.2.2.2.2.1.trans h01.2.2.1,
   hcs.2.2.2.2.2.1.trans h01.2.2.2.1, hcs.2.2.2.2.2.2.1.trans h01.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2⟩

private theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) : CalleeSavedPreserved s0 s2 := by
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩ := h01
  obtain ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv⟩ := h12
  exact ⟨b19.trans a19, b20.trans a20, b21.trans a21, b22.trans a22, b23.trans a23, b24.trans a24,
    b25.trans a25, b26.trans a26, b27.trans a27, b28.trans a28, b29.trans a29, bv.trans av⟩

private theorem spAligned_sub48 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 48#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp0 &&& 15#64 = 0#64 := beq_iff_eq.mp h; apply beq_iff_eq.mpr; revert h0; bv_bits

/-! ## Block `2` (`calloc`) Stage Lemmas -/

private theorem at_bl_target [MallocngMultiPlacement] {idx : Nat} {b : BitVec 64}
    (hb : BlkBase idx b) (j : Nat) (off : BitVec 64) : mbase j = b + off + (mbase j - mbase idx - off) := by
  have hb' : b = mbase idx := hb; rw [hb']; bv_arith

private theorem repack_stackFrame_1024 (sp0 v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (stackFrameAt (sp0 - 48#64) 704 ∗ stackFrameAt (sp0 - 752#64) 272 ∗ ((sp0 - 48#64) ↦₆₄ v0) ∗
     ((sp0 - 40#64) ↦₆₄ v1) ∗ ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
     ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5)) ⊢ stackFrameAt sp0 1024 := by
  rw [stackFrameAt_1024_split_48_704 sp0]; cells_unfold; sep_frame

private theorem procPreserved_of_bl_pre {s sf : State} {lrVal pcVal : BitVec 64}
    (h : MallocngProcPreserved ((s.writeReg64 (.gpr 30#5) lrVal).setPC pcVal) sf) : MallocngProcPreserved s sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   by simpa [sigActions_setPC, sigActions_writeReg64] using h.2.2.2.2.2.2⟩

private def callocStackSaved (sp0 : BitVec 64) (s0 : State) (v2 v3 : BitVec 64) : SepProp :=
  stackFrameAt (sp0 - 48#64) 704 ∗ stackFrameAt (sp0 - 752#64) 272 ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3)

private theorem calloc_epilogue_ret [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b) (sp0 retVal : BitVec 64) (Rest : SepProp) (s0 s : State)
    {v2 v3 : BitVec 64} (hpc : s.pc = b + 0xb4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = retVal) (hcs : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s (Rest ∗ callocStackSaved sp0 s0 v2 v3)
      (fun sf P_f => (P_f ⊢ Rest ∗ stackFrameAt sp0 1024) ∧ sf.readReg64 .x0 = retVal ∧
        MallocngProcPreserved s sf ∧ sf.brk = s.brk ∧ sf.mem = s.mem ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have ha16 : sp0 - 48#64 + 16#64 = sp0 - 32#64 := by bv_arith
  have ha24 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have ha8 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have ha48 : sp0 - 48#64 + 48#64 = sp0 := by bv_arith
  dsimp only [callocStackSaved]; wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    ⟨sepConj_mono_right (repack_stackFrame_1024 sp0 _ _ _ _ _ _), by simp [arm64_norm],
     ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [arm64_norm, hsp0], ?_⟩
  obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs
  exact ⟨by simp [arm64_norm], by simp [arm64_norm],
    by simpa [arm64_norm] using h21, by simpa [arm64_norm] using h22,
    by simpa [arm64_norm] using h23, by simpa [arm64_norm] using h24,
    by simpa [arm64_norm] using h25, by simpa [arm64_norm] using h26,
    by simpa [arm64_norm] using h27, by simpa [arm64_norm] using h28,
    by simp [arm64_norm], by simpa [calleeSavedVRegs] using hv⟩

private theorem calloc_overflow_exit [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b) (γ : GhostName) (tp brkStart sp0 : BitVec 64)
    (bud : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)) (s0 s1 : State) {v2 v3 : BitVec 64}
    (hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem)
    (hpc1 : s1.pc = b + 0x98#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hproc01 : MallocngProcPreserved s0 s1) (hbrk01 : s1.brk = s0.brk)
    (hperm01 : s1.mem.perm = s0.mem.perm) (hcs01 : CalleeSaved21_28 s0 s1)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart) :
    let P1 := mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗ callocStackSaved sp0 s0 v2 v3
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s1 P1
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨
          (⌜sf.readReg64 .x0 = 0#64 ∧ MallocngCallAccounting 16 (MallocngTightStepBound 0 bud.peakCount) s0 sf⌝ ∗
           MallocngPostEnv mallocngIface γ maddrs tp brkStart bud ivs0 s0 sf ∗ stackFrameAt sp0 1024) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  intro P1; have _ := hb
  have hspAl1 : s1.spAligned = true := by
    rw [State.spAligned, hsp1]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have htp1 : s1.tpidrEl0 = tp := hproc01.2.2.1.trans htp0
  have hSplitHeap : P1 = (∃∗ errnoVal : BitVec 32,
      ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ mallocngIface.MallocngCore γ maddrs brkStart s0.brk bud ivs0 ∗
      ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ callocStackSaved sp0 s0 v2 v3) := by
    dsimp only [P1]; rw [mallocngHeap_split_runtime]; unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact congrArg sepExists (funext fun _ => by ac_rfl)
  rw [hSplitHeap]
  apply SepWP.exists_elim; intro errnoVal
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b02.rebase b (fun _ => none))
  rw [at_bl_target hb 0 152#64] at herr
  wp_call herr
  have hproc12 : MallocngProcPreserved s1 sf := procPreserved_of_bl_pre ‹MallocngProcPreserved _ sf›
  have h_x0 : sf.readReg64 (.gpr 0#5) = tp - 0xa4#64 := htp1 ▸ ‹sf.readReg64 (.gpr 0#5) = _›
  have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem := ‹VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem›
  have h_sp : sf.sp = sp0 - 48#64 := ‹sf.sp = s1.sp›.trans hsp1
  have h_brk : sf.brk = s1.brk := ‹sf.brk = s1.brk›
  have h_perm : sf.mem.perm = s1.mem.perm := ‹sf.mem.perm = s1.mem.perm›
  wp_step; wp_step; wp_str32_cl m3 hm3 hcl2 _hcl3; wp_step
  let Rest := ((tp - 0xa4#64) ↦₃₂ 12#32) ∗ mallocngIface.MallocngCore γ maddrs brkStart s0.brk bud ivs0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  have hPreEq : (((tp - 0xa4#64) ↦₃₂ 12#32) ∗ mallocngIface.MallocngCore γ maddrs brkStart s0.brk bud ivs0 ∗
      ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ callocStackSaved sp0 s0 v2 v3) =
      (Rest ∗ callocStackSaved sp0 s0 v2 v3) := by dsimp only [Rest]; ac_rfl
  rw [hPreEq]
  have hcs03 : CalleeSaved21_28 s0 _ :=
    ⟨by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 21#5) = _›.trans hcs01.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 22#5) = _›.trans hcs01.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 23#5) = _›.trans hcs01.2.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 24#5) = _›.trans hcs01.2.2.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 25#5) = _›.trans hcs01.2.2.2.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 26#5) = _›.trans hcs01.2.2.2.2.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 27#5) = _›.trans hcs01.2.2.2.2.2.2.1,
     by simpa [arm64_norm] using ‹sf.readReg64 (.gpr 28#5) = _›.trans hcs01.2.2.2.2.2.2.2.1,
     by simpa [calleeSavedVRegs] using hvregs.trans hcs01.2.2.2.2.2.2.2.2⟩
  refine SepWP.mono (calloc_epilogue_ret hb sp0 0#64 Rest s0 _
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf])
    (by simp [arm64_norm, h_sp]) hsp0 hspAl0 (by simp [arm64_norm]) hcs03) ?_
  rintro s_end P_f _ _ ⟨hent, hx0_f, hproc3f, hbrk3f, hmem3f, hsp_f, hcs_f⟩
  have hproc23 : MallocngProcPreserved sf _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  have hproc0f : MallocngProcPreserved s0 s_end :=
    procPreserved_trans hproc01 (procPreserved_trans hproc12 (procPreserved_trans hproc23 hproc3f))
  have hbrk0f : s_end.brk = s0.brk := hbrk3f.trans (h_brk.trans hbrk01)
  have hperm0f : s_end.mem.perm = s0.mem.perm := by rw [hmem3f]; exact hm3.trans (h_perm.trans hperm01)
  have hAcc : MallocngCallAccounting 16 (MallocngTightStepBound 0 bud.peakCount) s0 s_end :=
    ⟨hproc0f, mappedDelta_congr_perm rfl hperm0f (MallocngMappedDelta.refl 16 _ _)⟩
  have hNoOrph : MallocngNoOrphanMappings ivs0 ivs0 s0.mem s_end.mem :=
    noOrphanMappings_congr_perm rfl hperm0f (mallocngNoOrphanMappings_refl _ _)
  refine ⟨fun R hsat => ?_, hsp_f, hcs_f⟩
  refine Satisfies.mono (sepConj_mono_left (Entails.trans hent ?_)) hsat
  refine Entails.pure_right ⟨hx0_f, hAcc⟩ (sepConj_mono_left ?_)
  dsimp only [Rest, MallocngPostEnv, MallocngEnv]
  refine Entails.sepExists_right ivs0 (Entails.pure_right hNoOrph
    (Entails.pure_right ⟨hproc0f.2.2.1.trans htp0, hproc0f.2.2.2.1.trans hbrks0⟩ ?_))
  rw [hbrk0f, mallocngHeap_split_runtime]; unfold MallocngRuntime; sep_frame

private theorem entails_withCL_pre {P : SepProp} {φ ψ : Prop} (hφ : φ) (hψ : ψ) :
    P ⊢ (⌜φ⌝ ∗ P) ∗ ⌜ψ⌝ := by
  rw [sepConj_comm]; exact Entails.pure_right hψ (Entails.pure_right hφ (Entails.refl P))

private theorem calloc_tail_memset [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b) (sp0 p : BitVec 64) (bs_pref : List (BitVec 8)) (k : Nat)
    (Rest : SepProp) (s0 s : State) {v2 v3 : BitVec 64}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + 0xc8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = p) (hx19 : (s.readReg64 .x19).toNat = k)
    (hbsLen : bs_pref.length = k) (hk48 : k ≤ 2 ^ 48) (hcs : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((p ↦ₛ bs_pref) ∗ Rest ∗ callocStackSaved sp0 s0 v2 v3)
      (fun sf P_f =>
        (P_f ⊢ (p ↦ₛ List.replicate k 0#8) ∗ Rest ∗ stackFrameAt sp0 1024) ∧
        sf.readReg64 .x0 = p ∧ MallocngProcPreserved s sf ∧ sf.brk = s.brk ∧
        sf.mem.perm = s.mem.perm ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have ha16 : sp0 - 48#64 + 16#64 = sp0 - 32#64 := by bv_arith
  have ha24 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have ha8 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have ha48 : sp0 - 48#64 + 48#64 = sp0 := by bv_arith
  dsimp only [callocStackSaved]; wp_steps
  let Frame := Rest ∗ callocStackSaved sp0 s0 v2 v3
  have hmemset := placed_memsetZero_perm_ok (P := blkPC_b02.rebase b (fun _ => none)) p bs_pref k hbsLen hk48
  rw [at_bl_target hb 21 220#64] at hmemset
  refine SepWP.call_subroutine_frame (F := Frame) (x := ()) (ret_pc := s0.readReg64 .lr) hmemset
    rfl (by simp [arm64_norm, hrun]) (by simpa [State.spAligned, arm64_norm, hsp0] using hspAl0)
    (by simp [arm64_norm])
    (fun R' hm => by
      change _ ⊨ ((p ↦ₛ bs_pref) ∗ Frame) ∗ R' at hm; rw [sepConj_assoc] at hm
      refine Satisfies.mono (sepConj_mono_left ?_) hm; dsimp only [withCL]
      exact entails_withCL_pre
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simpa [arm64_norm] using hx19⟩ hcl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  dsimp only [withCL]; rw [sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hproc_tf, hbrk_tf, hperm_tf, hx0_f⟩
  have hproc_sf : MallocngProcPreserved s sf :=
    ⟨hproc_tf.1, hproc_tf.2.1, hproc_tf.2.2.1, hproc_tf.2.2.2.1,
     hproc_tf.2.2.2.2.1, hproc_tf.2.2.2.2.2.1,
     by simpa [sigActions_setPC, sigActions_writeReg64] using hproc_tf.2.2.2.2.2.2⟩
  refine SepWP.done hpc_f hrun_f ⟨?_, hx0_f, hproc_sf, hbrk_tf, hperm_tf,
    by simpa [arm64_norm, hsp0] using hsp_f, ?_⟩
  · dsimp only [Frame, callocStackSaved]
    exact sepConj_mono_right (Entails.pure_left fun _ =>
      sepConj_mono_right (repack_stackFrame_1024 sp0 _ _ _ _ _ _))
  · refine calleeSavedPreserved_trans ?_ hcs_f
    obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs
    exact ⟨by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using h21, by simpa [arm64_norm] using h22,
      by simpa [arm64_norm] using h23, by simpa [arm64_norm] using h24,
      by simpa [arm64_norm] using h25, by simpa [arm64_norm] using h26,
      by simpa [arm64_norm] using h27, by simpa [arm64_norm] using h28,
      by simp [arm64_norm], by simpa [calleeSavedVRegs] using hv⟩

private def CalleeSaved22_28 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem calloc_memset_to_5c [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b)
    (sp0 p q_prev : BitVec 64) (bs_chunk : List (BitVec 8)) (len : Nat)
    (Rest : SepProp) (s0 s : State)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + 0x50#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = q_prev + BitVec.ofNat 64 len)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 len)
    (hx20 : s.readReg64 .x20 = p) (hx21 : s.readReg64 .x21 = 4096#64)
    (hbsLen : bs_chunk.length = len) (hlen : len ≤ 4096)
    (hcs : CalleeSaved22_28 s0 s) :
    SepWP (blkPC_b02.rebase b (fun _ => none)) (b + 0x5c#64) s
      ((q_prev ↦ₛ bs_chunk) ∗ Rest)
      (fun s' P' =>
        (P' ⊢ (q_prev ↦ₛ List.replicate len 0#8) ∗ Rest) ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl s'.mem ∧
        s'.readReg64 .x0 = q_prev ∧ s'.readReg64 .x20 = p ∧ s'.readReg64 .x21 = 4096#64 ∧
        s'.sp = sp0 - 48#64 ∧ CalleeSaved22_28 s0 s' ∧
        MallocngProcPreserved s s' ∧ s'.brk = s.brk ∧ s'.mem.perm = s.mem.perm)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have hsub : q_prev + BitVec.ofNat 64 len - BitVec.ofNat 64 len = q_prev := by bv_arith
  have hlenNat : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  wp_step; wp_step
  have hmemset := placed_memsetZero_perm_ok (P := blkPC_b02.rebase b (fun _ => none))
    q_prev bs_chunk len hbsLen (by omega)
  rw [at_bl_target hb 21 88#64] at hmemset
  wp_call hmemset
  have hproc_ss' : MallocngProcPreserved s sf := by
    have hp := procPreserved_of_bl_pre ‹MallocngProcPreserved _ sf›
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
      by simpa [sigActions_advancePC, sigActions_writeReg32, sigActions_writeReg64] using hp.2.2.2.2.2.2⟩
  refine SepWP.done hpc_sf hrun_sf
    ⟨Entails.refl _, hpost, ‹sf.readReg64 (.gpr 0#5) = q_prev›,
     ‹sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)›.trans hx20,
     ‹sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)›.trans hx21,
     hsp_sf.trans hsp,
     ⟨‹sf.readReg64 (.gpr 22#5) = _›.trans hcs.1,
      ‹sf.readReg64 (.gpr 23#5) = _›.trans hcs.2.1,
      ‹sf.readReg64 (.gpr 24#5) = _›.trans hcs.2.2.1,
      ‹sf.readReg64 (.gpr 25#5) = _›.trans hcs.2.2.2.1,
      ‹sf.readReg64 (.gpr 26#5) = _›.trans hcs.2.2.2.2.1,
      ‹sf.readReg64 (.gpr 27#5) = _›.trans hcs.2.2.2.2.2.1,
      ‹sf.readReg64 (.gpr 28#5) = _›.trans hcs.2.2.2.2.2.2.1,
      hvregs.trans hcs.2.2.2.2.2.2.2⟩,
     hproc_ss', ‹sf.brk = s.brk›, ‹sf.mem.perm = s.mem.perm›⟩

private theorem ofNat64_add (m n : Nat) :
    BitVec.ofNat 64 (m + n) = BitVec.ofNat 64 m + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

private theorem or_eq_zero_iff_64 (a b : BitVec 64) :
    (a ||| b) = 0#64 ↔ a = 0#64 ∧ b = 0#64 := by
  constructor
  · intro h; constructor <;> (revert h; bv_bits)
  · rintro ⟨rfl, rfl⟩; rfl

private theorem pointsTo64_pair_zero_eq_replicate16 (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64)) = (a ↦ₛ List.replicate 16 0#8) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
    show List.replicate 16 0#8 = unpack64 0#64 ++ unpack64 0#64 by decide,
    pointsToBytes_append, unpack64_length]

private theorem calloc_inner_scan [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b)
    (sp0 p q_prev : BitVec 64) (s0 : State) :
    ∀ (j : Nat) (bs_rem : List (BitVec 8)) (Rest : SepProp) (s : State),
    j < 256 →
    bs_rem.length = 16 * (j + 1) →
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem →
    s.pc = b + 0x74#64 → s.status = .Running →
    s.sp = sp0 - 48#64 → s0.sp = sp0 → s0.spAligned = true →
    s.readReg64 .x0 = q_prev →
    s.readReg64 .x19 = q_prev + BitVec.ofNat 64 (16 * (j + 1)) →
    s.readReg64 .x4 = 0#64 - q_prev →
    s.readReg64 .x20 = p → s.readReg64 .x21 = 4096#64 →
    CalleeSaved22_28 s0 s →
    SepWP (blkPC_b02.rebase b (fun _ => none)) (b + 0x5c#64) s
      ((q_prev ↦ₛ bs_rem) ∗ Rest)
      (fun s' P' =>
        (P' ⊢ (q_prev ↦ₛ List.replicate (16 * (j + 1)) 0#8) ∗ Rest) ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl s'.mem ∧
        s'.readReg64 .x0 = q_prev ∧ s'.readReg64 .x20 = p ∧ s'.readReg64 .x21 = 4096#64 ∧
        s'.sp = sp0 - 48#64 ∧ CalleeSaved22_28 s0 s' ∧
        MallocngProcPreserved s s' ∧ s'.brk = s.brk ∧ s'.mem.perm = s.mem.perm)
      (fun _ => ⌜False⌝) := by
  have _ := hb
  intro j
  induction j with
  | zero =>
    intro bs_rem Rest s _hj hbsLen hcl hpc hrun hsp hsp0 hspAl0 hx0 hx19 hx4 hx20 hx21 hcs
    have hspAl : s.spAligned = true := by
      rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
    obtain ⟨w5, w3, _, hpair_sep⟩ := exists_unpack64_of_length_16 (bs := bs_rem) (by simpa using hbsLen)
    have hSplit : (q_prev ↦ₛ bs_rem) = ((q_prev ↦₆₄ w5) ∗ ((q_prev + 8#64) ↦₆₄ w3)) := hpair_sep q_prev
    have ha_ldp : q_prev + 16#64 + (-16#64) = q_prev := by bv_arith
    simp only [Nat.zero_add, Nat.mul_one] at hx19 hbsLen ⊢
    change s.readReg64 .x19 = q_prev + 16#64 at hx19
    rw [hSplit, sepConj_assoc]
    wp_step; wp_step; wp_step
    by_cases horr : (w3 ||| w5) = 0#64
    · obtain ⟨hw3, hw5⟩ := (or_eq_zero_iff_64 w3 w5).mp horr; subst hw3 hw5
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      rw [← sepConj_assoc, pointsTo64_pair_zero_eq_replicate16]
      have hNil : ((q_prev ↦ₛ List.replicate 16 0#8) ∗ Rest) =
          ((q_prev ↦ₛ ([] : List (BitVec 8))) ∗ ((q_prev ↦ₛ List.replicate 16 0#8) ∗ Rest)) := by
        rw [pointsToBytes_nil, emp_sepConj]
      rw [hNil]
      refine SepWP.mono (calloc_memset_to_5c hb sp0 p q_prev [] 0 ((q_prev ↦ₛ List.replicate 16 0#8) ∗ Rest) s0 _
        hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm, hx20]) (by simp [arm64_norm, hx21]) rfl (by omega)
        ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
      rintro s' P' _ _ ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', hp, hbrk', hperm'⟩
      exact ⟨Entails.trans hent (by rw [List.replicate_zero, pointsToBytes_nil, emp_sepConj]; exact Entails.refl _),
        hcl', hx0', hx20', hx21', hsp', hcs', ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
         by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hp.2.2.2.2.2.2⟩, hbrk', hperm'⟩
    · have horr_imp : w3 = 0#64 → w5 ≠ 0#64 := fun h3 h5 => horr (by rw [h3, h5]; rfl)
      wp_step; rw [← sepConj_assoc, ← hSplit]
      refine SepWP.mono (calloc_memset_to_5c hb sp0 p q_prev bs_rem 16 Rest s0 _
        hcl (by simp [arm64_norm]; exact horr_imp) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simpa [arm64_norm] using hx19) (by simp [arm64_norm]; bv_arith)
        (by simp [arm64_norm, hx20]) (by simp [arm64_norm, hx21]) hbsLen (by omega)
        ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
      rintro s' P' _ _ ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', hp, hbrk', hperm'⟩
      exact ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
        by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hp.2.2.2.2.2.2⟩, hbrk', hperm'⟩
  | succ j' ih =>
    intro bs_rem Rest s hj hbsLen hcl hpc hrun hsp hsp0 hspAl0 hx0 hx19 hx4 hx20 hx21 hcs
    have hspAl : s.spAligned = true := by
      rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
    let m := 16 * (j' + 1); let a_pair := q_prev + BitVec.ofNat 64 m
    let bs_init := bs_rem.take m; let bs_pair := bs_rem.drop m
    have hbsInit : bs_init.length = m := by dsimp only [bs_init, m]; rw [List.length_take]; omega
    have hbsPair : bs_pair.length = 16 := by dsimp only [bs_pair, m]; rw [List.length_drop]; omega
    obtain ⟨w5, w3, _, hpair_sep⟩ := exists_unpack64_of_length_16 hbsPair
    have hSplit : (q_prev ↦ₛ bs_rem) = ((q_prev ↦ₛ bs_init) ∗ (a_pair ↦₆₄ w5) ∗ ((a_pair + 8#64) ↦₆₄ w3)) := by
      conv => lhs; rw [← List.take_append_drop m bs_rem]
      change (q_prev ↦ₛ (bs_init ++ bs_pair)) = _; rw [pointsToBytes_append, hbsInit, hpair_sep a_pair]
    have hm16 : BitVec.ofNat 64 (16 * (j' + 1 + 1)) = BitVec.ofNat 64 m + 16#64 := by
      rw [show 16 * (j' + 1 + 1) = m + 16 by dsimp only [m]; omega, ofNat64_add]
    have ha_sub : q_prev + (BitVec.ofNat 64 m + 16#64) - 16#64 = a_pair := by dsimp only [a_pair]; bv_arith
    rw [hSplit, sepConj_assoc, sepConj_assoc]; wp_step; wp_step; wp_step
    by_cases horr : (w3 ||| w5) = 0#64
    · obtain ⟨hw3, hw5⟩ := (or_eq_zero_iff_64 w3 w5).mp horr; subst hw3 hw5
      have hd0 : BitVec.ofNat 64 m ≠ 0#64 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [m]; omega)] at this
        simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this; dsimp only [m] at this; omega
      have hne : q_prev ≠ a_pair := by dsimp only [a_pair]; intro h; apply hd0; bv_omega
      have hne' : a_pair ≠ q_prev := Ne.symm hne
      wp_step; wp_step; wp_step; wp_step
      have hRearr : ((q_prev ↦ₛ bs_init) ∗ (a_pair ↦₆₄ 0#64) ∗ ((a_pair + 8#64) ↦₆₄ 0#64) ∗ Rest) =
          ((q_prev ↦ₛ bs_init) ∗ ((a_pair ↦ₛ List.replicate 16 0#8) ∗ Rest)) := by
        rw [← sepConj_assoc (a_pair ↦₆₄ 0#64), pointsTo64_pair_zero_eq_replicate16]
      rw [hRearr]
      refine SepWP.mono (ih bs_init ((a_pair ↦ₛ List.replicate 16 0#8) ∗ Rest) _
        (by omega) hbsInit hcl (by simp [arm64_norm, hne]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simpa [arm64_norm] using hx0) (by simp only [arm64_norm]; rfl)
        (by simpa [arm64_norm] using hx4) (by simp [arm64_norm, hx20]) (by simp [arm64_norm, hx21])
        ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
      rintro s' P' _ _ ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', hp, hbrk', hperm'⟩
      have hMerge : ((q_prev ↦ₛ List.replicate m 0#8) ∗ ((a_pair ↦ₛ List.replicate 16 0#8) ∗ Rest)) ⊢
          (q_prev ↦ₛ List.replicate (16 * (j' + 1 + 1)) 0#8) ∗ Rest := by
        dsimp only [a_pair]
        rw [← sepConj_assoc, ← pointsToBytes_replicate_zero_split q_prev m 16, show m + 16 = 16 * (j' + 1 + 1) by dsimp only [m]; omega]
        exact Entails.refl _
      exact ⟨Entails.trans hent hMerge, hcl', hx0', hx20', hx21', hsp', hcs',
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, by simpa [arm64_norm] using hp.2.2.2.2.2.2⟩, hbrk', hperm'⟩
    · have horr_imp : w3 = 0#64 → w5 ≠ 0#64 := fun h3 h5 => horr (by rw [h3, h5]; rfl)
      wp_step; rw [← sepConj_assoc, ← sepConj_assoc, sepConj_assoc (q_prev ↦ₛ bs_init), ← hSplit]
      refine SepWP.mono (calloc_memset_to_5c hb sp0 p q_prev bs_rem (16 * (j' + 1 + 1)) Rest s0 _
        hcl (by simp [arm64_norm]; exact horr_imp) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simpa [arm64_norm, hm16] using hx19) (by simp [arm64_norm]; bv_arith)
        (by simp [arm64_norm, hx20]) (by simp [arm64_norm, hx21]) hbsLen (by omega)
        ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
      rintro s' P' _ _ ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', hp, hbrk', hperm'⟩
      exact ⟨hent, hcl', hx0', hx20', hx21', hsp', hcs', ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
        by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hp.2.2.2.2.2.2⟩, hbrk', hperm'⟩

set_option maxRecDepth 20000 in
private theorem calloc_page_loop [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b) (sp0 p v3 : BitVec 64) (s0 : State) :
    ∀ (fuel k : Nat) (bs_pref : List (BitVec 8)) (Rest : SepProp) (s : State),
    k ≤ 4096 * fuel + 4095 → k < 2 ^ 64 → bs_pref.length = k →
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem → s.pc = b + 0x5c#64 → s.status = .Running →
    s.sp = sp0 - 48#64 → s0.sp = sp0 → s0.spAligned = true →
    s.readReg64 .x0 = p + BitVec.ofNat 64 k → s.readReg64 .x20 = p → s.readReg64 .x21 = 4096#64 →
    CalleeSaved22_28 s0 s →
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((p ↦ₛ bs_pref) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3)
      (fun sf P_f => (P_f ⊢ (p ↦ₛ List.replicate k 0#8) ∗ Rest ∗ stackFrameAt sp0 1024) ∧
        sf.readReg64 .x0 = p ∧ MallocngProcPreserved s sf ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜False⌝) := by
  have _ := hb; have ha32 : sp0 - 48#64 + 32#64 = sp0 - 16#64 := by bv_arith
  intro fuel; induction fuel with
  | zero =>
    intro k bs_pref Rest s hkFuel hk64 hbsLen hcl hpc hrun hsp hsp0 hspAl0 hx0 hx20 hx21 hcs
    have hspAl : s.spAligned = true := by
      rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
    have hk : k ≤ 4095 := by omega
    have hkNat : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
    have hx19_sub : p + BitVec.ofNat 64 k - p = BitVec.ofNat 64 k := by bv_arith
    have hle_bv : BitVec.ofNat 64 k ≤ 4095#64 := by show (BitVec.ofNat 64 k).toNat ≤ 4095; rw [hkNat]; exact hk
    have hule_bv : BitVec.ule (BitVec.ofNat 64 k) 4095#64 = true := by simp [BitVec.ule_iff_toNat_le, hkNat, hk]
    dsimp only [callocStackSaved]; wp_step; wp_step; wp_step; wp_step
    refine SepWP.mono (calloc_tail_memset hb sp0 p bs_pref k Rest s0 _
      hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
      (by simpa [arm64_norm] using hx20) (by simp [arm64_norm, hkNat]) hbsLen (by omega)
      ⟨by simp [arm64_norm], by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1],
       by simp [arm64_norm, hcs.2.2.1], by simp [arm64_norm, hcs.2.2.2.1],
       by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
       by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
    rintro sf P_f _ _ ⟨hent, hx0_f, hp, hbrk_f, hperm_f, hsp_f, hcs_f⟩
    exact ⟨hent, hx0_f, ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
      by simpa [arm64_norm] using hp.2.2.2.2.2.2⟩, hbrk_f, hperm_f, hsp_f, hcs_f⟩
  | succ fuel' ih =>
    intro k bs_pref Rest s hkFuel hk64 hbsLen hcl hpc hrun hsp hsp0 hspAl0 hx0 hx20 hx21 hcs
    by_cases hk : k ≤ 4095
    · exact ih k bs_pref Rest s (by omega) hk64 hbsLen hcl hpc hrun hsp hsp0 hspAl0 hx0 hx20 hx21 hcs
    · have hspAl : s.spAligned = true := by
        rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
      have hkNat : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
      have hx19_sub : p + BitVec.ofNat 64 k - p = BitVec.ofNat 64 k := by bv_arith
      have hgt_bv : ¬(BitVec.ofNat 64 k ≤ 4095#64) := by show ¬((BitVec.ofNat 64 k).toNat ≤ 4095); rw [hkNat]; omega
      have hnule_bv : BitVec.ule (BitVec.ofNat 64 k) 4095#64 = false :=
        Bool.eq_false_iff.mpr fun h => by rw [BitVec.ule_iff_toNat_le, hkNat] at h; change k ≤ 4095 at h; omega
      wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      let k' := k - 4096; let q_prev := p + BitVec.ofNat 64 k'
      let bs_head := bs_pref.take k'; let bs_page := bs_pref.drop k'
      have hbsHead : bs_head.length = k' := by dsimp only [bs_head, k']; rw [List.length_take]; omega
      have hbsPage : bs_page.length = 16 * (255 + 1) := by dsimp only [bs_page, k']; rw [List.length_drop]; omega
      have hk_add : BitVec.ofNat 64 k = BitVec.ofNat 64 k' + 4096#64 := by
        rw [show k = k' + 4096 by dsimp only [k']; omega, ofNat64_add]
      have hSplit : ((p ↦ₛ bs_pref) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3) =
          ((q_prev ↦ₛ bs_page) ∗ ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3)) := by
        conv => lhs; arg 1; rw [← List.take_append_drop k' bs_pref]
        change ((p ↦ₛ (bs_head ++ bs_page)) ∗ _) = _
        rw [pointsToBytes_append, hbsHead]; dsimp only [q_prev]; rw [sepConj_comm (p ↦ₛ bs_head), sepConj_assoc]
      rw [hSplit]
      refine SepWP.seq
        (calloc_inner_scan hb sp0 p q_prev s0 255 bs_page
          ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3) _
          (by omega) hbsPage hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
          (by simp [arm64_norm, hk_add]; dsimp only [q_prev]; bv_arith)
          (by simp [arm64_norm, hk_add]; dsimp only [q_prev]; bv_arith)
          (by simp [arm64_norm, hk_add]; dsimp only [q_prev]; bv_arith)
          (by simpa [arm64_norm] using hx20) (by simpa [arm64_norm] using hx21)
          ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
           by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
           by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2⟩) ?_
      rintro sm Pm hpc_m hrun_m ⟨hent_m, hcl_m, hx0_m, hx20_m, hx21_m, hsp_m, hcs_m, hp_m, hbrk_m, hperm_m⟩
      rw [show 16 * (255 + 1) = 4096 by omega] at hent_m
      have hRearrM : ((q_prev ↦ₛ List.replicate 4096 0#8) ∗
          ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3)) ⊢
          (p ↦ₛ bs_head) ∗ ((q_prev ↦ₛ List.replicate 4096 0#8) ∗ Rest) ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3 := by
        rw [← sepConj_assoc, sepConj_comm _ (p ↦ₛ bs_head), sepConj_assoc, ← sepConj_assoc (q_prev ↦ₛ List.replicate 4096 0#8)]
        exact Entails.refl _
      apply SepWP.weaken_pre (Entails.trans hent_m hRearrM)
      refine SepWP.mono (ih k' bs_head ((q_prev ↦ₛ List.replicate 4096 0#8) ∗ Rest) sm
        (by dsimp only [k']; omega) (by dsimp only [k']; omega) hbsHead
        hcl_m hpc_m hrun_m hsp_m hsp0 hspAl0 hx0_m hx20_m hx21_m hcs_m) ?_
      rintro sf P_f _ _ ⟨hent_f, hx0_f, hp_f, hbrk_f, hperm_f, hsp_f, hcs_f⟩
      have hMergeF : ((p ↦ₛ List.replicate k' 0#8) ∗ ((q_prev ↦ₛ List.replicate 4096 0#8) ∗ Rest) ∗ stackFrameAt sp0 1024) ⊢
          (p ↦ₛ List.replicate k 0#8) ∗ Rest ∗ stackFrameAt sp0 1024 := by
        dsimp only [q_prev]
        rw [sepConj_assoc ((p + BitVec.ofNat 64 k') ↦ₛ List.replicate 4096 0#8),
            ← sepConj_assoc, ← pointsToBytes_replicate_zero_split p k' 4096, show k' + 4096 = k by dsimp only [k']; omega]
        exact Entails.refl _
      have hp_sm : MallocngProcPreserved s sm :=
        ⟨hp_m.1, hp_m.2.1, hp_m.2.2.1, hp_m.2.2.2.1, hp_m.2.2.2.2.1, hp_m.2.2.2.2.2.1, by simpa [arm64_norm] using hp_m.2.2.2.2.2.2⟩
      exact ⟨Entails.trans hent_f hMergeF, hx0_f, procPreserved_trans hp_sm hp_f,
        hbrk_f.trans hbrk_m, hperm_f.trans hperm_m, hsp_f, hcs_f⟩
private theorem and_4095_le (z : BitVec 64) : (z &&& 4095#64).toNat ≤ 4095 := by
  rw [BitVec.toNat_and]; change z.toNat &&& (2 ^ 12 - 1) ≤ 4095; rw [Nat.and_two_pow_sub_one_eq_mod]; omega

private theorem calloc_zero_nonmmapped [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 2 b) (sp0 p v2 v3 : BitVec 64) (bs : List (BitVec 8)) (total : Nat)
    (Rest : SepProp) (s0 s : State) (htot64 : total < 2 ^ 64) (hbsLen : bs.length = total)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) (hpc : s.pc = b + 0x38#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 total) (hx20 : s.readReg64 .x20 = p) (hcs : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      ((p ↦ₛ bs) ∗ Rest ∗ callocStackSaved sp0 s0 v2 v3)
      (fun sf P_f => (P_f ⊢ (p ↦ₛ List.replicate total 0#8) ∗ Rest ∗ stackFrameAt sp0 1024) ∧
        sf.readReg64 .x0 = p ∧ MallocngProcPreserved s sf ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜False⌝) := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have htotNat : (BitVec.ofNat 64 total).toNat = total := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htot64]
  have ha32 : sp0 - 48#64 + 32#64 = sp0 - 16#64 := by bv_arith
  simp only [Reg.x19] at hx19; simp only [Reg.x20] at hx20
  by_cases htot : total ≤ 4095
  · have hle_bv : BitVec.ofNat 64 total ≤ 4095#64 := by show (BitVec.ofNat 64 total).toNat ≤ 4095; rw [htotNat]; exact htot
    have hule_bv : BitVec.ule (BitVec.ofNat 64 total) 4095#64 = true := by simp [BitVec.ule_iff_toNat_le, htotNat, htot]
    wp_step; wp_step; dsimp only [callocStackSaved]
    refine SepWP.mono (calloc_tail_memset hb sp0 p bs total Rest s0 _
      hcl (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
      (by simpa [arm64_norm] using hx20) (by simp [arm64_norm, hx19, htotNat]) hbsLen (by omega)
      ⟨by simp [arm64_norm, hcs.1], by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1],
       by simp [arm64_norm, hcs.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
       by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.2.2.1],
       by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2.2⟩) ?_
    rintro sf P_f _ _ ⟨hent, hx0_f, hp, hbrk_f, hperm_f, hsp_f, hcs_f⟩
    exact ⟨hent, hx0_f, ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
      by simpa [arm64_norm] using hp.2.2.2.2.2.2⟩, hbrk_f, hperm_f, hsp_f, hcs_f⟩
  · have hgt_bv : ¬(BitVec.ofNat 64 total ≤ 4095#64) := by show ¬((BitVec.ofNat 64 total).toNat ≤ 4095); rw [htotNat]; omega
    have hnule_bv : BitVec.ule (BitVec.ofNat 64 total) 4095#64 = false :=
      Bool.eq_false_iff.mpr fun h => by rw [BitVec.ule_iff_toNat_le, htotNat] at h; change total ≤ 4095 at h; omega
    dsimp only [callocStackSaved]; wp_step; wp_step; wp_step; wp_str64_cl m1 hm1 hcl hcl1; rw [hcs.1]; wp_step; wp_step
    let z := p + BitVec.ofNat 64 total; let r := (z &&& 4095#64).toNat
    have hr4095 : r ≤ 4095 := and_4095_le z
    let k := total - r; let q_prev := p + BitVec.ofNat 64 k
    have hkr : k + r = total := by dsimp only [k]; omega
    have hr_bv : BitVec.ofNat 64 r = z &&& 4095#64 := by simp [r]
    have hq_add : q_prev + BitVec.ofNat 64 r = z := by dsimp only [q_prev, z]; rw [BitVec.add_assoc, ← ofNat64_add, hkr]
    let bs_head := bs.take k; let bs_tail := bs.drop k
    have hbsHead : bs_head.length = k := by dsimp only [bs_head, k]; rw [List.length_take]; omega
    have hbsTail : bs_tail.length = r := by dsimp only [bs_tail, k]; rw [List.length_drop]; omega
    have hSplit : ((p ↦ₛ bs) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3) =
        ((q_prev ↦ₛ bs_tail) ∗ ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3)) := by
      conv => lhs; arg 1; rw [← List.take_append_drop k bs]
      change ((p ↦ₛ (bs_head ++ bs_tail)) ∗ _) = _
      rw [pointsToBytes_append, hbsHead]; dsimp only [q_prev]; rw [sepConj_comm (p ↦ₛ bs_head), sepConj_assoc]
    change SepWP _ _ _ ((p ↦ₛ bs) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3) _ _; rw [hSplit]
    refine SepWP.seq
      (calloc_memset_to_5c hb sp0 p q_prev bs_tail r
        ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3) s0 _
        hcl1 (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simp [arm64_norm, hq_add]; rfl) (by simp [arm64_norm, hr_bv]; rfl)
        (by simpa [arm64_norm] using hx20) (by simp [arm64_norm]) hbsTail (by omega)
        ⟨by simp [arm64_norm, hcs.2.1], by simp [arm64_norm, hcs.2.2.1], by simp [arm64_norm, hcs.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.1],
         by simp [arm64_norm, hcs.2.2.2.2.2.2.1], by simp [arm64_norm, hcs.2.2.2.2.2.2.2.1],
         by simpa [calleeSavedVRegs] using hcs.2.2.2.2.2.2.2.2⟩) ?_
    rintro sm Pm hpc_m hrun_m ⟨hent_m, hcl_m, hx0_m, hx20_m, hx21_m, hsp_m, hcs_m, hp_m, hbrk_m, hperm_m⟩
    have hRearrM : ((q_prev ↦ₛ List.replicate r 0#8) ∗
        ((p ↦ₛ bs_head) ∗ Rest ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3)) ⊢
        (p ↦ₛ bs_head) ∗ ((q_prev ↦ₛ List.replicate r 0#8) ∗ Rest) ∗ callocStackSaved sp0 s0 (s0.readReg64 .x21) v3 := by
      rw [← sepConj_assoc, sepConj_comm _ (p ↦ₛ bs_head), sepConj_assoc, ← sepConj_assoc (q_prev ↦ₛ List.replicate r 0#8)]
      exact Entails.refl _
    apply SepWP.weaken_pre (Entails.trans hent_m hRearrM)
    refine SepWP.mono (calloc_page_loop hb sp0 p v3 s0 (k / 4096) k bs_head
      ((q_prev ↦ₛ List.replicate r 0#8) ∗ Rest) sm (by omega) (by dsimp only [k]; omega) hbsHead
      hcl_m hpc_m hrun_m hsp_m hsp0 hspAl0 hx0_m hx20_m hx21_m hcs_m) ?_
    rintro sf P_f _ _ ⟨hent_f, hx0_f, hp_f, hbrk_f, hperm_f, hsp_f, hcs_f⟩
    have hMergeF : ((p ↦ₛ List.replicate k 0#8) ∗ ((q_prev ↦ₛ List.replicate r 0#8) ∗ Rest) ∗ stackFrameAt sp0 1024) ⊢
        (p ↦ₛ List.replicate total 0#8) ∗ Rest ∗ stackFrameAt sp0 1024 := by
      dsimp only [q_prev]
      rw [sepConj_assoc ((p + BitVec.ofNat 64 k) ↦ₛ List.replicate r 0#8),
          ← sepConj_assoc, ← pointsToBytes_replicate_zero_split p k r, hkr]
      exact Entails.refl _
    have hp_sm : MallocngProcPreserved s sm :=
      ⟨hp_m.1, hp_m.2.1, hp_m.2.2.1, hp_m.2.2.2.1, hp_m.2.2.2.2.1, hp_m.2.2.2.2.2.1, by simpa [arm64_norm] using hp_m.2.2.2.2.2.2⟩
    exact ⟨Entails.trans hent_f hMergeF, hx0_f, procPreserved_trans hp_sm hp_f,
      hbrk_f.trans hbrk_m, hperm_f.trans (hperm_m.trans hm1), hsp_f, hcs_f⟩

private theorem sepWP_false_oom {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P post (fun _ => ⌜False⌝)) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  refine reaches_pc_seq (SepWP.to_reaches_pc h hm) ?_
    (fun _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro sf hpc hrun ⟨P_f, hmf, hpost⟩
  exact SepWP.to_reaches_pc (SepWP.done hpc hrun hpost) hmf

private theorem pack_mallocngPostEnv [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bf : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (st' : MallocngSt) (s0 sf : State)
    (hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem)
    (hCount : MallocngCountIvsWF bf (dynamicRootRegions st') st')
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart) :
    (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
     MallocngRuntime maddrs tp) ⊢ MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
  have hHeap : (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
      MallocngRuntime maddrs tp) ⊢ mallocngIface.MallocngHeap γ maddrs tp brkStart sf.brk bf (dynamicRootRegions st') := by
    rw [mallocngHeap_split_runtime]
    change _ ⊢ MallocngCoreImpl γ maddrs brkStart sf.brk bf (dynamicRootRegions st') ∗ _
    rw [MallocngCoreImpl_eq, ← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_right
      (Entails.sepExists_right st' (Entails.pure_right hCount (Entails.refl _))))
  unfold MallocngPostEnv MallocngEnv
  exact Entails.sepExists_right (dynamicRootRegions st')
    (Entails.pure_right hNoOrph (Entails.pure_right ⟨htp, hbrks⟩ hHeap))

private theorem postEnv_congr_pre_post [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bf : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (s0 s_bl sm sf : State)
    (hperm0 : s_bl.mem.perm = s0.mem.perm) (hmemf : sf.mem = sm.mem)
    (hbrkf : sf.brk = sm.brk) (htpf : sf.tpidrEl0 = sm.tpidrEl0)
    (hbrksf : sf.brkStart = sm.brkStart) :
    MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s_bl sm ⊢
      MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf := by
  unfold MallocngPostEnv MallocngEnv
  refine Entails.sepExists_mono fun ivsf => ?_
  rw [hbrkf, htpf, hbrksf]
  exact sepConj_mono_left (Entails.pure_mono fun h =>
    noOrphanMappings_congr_perm hperm0 (congrArg Memory.perm hmemf) h)

private theorem calloc_malloc_hit [MallocngMultiPlacement] {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    {b : BitVec 64} (hb : BlkBase 2 b) {oom : State → SepProp}
    (γ : GhostName) (tp brkStart sp0 p v2 v3 : BitVec 64)
    (bs : List (BitVec 8)) (total idx : Nat) (bud bf : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (st' : MallocngSt) (g' : GroupDesc) (s0 sm : State)
    (htot64 : total < 2 ^ 64) (hBlkWf : MallocngBlockWf p total) (hbsLen : bs.length = total)
    (hg' : g' ∈ st'.groups) (hIdx : idx < g'.slots.length)
    (hSlot : g'.slots[idx]'hIdx = .liveUser p total (max total MallocngMinBlockCost))
    (hZeroMmap : g'.isMmapped = true → bs = List.replicate total 0#8)
    (hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sm.mem)
    (hCount : MallocngCountIvsWF bf (dynamicRootRegions st') st')
    (hDelta0 : MallocngMappedDelta 16 (MallocngTightStepBound total bud.peakCount) s0.mem sm.mem)
    (hproc0m : MallocngProcPreserved s0 sm) (hclm : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hpcm : sm.pc = b + 0x24#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0m : sm.readReg64 .x0 = p) (hx19m : sm.readReg64 .x19 = BitVec.ofNat 64 total)
    (htpm : sm.tpidrEl0 = tp) (hbrksm : sm.brkStart = brkStart)
    (hcs0m : CalleeSaved21_28 s0 sm) :
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
      (MallocngRoTablesA maddrs ∗
       MallocngCoreStA γ maddrs brkStart sm.brk bf.liveCost bf.peakCost st' ∗
       MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ B γ p total 16 ∗ callocStackSaved sp0 s0 v2 v3)
      (fun sf P_f => (P_f ⊢ ⌜sf.readReg64 .x0 = p ∧ MallocngBlockWf p total ∧
           MallocngCallAccounting 16 (MallocngTightStepBound total bud.peakCount) s0 sf⌝ ∗
          B γ p total 16 ∗ (p ↦ₛ List.replicate total 0#8) ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗ stackFrameAt sp0 1024) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  have _ := hb; have hp_ne : p ≠ 0#64 := hBlkWf.1
  have hPageRep := pageOf_add_lo12Of maddrs.replaced
  conv => arg 4; arg 2; arg 1; unfold MallocngCoreStA MallocngCoreStInflightA
  wp_step; wp_step; wp_step; wp_step; wp_step
  conv => arg 4; arg 2; arg 1; change MallocngCoreStA γ maddrs brkStart sm.brk bf.liveCost bf.peakCost st'
  have hallz := placed_mallocAllzerop_ok (P := blkPC_b02.rebase b (fun _ => none))
    γ brkStart p bs total (max total MallocngMinBlockCost) bf.liveCost bf.peakCost idx st' g' (B γ p total 16) hg' hIdx hSlot
  rw [at_bl_target hb 10 172#64] at hallz; wp_call hallz
  have hproc_ma : MallocngProcPreserved sm sf := by
    have hp := procPreserved_of_bl_pre ‹MallocngProcPreserved _ sf›
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
      by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg32, sigActions_writeReg64] using hp.2.2.2.2.2.2⟩
  have hcs0_az : CalleeSaved21_28 s0 sf :=
    ⟨‹sf.readReg64 (.gpr 21#5) = _›.trans hcs0m.1, ‹sf.readReg64 (.gpr 22#5) = _›.trans hcs0m.2.1,
     ‹sf.readReg64 (.gpr 23#5) = _›.trans hcs0m.2.2.1, ‹sf.readReg64 (.gpr 24#5) = _›.trans hcs0m.2.2.2.1,
     ‹sf.readReg64 (.gpr 25#5) = _›.trans hcs0m.2.2.2.2.1, ‹sf.readReg64 (.gpr 26#5) = _›.trans hcs0m.2.2.2.2.2.1,
     ‹sf.readReg64 (.gpr 27#5) = _›.trans hcs0m.2.2.2.2.2.2.1, ‹sf.readReg64 (.gpr 28#5) = _›.trans hcs0m.2.2.2.2.2.2.2.1,
     hvregs.trans hcs0m.2.2.2.2.2.2.2.2⟩
  have hmem_az : sf.mem = sm.mem := ‹sf.mem = _›; have hbrk_az : sf.brk = sm.brk := ‹sf.brk = _›
  have hx0_az := ‹sf.readReg32 .x0 = if g'.isMmapped then 1#32 else 0#32›
  have hx19_az : sf.readReg64 .x19 = BitVec.ofNat 64 total :=
    ‹sf.readReg64 (.gpr 19#5) = _›.trans (by simpa [arm64_norm] using hx19m)
  have hx20_az : sf.readReg64 .x20 = p := ‹sf.readReg64 (.gpr 20#5) = _›
  let EnvRest := MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
    MallocngRuntime maddrs tp ∗ B γ p total 16
  cases hMmap : g'.isMmapped
  · simp only [hMmap, Bool.false_eq_true, ↓reduceIte] at hx0_az; wp_step
    have hPreEq : (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
        (p ↦ₛ bs) ∗ B γ p total 16 ∗ MallocngRuntime maddrs tp ∗ callocStackSaved sp0 s0 v2 v3) =
        ((p ↦ₛ bs) ∗ EnvRest ∗ callocStackSaved sp0 s0 v2 v3) := by dsimp only [EnvRest]; ac_rfl
    rw [hPreEq]
    refine SepWP.mono (sepWP_false_oom (calloc_zero_nonmmapped hb sp0 p v2 v3 bs total EnvRest s0 _
      htot64 hbsLen (by simpa [arm64_norm] using hpost)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf]) (by simp [arm64_norm, hsp_sf, hspm]) hsp0 hspAl0
      (by simpa [arm64_norm] using hx19_az) (by simpa [arm64_norm] using hx20_az)
      ⟨by simpa [arm64_norm] using hcs0_az.1, by simpa [arm64_norm] using hcs0_az.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.2.2.1,
       by simpa [calleeSavedVRegs] using hcs0_az.2.2.2.2.2.2.2.2⟩)) ?_
    rintro s_end P_end _ _ ⟨hent, hx0_end, hp_end, hbrk_end, hperm_end, hsp_end, hcs_end⟩
    have hp_az_end : MallocngProcPreserved sf s_end :=
      ⟨hp_end.1, hp_end.2.1, hp_end.2.2.1, hp_end.2.2.2.1, hp_end.2.2.2.2.1, hp_end.2.2.2.2.2.1,
       by simpa [arm64_norm] using hp_end.2.2.2.2.2.2⟩
    have hproc_all := procPreserved_trans hproc0m (procPreserved_trans hproc_ma hp_az_end)
    have hperm_m_end : s_end.mem.perm = sm.mem.perm := hperm_end.trans (congrArg Memory.perm hmem_az)
    have hAcc : MallocngCallAccounting 16 (MallocngTightStepBound total bud.peakCount) s0 s_end :=
      ⟨hproc_all, mappedDelta_congr_perm rfl hperm_m_end hDelta0⟩
    have hPost := pack_mallocngPostEnv γ tp brkStart bf ivs0 st' s0 s_end
      (noOrphanMappings_congr_perm rfl hperm_m_end hNoOrph0) hCount
      (hp_az_end.2.2.1.trans (hproc_ma.2.2.1.trans htpm)) (hp_az_end.2.2.2.1.trans (hproc_ma.2.2.2.1.trans hbrksm))
    have hbrk_sf : s_end.brk = sf.brk := hbrk_end
    refine ⟨Entails.trans hent (Entails.pure_right ⟨hx0_end, hBlkWf, hAcc⟩ ?_), hsp_end, hcs_end⟩
    dsimp only [EnvRest]; rw [← hbrk_sf]
    have hOrd : ((p ↦ₛ List.replicate total 0#8) ∗
        (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s_end.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp ∗ B γ p total 16) ∗ stackFrameAt sp0 1024) ⊢
        B γ p total 16 ∗ (p ↦ₛ List.replicate total 0#8) ∗
        (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s_end.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp) ∗ stackFrameAt sp0 1024 := Entails.of_eq (by ac_rfl)
    exact Entails.trans hOrd (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPost)))
  · simp only [hMmap, ↓reduceIte] at hx0_az; have hbsZ := hZeroMmap hMmap; subst hbsZ; wp_step
    let EpRest := B γ p total 16 ∗ (p ↦ₛ List.replicate total 0#8) ∗
      (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗ MallocngRuntime maddrs tp)
    have hPreEq : (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
        (p ↦ₛ List.replicate total 0#8) ∗ B γ p total 16 ∗ MallocngRuntime maddrs tp ∗
        callocStackSaved sp0 s0 v2 v3) = (EpRest ∗ callocStackSaved sp0 s0 v2 v3) := by dsimp only [EpRest]; ac_rfl
    rw [hPreEq]
    refine SepWP.mono (sepWP_false_oom (calloc_epilogue_ret hb sp0 p EpRest s0 _
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf])
      (by simp [arm64_norm, hsp_sf, hspm]) hsp0 hspAl0 (by simpa [arm64_norm] using hx20_az)
      ⟨by simpa [arm64_norm] using hcs0_az.1, by simpa [arm64_norm] using hcs0_az.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.1,
       by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.2.1, by simpa [arm64_norm] using hcs0_az.2.2.2.2.2.2.2.1,
       by simpa [calleeSavedVRegs] using hcs0_az.2.2.2.2.2.2.2.2⟩)) ?_
    rintro s_end P_end _ _ ⟨hent, hx0_end, hp_end, hbrk_end, hmem_end, hsp_end, hcs_end⟩
    have hp_az_end : MallocngProcPreserved sf s_end :=
      ⟨hp_end.1, hp_end.2.1, hp_end.2.2.1, hp_end.2.2.2.1, hp_end.2.2.2.2.1, hp_end.2.2.2.2.2.1,
       by simpa [arm64_norm] using hp_end.2.2.2.2.2.2⟩
    have hproc_all := procPreserved_trans hproc0m (procPreserved_trans hproc_ma hp_az_end)
    have hperm_m_end : s_end.mem.perm = sm.mem.perm := congrArg Memory.perm (hmem_end.trans hmem_az)
    have hAcc : MallocngCallAccounting 16 (MallocngTightStepBound total bud.peakCount) s0 s_end :=
      ⟨hproc_all, mappedDelta_congr_perm rfl hperm_m_end hDelta0⟩
    have hPost := pack_mallocngPostEnv γ tp brkStart bf ivs0 st' s0 s_end
      (noOrphanMappings_congr_perm rfl hperm_m_end hNoOrph0) hCount
      (hp_az_end.2.2.1.trans (hproc_ma.2.2.1.trans htpm)) (hp_az_end.2.2.2.1.trans (hproc_ma.2.2.2.1.trans hbrksm))
    have hbrk_sf : s_end.brk = sf.brk := hbrk_end
    refine ⟨Entails.trans hent (Entails.pure_right ⟨hx0_end, hBlkWf, hAcc⟩ ?_), hsp_end, hcs_end⟩
    dsimp only [EpRest]; rw [← hbrk_sf, sepConj_assoc, sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hPost))

private theorem calloc_no_ovf [MallocngMultiPlacement] {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    {b : BitVec 64} (hb : BlkBase 2 b) (hDefMalloc : DefaultMallocPlacedTokStmt B)
    (γ : GhostName) (nmemb size sp0 tp brkStart v2 v3 : BitVec 64)
    (bud : MallocngBudget) (ivs0 : List (BitVec 64 × Nat)) (R : SepProp) (s0 s : State)
    (hovf : nmemb.toNat * size.toNat < 2 ^ 64)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + 0x18#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 48#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = nmemb) (hx1 : s.readReg64 .x1 = size)
    (hproc0s : MallocngProcPreserved s0 s) (hbrks : s.brk = s0.brk) (hperms : s.mem.perm = s0.mem.perm)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart) (hcs0s : CalleeSaved21_28 s0 s) :
    let spec := ToBaseSpec.toSpec (mallocngCallocTokSpec B msvc γ maddrs) (mbase 2)
    let x := (nmemb, size, sp0, tp, brkStart, bud, ivs0)
    SepWP (blkPC_b02.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗ callocStackSaved sp0 s0 v2 v3)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (spec.onOom x s0) := by
  intro spec x; have _ := hb
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok total bud
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
  have hmul_eq : size * nmemb = BitVec.ofNat 64 total := by
    apply BitVec.eq_of_toNat_eq
    rw [mul_toNat_of_no_overflow hovf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hovf]
  have hmul_nat : (BitVec.ofNat 64 total).toNat = total := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hovf]
  wp_step; wp_step; wp_step
  let RestStack := stackFrameAt (sp0 - 752#64) 272 ∗
    ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((sp0 - 16#64) ↦₆₄ v2) ∗ ((sp0 - 8#64) ↦₆₄ v3)
  have hmal := call_placed_defaultMalloc_tok hDefMalloc (P := blkPC_b02.rebase b (fun _ => none))
    γ tp brkStart bud ivs0 total
  refine SepWP.call_subroutine_frame (F := RestStack) (x := ()) (ret_pc := b + 0x24#64) hmal
    (by simp only [arm64_norm]; exact (at_bl_target hb 4 32#64).symm)
    (by simp [arm64_norm, hrun]) (by simpa [State.spAligned, arm64_norm, hsp] using hspAl)
    (by simp [arm64_norm])
    (fun R' hm => by
      change _ ⊨ (mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗
        (stackFrameAt (sp0 - 48#64) 704 ∗ RestStack)) ∗ R' at hm
      rw [← sepConj_assoc _ (stackFrameAt (sp0 - 48#64) 704) RestStack,
          sepConj_assoc _ RestStack R'] at hm
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [libcMallocImplPlacedTokSpec, withCL, MallocngEnv, stackFrame]
      let s_bl := ((((s.writeReg64 (.gpr 19#5) (BitVec.ofNat 64 total)).writeReg64
        (.gpr 0#5) (BitVec.ofNat 64 total)).writeReg64 (.gpr 30#5) (b + 36#64)).setPC
        (b + 32#64 + (mbase 4 - mbase 2 - 32#64)))
      have hx0_bl : s_bl.readReg64 .x0 = BitVec.ofNat 64 total := by simp [s_bl, arm64_norm]
      have hsp_bl : s_bl.sp = sp0 - 48#64 := by simp [s_bl, arm64_norm, hsp]
      have hmem_bl : s_bl.mem = s.mem := by simp [s_bl, arm64_norm]
      have htp_bl : s_bl.tpidrEl0 = tp := by simpa [s_bl, arm64_norm] using hproc0s.2.2.1.trans htp0
      have hbrks_bl : s_bl.brkStart = brkStart := by simpa [s_bl, arm64_norm] using hproc0s.2.2.2.1.trans hbrks0
      have hbrk_bl : s_bl.brk = s0.brk := by simpa [s_bl, arm64_norm] using hbrks
      change _ ⊢ _ ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_bl.mem⌝
      rw [hx0_bl, hsp_bl, hmem_bl, htp_bl, hbrks_bl, hbrk_bl, stackFrameAt_eq_memRegion (sp0 - 48#64) 704]
      refine Entails.trans ?_ (entails_withCL_pre hmul_nat hcl)
      rw [sepConj_comm]
      exact sepConj_mono_right (Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)))
    (fun R' sf _ hp => by dsimp only [libcMallocImplPlacedTokSpec, withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [libcMallocImplPlacedTokSpec, withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho
      dsimp only [libcMallocImplPlacedTokSpec, withCL, spec, ToBaseSpec.toSpec, mallocngCallocTokSpec, x] at ho' ⊢
      rw [satisfies_pure_sepConj] at ho' ⊢
      exact ⟨MallocngTightOomCond.of_pre_perm hproc0s.1 hproc0s.2.1
        (by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hproc0s.2.2.2.2.2.2)
        hperms ho'.1, ho'.2⟩)
  dsimp only [libcMallocImplPlacedTokSpec, withCL, stackFrame]
  have hspm : sm.sp = sp0 - 48#64 := hsp_m.trans (by simp [arm64_norm, hsp])
  have hx19m : sm.readReg64 .x19 = BitVec.ofNat 64 total := hcs_m.1.trans (by simp [arm64_norm])
  have hcs0m : CalleeSaved21_28 s0 sm := calleeSaved21_28_trans
    ⟨by simpa [arm64_norm] using hcs0s.1, by simpa [arm64_norm] using hcs0s.2.1,
     by simpa [arm64_norm] using hcs0s.2.2.1, by simpa [arm64_norm] using hcs0s.2.2.2.1,
     by simpa [arm64_norm] using hcs0s.2.2.2.2.1, by simpa [arm64_norm] using hcs0s.2.2.2.2.2.1,
     by simpa [arm64_norm] using hcs0s.2.2.2.2.2.2.1, by simpa [arm64_norm] using hcs0s.2.2.2.2.2.2.2.1,
     by simpa [calleeSavedVRegs] using hcs0s.2.2.2.2.2.2.2.2⟩ hcs_m
  rw [sepConj_comm (_ ∗ _ ∗ _) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝, sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; intro hclm; apply SepWP.pure_elim; rintro ⟨hproc_bl_m, hDelta_bl⟩
  have hproc_s_m : MallocngProcPreserved s sm :=
    ⟨hproc_bl_m.1, hproc_bl_m.2.1, hproc_bl_m.2.2.1, hproc_bl_m.2.2.2.1, hproc_bl_m.2.2.2.2.1, hproc_bl_m.2.2.2.2.2.1,
     by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hproc_bl_m.2.2.2.2.2.2⟩
  have hproc0m : MallocngProcPreserved s0 sm := procPreserved_trans hproc0s hproc_s_m
  have hsp_bl_eq : ((((s.writeReg64 (.gpr 19#5) (BitVec.ofNat 64 total)).writeReg64
      (.gpr 0#5) (BitVec.ofNat 64 total)).writeReg64 (.gpr 30#5) (b + 36#64)).setPC
      (b + 32#64 + (mbase 4 - mbase 2 - 32#64))).sp = sp0 - 48#64 := by simp [arm64_norm, hsp]
  rw [hsp_bl_eq, ← stackFrameAt_eq_memRegion (sp0 - 48#64) 704]
  by_cases hMax : total ≤ MallocngMaxAllocSize
  · have hok : ok = true := decide_eq_true hMax
    rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn hMax)), sepConj_comm (stackFrameAt (sp0 - 48#64) 704), sepConj_assoc]
    simp only [sepExists_sepConj_left]
    apply SepWP.exists_elim; intro p; apply SepWP.exists_elim; intro bs; apply SepWP.exists_elim; intro st'
    rw [sepConj_assoc]; apply SepWP.pure_elim
    rintro ⟨hx0m, htpm, hbrksm, hBlkWf, hbsLen, hNoOrph_bl, hCount, g', hg', idx, hIdx, hSlot, _, hZeroMmap⟩
    have hPreHit : ((MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sm.brk bf.liveCost bf.peakCost st' ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ B γ p total 16) ∗
        (stackFrameAt (sp0 - 48#64) 704 ∗ RestStack)) =
        (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart sm.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ B γ p total 16 ∗
         callocStackSaved sp0 s0 v2 v3) := by dsimp only [callocStackSaved, RestStack]; ac_rfl
    rw [hPreHit]
    have hDelta0 : MallocngMappedDelta 16 (MallocngTightStepBound total bud.peakCount) s0.mem sm.mem := by
      simp only [decide_eq_true hMax, ↓reduceIte] at hDelta_bl
      exact mappedDelta_congr_perm hperms rfl hDelta_bl
    have hNoOrph0 := noOrphanMappings_congr_perm hperms rfl hNoOrph_bl
    refine SepWP.mono (calloc_malloc_hit (B := B) hb γ tp brkStart sp0 p v2 v3 bs total idx bud bf ivs0 st' g'
      s0 sm hovf hBlkWf hbsLen hg' hIdx hSlot hZeroMmap hNoOrph0 hCount hDelta0 hproc0m hclm
      hpc_m hrun_m hspm hsp0 hspAl0 hx0m hx19m htpm hbrksm hcs0m) ?_
    rintro sf P_f _ _ ⟨hent, hsp_f, hcs_f⟩; refine ⟨fun hsat => ?_, hsp_f, hcs_f⟩
    have hsat' := Satisfies.mono (sepConj_mono_left hent) hsat
    rw [sepConj_assoc, satisfies_pure_sepConj] at hsat'; obtain ⟨⟨hx0_f, _, hAcc⟩, hsat_sp⟩ := hsat'
    refine Satisfies.mono (sepConj_mono_left ?_) hsat_sp
    dsimp only [spec, ToBaseSpec.toSpec, mallocngCallocTokSpec, x, mallocngStackBytes]
    change _ ⊢ ⌜(OptOwn (MallocngTokZeroedBlock (B γ))).pureWf (sf.readReg64 .x0)
        (if ok = true then some (total, 16) else none) ∧
      MallocngCallAccounting 16 (MallocngTightStepBound (if ok = true then total else 0) bud.peakCount) s0 sf⌝ ∗
      (OptOwn (MallocngTokZeroedBlock (B γ))).interp (sf.readReg64 .x0)
        (if ok = true then some (total, 16) else none) ∗
      (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗ stackFrameAt sp0 1024)
    simp only [hok, ↓reduceIte, hx0_f, OptOwn_pureWf_some, OptOwn_interp_some, MallocngTokZeroedBlock]
    exact Entails.pure_right
      ⟨⟨hBlkWf.1, hBlkWf.1, hBlkWf.2.1, Nat.lt_of_le_of_lt hBlkWf.2.2.1 (by omega)⟩, hAcc⟩
      (Entails.of_eq (by ac_rfl))
  · have hok : ok = false := decide_eq_false hMax
    rw [ite_eq_right_iff.mpr (fun hp => False.elim (hMax hp)), sepConj_comm (stackFrameAt (sp0 - 48#64) 704), sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; intro hx0m
    have hspAl_m : sm.spAligned = true := by
      rw [State.spAligned, hspm]; exact spAligned_sub48 (by simpa [State.spAligned, hsp0] using hspAl0)
    wp_step; wp_step
    refine SepWP.mono (sepWP_false_oom (calloc_epilogue_ret hb sp0 0#64 _ s0 _
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun_m]) (by simp [arm64_norm, hspm]) hsp0 hspAl0 (by simp [arm64_norm])
      ⟨by simpa [arm64_norm] using hcs0m.1, by simpa [arm64_norm] using hcs0m.2.1,
       by simpa [arm64_norm] using hcs0m.2.2.1, by simpa [arm64_norm] using hcs0m.2.2.2.1,
       by simpa [arm64_norm] using hcs0m.2.2.2.2.1, by simpa [arm64_norm] using hcs0m.2.2.2.2.2.1,
       by simpa [arm64_norm] using hcs0m.2.2.2.2.2.2.1, by simpa [arm64_norm] using hcs0m.2.2.2.2.2.2.2.1,
       by simpa [calleeSavedVRegs] using hcs0m.2.2.2.2.2.2.2.2⟩)) ?_
    rintro sf P_f _ _ ⟨hent, hx0_f, hp_end, hbrk_end, hmem_end, hsp_f, hcs_f⟩
    have hp_m_f : MallocngProcPreserved sm sf :=
      ⟨hp_end.1, hp_end.2.1, hp_end.2.2.1, hp_end.2.2.2.1, hp_end.2.2.2.2.1, hp_end.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_advancePC, sigActions_writeReg64] using hp_end.2.2.2.2.2.2⟩
    have hAcc : MallocngCallAccounting 16 (MallocngTightStepBound 0 bud.peakCount) s0 sf := by
      simp only [decide_eq_false hMax, Bool.false_eq_true, ↓reduceIte] at hDelta_bl
      exact ⟨procPreserved_trans hproc0m hp_m_f, mappedDelta_congr_perm hperms (congrArg Memory.perm hmem_end) hDelta_bl⟩
    have hPostShift := postEnv_congr_pre_post γ tp brkStart bf ivs0 s0 _ sm sf
      (by simpa [arm64_norm] using hperms) hmem_end hbrk_end hp_m_f.2.2.1 hp_m_f.2.2.2.1
    refine ⟨fun hsat => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left (Entails.trans hent ?_)) hsat
    dsimp only [spec, ToBaseSpec.toSpec, mallocngCallocTokSpec, x, mallocngStackBytes]
    change _ ⊢ ⌜(OptOwn (MallocngTokZeroedBlock (B γ))).pureWf (sf.readReg64 .x0)
        (if ok = true then some (total, 16) else none) ∧
      MallocngCallAccounting 16 (MallocngTightStepBound (if ok = true then total else 0) bud.peakCount) s0 sf⌝ ∗
      (OptOwn (MallocngTokZeroedBlock (B γ))).interp (sf.readReg64 .x0)
        (if ok = true then some (total, 16) else none) ∗
      (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗ stackFrameAt sp0 1024)
    simp only [hok, Bool.false_eq_true, ↓reduceIte, hx0_f, OptOwn_pureWf_none, OptOwn_interp_none]
    exact Entails.pure_right ⟨trivial, hAcc⟩ (Entails.pure_right trivial (sepConj_mono_left hPostShift))

private theorem unpack_stackFrame_1024 (sp0 : BitVec 64) :
    stackFrameAt sp0 1024 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        stackFrameAt (sp0 - 48#64) 704 ∗ stackFrameAt (sp0 - 752#64) 272 ∗
        ((sp0 - 48#64) ↦₆₄ w0) ∗ ((sp0 - 40#64) ↦₆₄ w1) ∗ ((sp0 - 32#64) ↦₆₄ w2) ∗
        ((sp0 - 24#64) ↦₆₄ w3) ∗ ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5) := by
  rw [stackFrameAt_1024_split_48_704 sp0]; cells_unfold
  exact Entails.refl _

private theorem blk02_calloc_ok [MallocngMultiPlacement] {B : GhostName → BitVec 64 → Nat → Nat → SepProp}
    (hDefMalloc : DefaultMallocPlacedTokStmt B) (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 2 msvc) (mbase 2)
      (withCL mmpl (ToBaseSpec.toSpec (mallocngCallocTokSpec B msvc γ maddrs) (mbase 2))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b02.rebase c (fun _ => none)).fnAddr "calloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b02.fnOff "calloc") = c
    rw [blkPC_b02_fnOff_0x0]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b02 (hfn (mbase 2)) fun b hb => ?_
  have _ := hb; apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp; rw [hfn b] at hpc
  rcases x with ⟨nmemb, size, sp0, tp, brkStart, bud, ivs0⟩
  dsimp only [ToBaseSpec.toSpec, mallocngCallocTokSpec, MallocngEnv, mallocngStackBytes] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hm0, ⟨hx0, hx1, hsp0, _, _⟩, ⟨htp0, hbrks0⟩, hmem0⟩ := hpre
  have hcl_s0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  rw [← sepConj_assoc] at hmem0
  refine ⟨mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗ stackFrameAt sp0 1024, hmem0, ?_⟩
  apply SepWP.weaken_pre (sepConj_mono_right (unpack_stackFrame_1024 sp0))
  simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have ha1 : sp0 + (-48#64) = sp0 - 48#64 := by bv_arith
  have ha2 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have ha3 : sp0 - 48#64 + 16#64 = sp0 - 32#64 := by bv_arith
  have ha4 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have hspAl0 : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hsp
  have hspAl48 : ((sp0 - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  wp_stp64_cl m1 hm1 hcl_s0 hcl1; wp_step; wp_stp64_cl m2 hm2 hcl1 hcl2
  have hPreSaved : (mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗
      stackFrameAt (sp0 - 48#64) 704 ∗ stackFrameAt (sp0 - 752#64) 272 ∗
      ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5)) =
      (mallocngIface.MallocngHeap γ maddrs tp brkStart s0.brk bud ivs0 ∗ callocStackSaved sp0 s0 w4 w5) := rfl
  rw [hPreSaved]
  by_cases hz1 : size = 0#64
  · subst hz1; wp_step
    exact calloc_no_ovf hb hDefMalloc γ nmemb 0#64 sp0 tp brkStart w4 w5 bud ivs0 R s0 _
      (by simp) hcl2 (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm]) hsp0 hsp
      (by simpa [arm64_norm] using hx0) (by simp [arm64_norm, hx1])
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [sigActions_setPC, sigActions_setMem, sigActions_writeReg64]⟩
      rfl (hm2.trans hm1) htp0 hbrks0
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
  · wp_step; wp_step
    by_cases hovf : nmemb.toNat * size.toNat < 2 ^ 64
    · have hum0 : ((nmemb.zeroExtend 128 * size.zeroExtend 128) >>> 64).truncate 64 = 0#64 :=
        (umulh_eq_zero_iff nmemb size).mpr hovf
      wp_step
      exact calloc_no_ovf hb hDefMalloc γ nmemb size sp0 tp brkStart w4 w5 bud ivs0 R s0 _
        hovf hcl2 (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm]) hsp0 hsp
        (by simpa [arm64_norm] using hx0) (by simpa [arm64_norm] using hx1)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [sigActions_setPC, sigActions_setMem, sigActions_writeReg64]⟩
        rfl (hm2.trans hm1) htp0 hbrks0
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
    · have hum_ne : ((nmemb.zeroExtend 128 * size.zeroExtend 128) >>> 64).truncate 64 ≠ 0#64 :=
        fun h => hovf ((umulh_eq_zero_iff nmemb size).mp h)
      wp_step
      have hok : decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = false :=
        decide_eq_false (by unfold MallocngMaxAllocSize; omega)
      refine SepWP.mono (sepWP_false_oom (calloc_overflow_exit hb γ tp brkStart sp0 bud ivs0 s0 _
        hcl2 (by simp [arm64_norm, hum_ne]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm]) hsp0 hsp
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [sigActions_setPC, sigActions_setMem, sigActions_writeReg64]⟩
        rfl (hm2.trans hm1)
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩
        htp0 hbrks0)) ?_
      rintro sf P_f _ _ ⟨hq, hsp_f, hcs_f⟩; refine ⟨fun hsat => ?_, hsp_f, hcs_f⟩
      have hsat' := hq R hsat; rw [sepConj_assoc, satisfies_pure_sepConj] at hsat'
      obtain ⟨⟨hx0_f, hAcc⟩, hsat_env⟩ := hsat'
      refine Satisfies.mono (sepConj_mono_left ?_) hsat_env
      dsimp only [ToBaseSpec.toSpec, mallocngCallocTokSpec, mallocngStackBytes]
      change _ ⊢ ⌜(OptOwn (MallocngTokZeroedBlock (B γ))).pureWf (sf.readReg64 .x0)
          (if decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = true then some (nmemb.toNat * size.toNat, 16) else none) ∧
        MallocngCallAccounting 16 (MallocngTightStepBound (if decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = true
          then nmemb.toNat * size.toNat else 0) bud.peakCount) s0 sf⌝ ∗
        (OptOwn (MallocngTokZeroedBlock (B γ))).interp (sf.readReg64 .x0)
          (if decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = true then some (nmemb.toNat * size.toNat, 16) else none) ∗
        (MallocngPostEnv mallocngIface γ maddrs tp brkStart
          (mallocngAllocBudget (decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize)) (nmemb.toNat * size.toNat) bud)
          ivs0 s0 sf ∗ stackFrameAt sp0 1024)
      simp only [hok, Bool.false_eq_true, ↓reduceIte, mallocngAllocBudget, hx0_f, OptOwn_pureWf_none, OptOwn_interp_none]
      exact Entails.pure_right ⟨trivial, hAcc⟩ (Entails.pure_right trivial (Entails.refl _))

/-- Multi-block placed `calloc(nmemb, size)` (`b02`) satisfies `mallocngCallocTokSpec B`. -/
theorem callocPlaced_entry_tok_ok {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hDefMalloc : DefaultMallocPlacedTokStmt B)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc" (mallocngCallocTokSpec B svc γ (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := { mpl := mpl, svc := svc, placeable := hPlace, svcValid := hSvc }
  refine ⟨by decide, 2, 0, by decide +kernel, ?_⟩
  rw [fnAddr_calloc]
  exact withCL_to_withCodeLoaded (blk02_calloc_ok hDefMalloc γ)

/-- Multi-block placed `calloc(nmemb, size)` (`b02`) satisfies `mallocngCallocTightSpec`. -/
theorem callocPlaced_entry_tight_ok (hDefMalloc : DefaultMallocPlacedTightStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPlace : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngCallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  callocPlaced_entry_tok_ok (DefaultMallocPlacedTightStmt.toTok hDefMalloc) mpl svc hPlace hSvc γ

end VerifiedLibraries.Mallocng.Proofs
