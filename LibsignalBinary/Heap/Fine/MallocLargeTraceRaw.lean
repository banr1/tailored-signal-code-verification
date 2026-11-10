/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocLargeProof
public import LibsignalBinary.Heap.Fine.MallocLargeTraceHelpers
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof

/-!
# Raw-State Placed `__libc_malloc_impl` Large `mmap` Branch

Proves `placed_mallocImpl_large_raw_ok` (`131,051 < req ≤ MallocngMaxAllocSize`, `blk09`),
composing `call_placed_allocMeta_fine` with direct `mmap` group initialization to expose the
concrete `sc = 63` group `cg` for `MallocngFineInv`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

@[local simp, local arm64_norm, local wp_norm]
private theorem pageOf_add_zext_lo12Of (T : BitVec 64) :
    pageOf T + BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = T := by
  have h : BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = lo12Of T := by
    unfold lo12Of; bv_bits
  rw [h, pageOf_add_lo12Of]

private theorem ctxBytes_length (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (hPad : c.seqPad.length = 7) :
    c.toBytes.length = 928 := by
  obtain ⟨hPre, hSuf, hEq, _⟩ := ctxBytes_seq_split hAct hUse hUnm hBnc hPad
  have h := congrArg List.length hEq
  simp only [List.length_append, List.length_singleton] at hPre hSuf h
  omega

private theorem extract_fresh_mmap_disjoint_A [MallocngMultiPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {oom : State → SepProp}
    {post : State → SepProp → Prop}
    {inflight : Nat} {γ : GhostName} {brkStart mb : BitVec 64}
    {liveCost peakCost len : Nat} {st1 : MallocngSt} {Rest : SepProp}
    (hMbAl : mb.toNat % 4096 = 0)
    (hLenAl : len % 4096 = 0)
    (hLenPos : 4096 ≤ len)
    (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (hk : (∀ r ∈ dynamicRootRegions st1, DisjointRegions r.1 r.2 mb len) →
      SepWP prog target_pc s
        ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
         MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ Rest)
        post oom) :
    SepWP prog target_pc s
      ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ Rest)
      post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hm' : s.mem ⊨
      (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
      MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ (Rest ∗ R) := by
    simpa [sepConj_assoc] using hm
  have hDisj := fresh_mmap_disjoint_A hm' hMbAl hLenAl hLenPos hMbBound
  exact SepWP.to_reaches_pc (hk hDisj) hm

/-! ## `unmapSeq` Loop and Post-`alloc_meta` Group Initialization -/

private theorem unmapSeq_loop_bv (ctx : BitVec 64) (k : Nat) :
    (ctx + BitVec.ofNat 64 (848 + k)) + 1#64 = ctx + BitVec.ofNat 64 (848 + (k + 1)) ∧
    BitVec.ofNat 64 (848 + k) + 1#64 = BitVec.ofNat 64 (848 + (k + 1)) ∧
    (k + 1 < 32 → 880#64 ≠ BitVec.ofNat 64 (848 + (k + 1))) ∧
    (k + 1 = 32 → 880#64 = BitVec.ofNat 64 (848 + (k + 1))) := by
  refine ⟨by bv_omega, by bv_omega, fun hlt => by bv_omega, fun heq => ?_⟩
  have hk : k = 31 := by omega
  subst hk
  bv_omega

set_option maxHeartbeats 400000 in
private theorem unmapSeq_zero_loop [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 : State} {mb : BitVec 64} {req : Nat} {oom : State → SepProp}
    (tail : List (BitVec 8)) :
    ∀ {k : Nat} {s : State} {F : SepProp},
      k + tail.length = 32 →
      1 ≤ tail.length →
      s.pc = b + miOff_seq_zero_loop →
      s.status = .Running →
      s.sp = s0.sp - 80#64 →
      MallocngProcPreserved s0 s →
      MallocImplUntouchedCS s0 s →
      s.readReg64 (.gpr 1#5) = maddrs.ctx + BitVec.ofNat 64 (848 + k) →
      s.readReg64 (.gpr 2#5) = maddrs.ctx + 880#64 →
      s.readReg64 (.gpr 19#5) = mb →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req →
      s.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_seq_zero_mov1) s
        (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦ₛ tail) ∗ F)
        (fun s1 P1 =>
          (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
           MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
           s1.readReg64 (.gpr 0#5) = maddrs.ctx ∧
           s1.readReg64 (.gpr 19#5) = mb ∧
           s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
           s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
           s1.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
          (P1 ⊢ ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦ₛ List.replicate tail.length 0#8) ∗ F))
        oom := by
  have _ := hb
  induction tail with
  | nil =>
    intro k s F _ hPos
    simp at hPos
  | cons b0 tail' ih =>
    intro k s F hk hPos hpc hrun hsp hProc hcs hx1 hx2 hx19 hx20 hx24 hx25
    dsimp only [miOff_seq_zero_loop, miOff_seq_zero_mov1] at hpc ⊢
    obtain ⟨hPtrNext, hPtrOff, hNeLt, hEq32⟩ := unmapSeq_loop_bv maddrs.ctx k
    rw [pointsToBytes_cons, sepConj_assoc]
    wp_str8_perm m1 hm1
    wp_steps 2
    rcases tail' with _ | ⟨b1, rest⟩
    · simp only [List.length_singleton] at hk
      have hEq := hEq32 hk
      wp_if hBr
      · exact False.elim (hBr (by simpa [hx2, hPtrOff] using hEq))
      · wp_step
        apply SepWP.done
        · simp only [arm64_norm]
        · exact hrun
        · refine ⟨⟨by simpa using hsp, rfl, hm1,
            by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
            untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
            by simp, by simp [hx19], by simp [hx20], by simp [hx24], by simp [hx25]⟩, ?_⟩
          simp only [List.length_singleton, List.replicate_succ, List.replicate_zero,
            pointsToBytes_cons, pointsToBytes_nil, sepConj_assoc]
          exact Entails.refl _
    · simp only [List.length_cons] at hk
      have hLt : k + 1 < 32 := by omega
      have hNe := hNeLt hLt
      wp_if hBr
      · rw [hPtrNext]
        have hFrameSwap :
            (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) ∗
             (((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) ∗ F)) =
            (((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) ∗
             (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) ∗ F)) := by
          generalize ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) = p0,
            ((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) = p1
          ac_rfl
        rw [hFrameSwap]
        refine SepWP.mono
          (ih (k := k + 1)
            (by simp only [List.length_cons]; omega)
            (by simp)
            (by simp only [arm64_norm]) hrun (by simpa using hsp)
            (by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc])
            (untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
            (by simp) (by simp [hx2]) (by simp [hx19]) (by simp [hx20])
            (by simp [hx24]) (by simp [hx25]))
          ?_
        rintro s2 P2 _ _ ⟨⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx19_2, hx20_2, hx24_2, hx25_2⟩, hP2⟩
        refine ⟨⟨hsp2, hbrk2, hperm2.trans hm1, hProc2, hcs2, hx0_2, hx19_2, hx20_2, hx24_2, hx25_2⟩,
          Entails.trans hP2 ?_⟩
        simp only [List.length_cons, List.replicate_succ, pointsToBytes_cons, ← hPtrNext]
        exact Entails.of_eq (by
          generalize ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) = p0,
            (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) + 1#64) ↦ₛ List.replicate (rest.length + 1) 0#8) = p1
          ac_rfl)
      · exfalso
        exact hNe (by simpa [hx2, hPtrOff] using hBr)

private theorem seq_bv_helpers :
    (∀ mb : BitVec 64, mb ≠ BitVec.allOnes 64 → mb + 1#64 ≠ 0#64) ∧
    (∀ b8 : BitVec 8, (BitVec.zeroExtend 32 b8 == 0xff#32) = (b8 == 0xff#8)) ∧
    (∀ b8 : BitVec 8, BitVec.truncate 8 (BitVec.zeroExtend 32 b8 + 1#32) = b8 + 1#8) := by
  refine ⟨fun mb hne heq => hne ?_, fun b8 => by bv_bits, fun b8 => by bv_bits⟩
  apply BitVec.eq_of_toNat_eq
  have hlt := mb.isLt
  have h0 : (mb + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_allOnes] at h0 ⊢
  omega

set_option maxHeartbeats 400000 in
private theorem mallocImpl_large_seq_prep [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {mb : BitVec 64} {req : Nat}
    {c : CtxFields} {oom : State → SepProp}
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7)
    (hMbNe1 : mb ≠ BitVec.allOnes 64)
    (hpc : s.pc = b + miOff_after_mmap) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = mb)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    let c' := if c.seq = 0xff#8 then { c with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
              else { c with seq := c.seq + 1#8 }
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_call_alloc_meta) s
      ((maddrs.ctx ↦ₛ c.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 19#5) = mb ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
         s1.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
        (P1 ⊢ (maddrs.ctx ↦ₛ c'.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F))
      oom := by
  intro c'
  have _ := hb
  obtain ⟨hCmnNe, _, hAdd1⟩ := seq_bv_helpers
  have hCtxOps := ctxBytes_ops c hAct hUse hUnm hBnc hPad
  have hCtxLen : c.toBytes.length = 928 := ctxBytes_length c hAct hUse hUnm hBnc hPad
  have hGetSeq : c.toBytes.getD 912 0#8 = c.seq := hCtxOps.2.2.2.2.1
  have hGetSeqOpt : c.toBytes[912]?.getD 0#8 = c.seq := by
    simpa only [List.getD_eq_getElem?_getD] using hGetSeq
  have hWriteInc : ByteSlice.write8 c.toBytes 912 (c.seq + 1#8) =
      ({ c with seq := c.seq + 1#8 }).toBytes := hCtxOps.2.2.2.2.2 (c.seq + 1#8)
  generalize hCtxBs : c.toBytes = ctxBs at hCtxLen hGetSeq hGetSeqOpt hWriteInc ⊢
  dsimp only [miOff_after_mmap, miOff_call_alloc_meta] at hpc ⊢
  wp_steps
  wp_if hCmn
  · exact False.elim (hCmnNe mb hMbNe1 (by simpa [hx0] using hCmn))
  wp_steps
  wp_if hSeqFF
  · have hSeqEq : c.seq = 0xff#8 := by
      revert hSeqFF; bv_bits
    dsimp only [c']
    rw [ite_eq_left hSeqEq]
    wp_steps 2
    obtain ⟨hPreLen, hSufLen, hSplitEq, hRejoin⟩ := ctxBytes_seq_split hAct hUse hUnm hBnc hPad
    let pre848 := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
      unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
      unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
      unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++
      c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64
    let suf15 := c.seqPad ++ unpack64 c.brk
    let rest48 := c.bounces ++ [c.seq] ++ suf15
    have hCtxSplit :
        (maddrs.ctx ↦ₛ ctxBs) =
          (((maddrs.ctx + BitVec.ofNat 64 (848 + 0)) ↦ₛ c.unmapSeq) ∗
           ((maddrs.ctx ↦ₛ pre848) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48))) := by
      have hAssoc : ctxBs = pre848 ++ (c.unmapSeq ++ rest48) := by
        rw [← hCtxBs]; simpa [pre848, rest48, suf15, List.append_assoc] using hSplitEq
      rw [hAssoc, pointsToBytes_append, hPreLen,
          pointsToBytes_append_off maddrs.ctx 848 880 c.unmapSeq rest48 (by omega)]
      dsimp only [Nat.add_zero]
      generalize (maddrs.ctx ↦ₛ pre848) = pPre,
        ((maddrs.ctx + 848#64) ↦ₛ c.unmapSeq) = pUnm,
        ((maddrs.ctx + 880#64) ↦ₛ rest48) = pRest
      ac_rfl
    rw [hCtxSplit, sepConj_assoc, sepConj_assoc]
    refine SepWP.seq_entails_emp
      (unmapSeq_zero_loop (s0 := s0) (mb := mb) (req := req) hb c.unmapSeq (k := 0)
        (by omega) (by omega)
        (by dsimp only [miOff_seq_zero_loop]; simp only [arm64_norm]; try bv_lin) hrun (by simpa using hsp)
        (by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc])
        (untouchedCS_step hcs (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [calleeSavedVRegs]))
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hx20) (by simp [arm64_norm]) (by simp [arm64_norm])) ?_
    rintro sL hpcL hrunL ⟨hspL, hbrkL, hpermL, hProcL, hcsL, hx0L, hx19L, hx20L, hx24L, hx25L⟩
    dsimp only [miOff_seq_zero_mov1] at hpcL
    let cZero := { c with unmapSeq := List.replicate 32 0#8, seq := c.seq }
    have hCtxRejoin :
        (((maddrs.ctx + BitVec.ofNat 64 (848 + 0)) ↦ₛ List.replicate c.unmapSeq.length 0#8) ∗
         ((maddrs.ctx ↦ₛ pre848) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48) ∗
          (((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F))) =
        ((maddrs.ctx ↦ₛ cZero.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F) := by
      rw [hUnm]
      have hZeroBytes : cZero.toBytes = pre848 ++ (List.replicate 32 0#8 ++ rest48) := by
        have h1 := (hRejoin c.seq (List.replicate 32 0#8)).symm
        simpa [cZero, pre848, rest48, suf15, List.append_assoc] using h1
      have hSplit2 :
          (maddrs.ctx ↦ₛ cZero.toBytes) =
            ((maddrs.ctx ↦ₛ pre848) ∗
             (((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48))) := by
        rw [hZeroBytes, pointsToBytes_append, hPreLen,
            pointsToBytes_append_off maddrs.ctx 848 880 (List.replicate 32 0#8) rest48 (by simp)]
      rw [hSplit2]
      dsimp only [Nat.add_zero]
      generalize (maddrs.ctx ↦ₛ pre848) = pPre,
        ((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) = pUnm,
        ((maddrs.ctx + 880#64) ↦ₛ rest48) = pRest,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pLb
      ac_rfl
    rw [hCtxRejoin]
    have hOpsZero := ctxBytes_ops cZero hAct hUse (by simp [cZero]) hBnc hPad
    have hZeroLen : cZero.toBytes.length = 928 :=
      ctxBytes_length cZero hAct hUse (by simp [cZero]) hBnc hPad
    have hWrite1 : ByteSlice.write8 cZero.toBytes 912 1#8 =
        ({ c with unmapSeq := List.replicate 32 0#8, seq := 1#8 }).toBytes := hOpsZero.2.2.2.2.2 1#8
    generalize hZeroBs : cZero.toBytes = zeroBs at hZeroLen hWrite1 ⊢
    wp_step
    wp_str8_perm mS hmS
    wp_step
    apply SepWP.done
    · simp only [arm64_norm]; try bv_lin
    · exact hrunL
    · refine ⟨⟨by simpa using hspL, hbrkL, hmS.trans hpermL,
        by dsimp only [MallocngProcPreserved] at hProcL ⊢; simp [arm64_norm, hProcL],
        untouchedCS_step hcsL (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [hx19L], by simp [hx20L], by simp [hx24L], by simp [hx25L]⟩, ?_⟩
      simpa [hWrite1] using Entails.refl _
  · have hSeqNe : c.seq ≠ 0xff#8 := by
      intro hEq; rw [hEq] at hSeqFF; simp at hSeqFF
    dsimp only [c']
    rw [ite_eq_right hSeqNe]
    wp_step
    wp_str8_perm mS hmS
    apply SepWP.done
    · simp only [arm64_norm]; try bv_lin
    · exact hrun
    · refine ⟨⟨by simpa using hsp, rfl, hmS,
        by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
        untouchedCS_step hcs (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [calleeSavedVRegs]),
        by simp [arm64_norm], by simpa [arm64_norm] using hx20, by simp [arm64_norm], by simp [arm64_norm]⟩, ?_⟩
      have hVal : BitVec.truncate 8 (BitVec.zeroExtend 32 c.seq + 1#32) = c.seq + 1#8 := hAdd1 c.seq
      simpa [hGetSeqOpt, hVal, hWriteInc] using Entails.refl _

set_option maxHeartbeats 400000 in
private theorem mallocImpl_large_post_meta [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {m mb : BitVec 64} {req len : Nat}
    {c : CtxFields} {oom : State → SepProp}
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7)
    (hLenLo : 4096 ≤ len)
    (hmNe0 : m ≠ 0#64)
    (hPkEq : (((BitVec.ofNat 64 req + 0x1013#64) &&& 0xfffffffffffff000#64) ||| 0xfe0#64) =
      (mkLargeGroup m mb len).packedWord)
    (hpc : s.pc = b + miOff_after_alloc_meta) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = m)
    (hx19 : s.readReg64 (.gpr 19#5) = mb)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    let gNew := mkLargeGroup m mb len
    let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_call_unlock) s
      ((m ↦ₛ List.replicate 40 0#8) ∗ (mb ↦ₛ List.replicate len 0#8) ∗
       (maddrs.ctx ↦ₛ c.toBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 0#5) = maddrs.lock ∧
         s1.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 (c.mmapCounter + 1#32) ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 21#5) = 0#64 ∧
         s1.readReg64 (.gpr 22#5) = m ∧
         s1.readReg64 (.gpr 23#5) = 0#64) ∧
        (P1 ⊢ (m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
          (maddrs.ctx ↦ₛ ({ c with mmapCounter := c.mmapCounter + 1#32 }).toBytes) ∗ F))
      oom := by
  intro gNew groupBytes
  have _ := hb
  obtain ⟨hm1Len, hm2Len, hm3Len, hm4Eq, hMbWrite⟩ := large_meta_mem_writes m mb len (by omega)
  have hCtxOps := ctxBytes_ops c hAct hUse hUnm hBnc hPad
  have hCtxLen : c.toBytes.length = 928 := ctxBytes_length c hAct hUse hUnm hBnc hPad
  have hGetMmc :
      pack32 (c.toBytes[12]?.getD 0#8) (c.toBytes[13]?.getD 0#8)
        (c.toBytes[14]?.getD 0#8) (c.toBytes[15]?.getD 0#8) = c.mmapCounter := by
    simpa only [List.getD_eq_getElem?_getD] using hCtxOps.1
  have hCtxWrite : ByteSlice.write32 c.toBytes 12 (c.mmapCounter + 1#32) =
      ({ c with mmapCounter := c.mmapCounter + 1#32 }).toBytes := hCtxOps.2.1 (c.mmapCounter + 1#32)
  generalize hCtxBs : c.toBytes = ctxBs at hCtxLen hGetMmc hCtxWrite ⊢
  generalize hm0 : List.replicate 40 0#8 = m0Bs at hm1Len hm2Len hm3Len hm4Eq ⊢
  have hm0Len : m0Bs.length = 40 := by subst hm0; rfl
  generalize hmb0 : List.replicate len 0#8 = mb0Bs at hMbWrite ⊢
  have hmb0Len : mb0Bs.length = len := by subst hmb0; simp
  dsimp only [miOff_after_alloc_meta, miOff_call_unlock] at hpc ⊢
  wp_steps 2
  wp_if hCbz
  · exact False.elim (hmNe0 (by simpa [hx0] using hCbz))
  wp_step
  wp_str64_perm mm1 hmm1
  wp_str64_perm mm2 hmm2
  wp_steps 2
  wp_str32_perm mm3 hmm3
  wp_steps 6
  wp_str32_perm mm4 hmm4
  wp_str32_perm mm5 hmm5
  wp_str64_perm mm6 hmm6
  wp_steps 2
  apply SepWP.done
  · simp only [arm64_norm]; try bv_lin
  · exact hrun
  · refine ⟨⟨by simpa using hsp, rfl,
      hmm6.trans (hmm5.trans (hmm4.trans (hmm3.trans (hmm2.trans hmm1)))),
      by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
      untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
      by simp, by simp [hGetMmc], by simp [hx20], by simp,
      by simp, by simp⟩, ?_⟩
    simpa [hx0, hx19, hx20, hPkEq, hGetMmc, hm4Eq, hMbWrite, hCtxWrite, gNew, groupBytes]
      using Entails.refl _

private theorem stackFrame_eq_stackFrameAt {s : State} {sp1 : BitVec 64} (k : Nat)
    (hsp : s.sp = sp1) (_hk : k ≤ 624 := by decide) :
    stackFrame s k = stackFrameAt sp1 k := by
  unfold stackFrame
  rw [hsp, ← stackFrameAt_eq_memRegion sp1 k]

private theorem stackFrameAt_624_eq (sp1 : BitVec 64) (k : Nat) (hk : k ≤ 624) :
    stackFrameAt sp1 624 = (stackFrameAt sp1 k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) (624 - k)) := by
  have hEq : (624 : Nat) = k + (624 - k) := by omega
  conv => lhs; rw [hEq]
  exact stackFrameAt_split sp1 k (624 - k)

private theorem map_replace_head_of_nodup {g cg : GroupDesc} {gs : List GroupDesc}
    (hnd : (((g :: gs).map GroupDesc.metaPtr)).Nodup) :
    (g :: gs).map (fun x => if x.metaPtr == g.metaPtr then cg else x) = cg :: gs := by
  rw [List.map_cons, List.nodup_cons] at hnd
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
  have hNotMem : ∀ x ∈ gs, x.metaPtr ≠ g.metaPtr :=
    fun x hx hEq => hnd.1 (hEq ▸ List.mem_map_of_mem hx)
  clear hnd
  induction gs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, beq_eq_false_iff_ne.mpr (hNotMem x (List.mem_cons_self ..)),
      Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
    exact ih (fun y hy => hNotMem y (List.mem_cons_of_mem x hy))

/-! ## Large `mmap` Branch Theorem -/

set_option maxHeartbeats 400000 in
theorem placed_mallocImpl_large_raw_ok [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64}
    {liveCost peakCost maxGroups maxMetaAreas req : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk liveCost peakCost st0)
    (hGroups0 : st0.groups.length ≤ maxGroups)
    (hMeta0 : st0.metaAreas.length ≤ maxMetaAreas)
    (hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas)
    (hGt : 131051 < req) (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_large_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    let maxBytes := ((req + 20 + 4095) / 4096) * 4096 + 131072 * maxMetaAreas
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        ∃ (st' : MallocngSt) (cg : GroupDesc) (p : BitVec 64) (live' peak' : Nat),
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ MallocngProcPreserved s0 sf ∧
          sf.readReg64 .x0 = p ∧
          VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem ∧
          MallocngCallAccounting 16 maxBytes s0 sf ∧
          MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
          (P_f ⊢ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗ stackFrame s0 704 ∗
            (p ↦ₛ List.replicate req 0#8) ∗ MallocngBlockToken γ p req) ∧
          st'.groups = cg :: st0.groups ∧
          (∃ st1 : MallocngSt, st'.groups = cg :: st1.groups ∧ FineSameGroupsSlotKind st1.groups st0.groups) ∧
          cg.sc = 63 ∧ cg.parentMeta = none ∧ cg.nestedCap = 0 ∧ cg.lastIdx = 0 ∧ 0 < cg.maplen ∧
          cg.maplen * 4096 = ((req + 20 + 4095) / 4096) * 4096 ∧
          cg.slots = [.liveUser p req (max req MallocngMinBlockCost)] ∧
          st0.liveMap p = none ∧
          st'.liveMap = st0.liveMap.insert p req 0 ∧
          st'.metaAreas.length ≤ maxMetaAreas ∧
          MallocngBlockWf p req ∧
          p ≠ 0#64 ∧ p &&& 15#64 = 0#64 ∧ p.toNat + req ≤ 2 ^ 48)
      (fun sf => ⌜MallocngOomCondFine msvc maxBytes s0 sf⌝) := by
  intro maxBytes
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  obtain ⟨hRawPos, hRawMax, hAdd20Nat, hLenLo, hLenMod, _, _,
    _, _, _, hFitNew, hMapBound, hPkNew⟩ :=
    large_mmap_len_bounds (peakCount := 0) hGt hReqMax
  let rawLen := req + 20
  let len := pageAlignUp rawLen
  have hLenEq : len = ((req + 20 + 4095) / 4096) * 4096 := rfl
  have hLenStepFine : len ≤ maxBytes := by
    dsimp only [maxBytes]; rw [hLenEq]; omega
  have hMetaStepFine : allocMetaFineByteBound maxMetaAreas ≤ maxBytes := by
    dsimp only [allocMetaFineByteBound, maxBytes]; omega
  have hSumStepFine : len + allocMetaFineByteBound maxMetaAreas ≤ maxBytes := by
    dsimp only [allocMetaFineByteBound, maxBytes]; rw [hLenEq]; omega
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  have hRtUnpack :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      (∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) := by
    unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepExists_congr fun errnoVal => ?_
    generalize ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 = pCr
    ac_rfl
  rw [hRtUnpack]
  apply SepWP.exists_elim; intro errnoVal
  dsimp only [miOff_large_entry] at hpc
  wp_steps 8
  have hmmap := placed_mmapRw_large_ok (P := blkPC_b09.rebase b (fun _ => none))
    tp errnoVal rawLen hRawPos hRawMax
  dsimp only at hmmap
  rw [at_bl_target_b09_raw hb 16 miOff_call_mmap] at hmmap
  let mmapFrame :=
    stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs ∗
    MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  refine SepWP.call_subroutine_frame (F := mmapFrame) (x := ()) (ret_pc := b + miOff_after_mmap)
    hmmap rfl
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_call_mmap, miOff_after_mmap, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, mmapFrame, State.setPC, State.writeReg64, State.writeReg32]
      rw [stackFrame_eq_stackFrameAt 64 (by simpa [arm64_norm] using hsp),
          stackFrameAt_624_eq (s0.sp - 80#64) 64 (by decide)]
      simp only [sepConj_assoc]
      refine Entails.pure_right
        ⟨by simpa [arm64_norm] using hProc.2.2.1.trans htp0,
         rfl,
         hAdd20Nat,
         rfl, rfl, rfl, rfl⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ = pCL,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
        stackFrameAt (s0.sp - 80#64) 64 = pS1,
        stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) = pS2,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 = pCr,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (oomCondFine_of_mmap_large hLenLo hLenMod hLenStepFine ?_ hPerm0 hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc ⊢
      simp [arm64_norm, hProc])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro mb
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_m0, hbrk_m, hx0_m, hMbNe0, hMbNe1, hMbDiv, hMbBound, hDelta_m, hInReg_m⟩
  rw [stackFrame_eq_stackFrameAt 64 (by simpa [arm64_norm] using hsp)]
  have hPullCL :
      ((stackFrameAt (s0.sp - 80#64) 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗ mmapFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
       (stackFrameAt (s0.sp - 80#64) 624 ∗
        (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA 0 γ maddrs brkStart sm.brk liveCost peakCost st0 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) := by
    have hBrkEq : sm.brk = s.brk := hbrk_m
    rw [hBrkEq]
    dsimp only [mmapFrame]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) 64 (by decide)]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ = pCL,
      stackFrameAt (s0.sp - 80#64) 64 = pS1,
      stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) = pS2,
      ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightA 0 γ maddrs brkStart s.brk liveCost peakCost st0 = pCr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
    ac_rfl
  rw [hPullCL]
  apply SepWP.pure_elim; intro hcl_m
  have hProc_m : MallocngProcPreserved s0 sm := by
    refine procPres_trans ?_ ⟨hProc_m0.1, hProc_m0.2.1, hProc_m0.2.2.1, hProc_m0.2.2.2.1,
      hProc_m0.2.2.2.2.1, hProc_m0.2.2.2.2.2.1,
      by simpa [sigActions_setPC, sigActions_writeReg64, sigActions_writeReg32] using hProc_m0.2.2.2.2.2.2⟩
    dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc]
  have hsp_sm : sm.sp = s0.sp - 80#64 := hsp_m.trans (by simpa [arm64_norm] using hsp)
  have hcs_sm : MallocImplUntouchedCS s0 sm :=
    untouchedCS_step hcs (hcs_m.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_m.2.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_m.2.2.2.2.2.2.2.2.2.1.trans (by simp))
      (by simpa [calleeSavedVRegs] using hcs_m.2.2.2.2.2.2.2.2.2.2.2)
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req :=
    hcs_m.2.1.trans (by simpa [arm64_norm] using hx20)
  have hDelta0_sm : MallocngMappedDelta 1 len s0.mem sm.mem := by
    obtain ⟨ivs, hl, hs, hc⟩ := hDelta_m
    exact ⟨ivs, hl, hs, fun a ha => (hc a ha).imp (fun hm => hPerm0 ▸ hm) id⟩
  have hInReg0_sm : MmapNewInRegion mb len s0.mem sm.mem :=
    fun a ha => (hInReg_m a ha).imp (fun hm => hPerm0 ▸ hm) id
  have hwf_sm : MallocngWFInflight 0 maddrs.base brkStart sm.brk liveCost peakCost st0 := hbrk_m ▸ hwf0
  let st_seq := updateSeqSt st0
  have hwf_seq0 : MallocngWF maddrs.base brkStart sm.brk liveCost peakCost st_seq :=
    updateSeqSt_wf hwf_sm
  let coreBody0 :=
    MallocngLiveAuth γ st0.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗ MallocngAuxvState γ st0.auxvPtr st0.auxvSnap ∗
    ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗
    ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
    MappedSet st0.masterDom (OwnedMappedByte st0)
  let seqFrame :=
    stackFrameAt (s0.sp - 80#64) 624 ∗
    (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs ∗
    coreBody0 ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  have hToSeq :
      (stackFrameAt (s0.sp - 80#64) 624 ∗
       (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA 0 γ maddrs brkStart sm.brk liveCost peakCost st0 ∗
       ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) =
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ seqFrame) := by
    dsimp only [MallocngCoreStInflightA, coreBody0, seqFrame]
    rw [propext ⟨fun _ => trivial, fun _ => hwf_sm⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
      MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
    ac_rfl
  rw [hToSeq]
  refine sepWP_seq_cl (mid := b + miOff_call_alloc_meta) hcl_m ?_
  refine SepWP.mono
    (mallocImpl_large_seq_prep hb hwf_sm.ctx_lens.1 hwf_sm.ctx_lens.2.1
      hwf_sm.ctx_lens.2.2.1 hwf_sm.ctx_lens.2.2.2.1 (by simp [hwf_sm.ctx_lens.2.2.2.2.1])
      hMbNe1 hpc_m hrun_m hsp_sm hProc_m hcs_sm hx0_m hx20_sm) ?_
  rintro s_q P_q hpc_q hrun_q ⟨⟨hsp_q, hbrk_q, hperm_q, hProc_q, hcs_q, hx19_q, hx20_q, hx24_q, hx25_q⟩, hPq⟩ hcl_q
  apply SepWP.weaken_pre hPq
  have hwf_seq : MallocngWFInflight 0 maddrs.base brkStart s_q.brk liveCost peakCost st_seq :=
    hbrk_q ▸ hwf_seq0
  have hCtxSeqEq :
      (if st0.ctx.seq = 0xff#8 then { st0.ctx with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
       else { st0.ctx with seq := st0.ctx.seq + 1#8 }) = st_seq.ctx := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hRebundleSeq :
      ((maddrs.ctx ↦ₛ (if st0.ctx.seq = 0xff#8 then { st0.ctx with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
        else { st0.ctx with seq := st0.ctx.seq + 1#8 }).toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ seqFrame) ⊢
      stackFrameAt (s0.sp - 80#64) 624 ∗
      MallocngCoreStInflightA 0 γ maddrs brkStart s_q.brk liveCost peakCost st_seq ∗
      MallocngRuntime maddrs tp ∗
      (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
      MallocngRoTablesA maddrs := by
    rw [hCtxSeqEq]
    have hRtIntro :
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ⊢
          MallocngRuntime maddrs tp := by
      unfold MallocngRuntime
      exact sepConj_mono_left (Entails.sepExists_right errnoVal (Entails.refl _))
    have hCoreEq :
        MallocngCoreStInflightA 0 γ maddrs brkStart s_q.brk liveCost peakCost st_seq =
          ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ coreBody0) := by
      have hSameAtoms :
          MallocngLiveAuth γ st_seq.liveMap = MallocngLiveAuth γ st0.liveMap ∧
          ((maddrs.libc + 8#64) ↦₆₄ st_seq.auxvPtr) = ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) ∧
          MallocngAuxvState γ st_seq.auxvPtr st_seq.auxvSnap = MallocngAuxvState γ st0.auxvPtr st0.auxvSnap ∧
          ByteMap st_seq.masterDom (OwnedRwByte st_seq) st_seq.byteVal =
            ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∧
          ProtNoneByteMap st_seq.masterDom (OwnedProtNoneByte st_seq) st_seq.byteVal =
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∧
          MappedSet st_seq.masterDom (OwnedMappedByte st_seq) =
            MappedSet st0.masterDom (OwnedMappedByte st0) := by
        dsimp only [st_seq, updateSeqSt]
        split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      dsimp only [MallocngCoreStInflightA, coreBody0]
      rw [propext ⟨fun _ => trivial, fun _ => hwf_seq⟩, pure_true, emp_sepConj,
          hSameAtoms.1, hSameAtoms.2.1, hSameAtoms.2.2.1, hSameAtoms.2.2.2.1,
          hSameAtoms.2.2.2.2.1, hSameAtoms.2.2.2.2.2]
      generalize (maddrs.ctx ↦ₛ st_seq.ctx.toBytes) = pCtx,
        MallocngLiveAuth γ st0.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st0.auxvPtr) = pLb8,
        MallocngAuxvState γ st0.auxvPtr st0.auxvSnap = pAx,
        ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
        ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
        MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
      ac_rfl
    rw [hCoreEq]
    dsimp only [seqFrame]
    have hRearr :
        ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗
         (stackFrameAt (s0.sp - 80#64) 624 ∗ (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
          MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ coreBody0 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) =
        (stackFrameAt (s0.sp - 80#64) 624 ∗ ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ coreBody0) ∗
         (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
         (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs) := by
      generalize (maddrs.ctx ↦ₛ st_seq.ctx.toBytes) = pCtx,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        (mb ↦ₛ List.replicate len 0#8) = pMb,
        memMapped mb len = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        coreBody0 = pCb,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
      ac_rfl
    rw [hRearr]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hRtIntro))
  apply SepWP.weaken_pre hRebundleSeq
  have hSpAl_q : s_q.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp_q]; exact sp_sub_80_aligned hsp_align
  have hSeqGroupsEq : st_seq.groups = st0.groups := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hSeqMetaEq : st_seq.metaAreas = st0.metaAreas := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hSeqLiveEq : st_seq.liveMap = st0.liveMap := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hGroupsSeq : st_seq.groups.length ≤ maxGroups := by
    rwa [hSeqGroupsEq]
  have hMetaSeq : st_seq.metaAreas.length ≤ maxMetaAreas := by
    rwa [hSeqMetaEq]
  dsimp only [miOff_call_alloc_meta] at hpc_q
  wp_step
  have hMetaCall := call_placed_allocMeta_fine (P := blkPC_b09.rebase b (fun _ => none))
    0 (by decide) γ tp brkStart liveCost peakCost maxGroups maxMetaAreas st_seq
    hGroupsSeq hMetaSeq hMetaStep
  rw [at_bl_target_b09_raw hb 7 miOff_call_alloc_meta] at hMetaCall
  let metaFrame :=
    stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) ∗
    (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs
  have hDelta0_q : MallocngMappedDelta 1 len s0.mem s_q.mem :=
    mappedDelta_congr_perm_right hDelta0_sm hperm_q
  refine SepWP.call_subroutine_frame (F := metaFrame) (x := ()) (ret_pc := b + miOff_after_alloc_meta)
    hMetaCall rfl
    (by simp [arm64_norm, hrun_q])
    (by simpa [State.spAligned, arm64_norm] using hSpAl_q)
    (by dsimp only [miOff_call_alloc_meta, miOff_after_alloc_meta, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, metaFrame, State.setPC, State.writeReg64]
      rw [stackFrame_eq_stackFrameAt 224 (by simpa [arm64_norm] using hsp_q),
          stackFrameAt_624_eq (s0.sp - 80#64) 224 (by decide)]
      simp only [sepConj_assoc]
      refine Entails.pure_right
        ⟨by simpa [arm64_norm] using hProc_q.2.2.1.trans htp0,
         by simpa [arm64_norm] using hProc_q.2.2.2.1.trans hbrkS0⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_q.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl_q (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_q.mem⌝ = pCL,
        stackFrameAt (s0.sp - 80#64) 224 = pS1,
        stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) = pS2,
        MallocngCoreStInflightA 0 γ maddrs brkStart s_q.brk liveCost peakCost st_seq = pCr,
        MallocngRuntime maddrs tp = pRt,
        (mb ↦ₛ List.replicate len 0#8) = pMb,
        memMapped mb len = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun s_a hpc_a hrun_a hsp_a hcs_a => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (oomCondFine_of_allocMeta_after_mmap hMetaStepFine hSumStepFine ?_ hDelta0_q hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc_q ⊢
      simp [arm64_norm, hProc_q])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro m
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_a0, hx0_a, hmNe0, _, _, _, _, hRes1, hGrps1, _, hLive1, _, hMetaLe_a,
    _, _, _, _, _, _, hNoOrph_a, hDelta_a⟩
  rw [stackFrame_eq_stackFrameAt 224 (by simpa [arm64_norm] using hsp_q)]
  have hPullCL_a :
      ((stackFrameAt (s0.sp - 80#64) 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
        MallocngCoreStInflightA (0 + 1) γ maddrs brkStart s_a.brk liveCost peakCost st1) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ ∗ metaFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ ∗
       ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
        MallocngCoreStInflightA 1 γ maddrs brkStart s_a.brk liveCost peakCost st1 ∗
        ((m ↦ₛ List.replicate 40 0#8) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         MallocngRoTablesA maddrs ∗
         MallocngRuntime maddrs tp))) := by
    dsimp only [metaFrame, Nat.zero_add]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) 224 (by decide)]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ = pCL,
      stackFrameAt (s0.sp - 80#64) 224 = pS1,
      stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) = pS2,
      MallocngRuntime maddrs tp = pRt,
      (m ↦ₛ List.replicate 40 0#8) = pM,
      MallocngCoreStInflightA 1 γ maddrs brkStart s_a.brk liveCost peakCost st1 = pCr,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo
    ac_rfl
  rw [hPullCL_a]
  apply SepWP.pure_elim; intro hcl_a
  apply extract_fresh_mmap_disjoint_A (Nat.mod_eq_zero_of_dvd hMbDiv) hLenMod hLenLo hMbBound
  intro hDisjDyn
  have hUnpackCore1 :
      ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocngCoreStInflightA 1 γ maddrs brkStart s_a.brk liveCost peakCost st1 ∗
       ((m ↦ₛ List.replicate 40 0#8) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) =
      (⌜MallocngWFInflight 1 maddrs.base brkStart s_a.brk liveCost peakCost st1⌝ ∗
       ((m ↦ₛ List.replicate 40 0#8) ∗ (mb ↦ₛ List.replicate len 0#8) ∗
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
        (memMapped mb len ∗
         MallocngLiveAuth γ st1.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
         ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
         ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
         MappedSet st1.masterDom (OwnedMappedByte st1) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) := by
    dsimp only [MallocngCoreStInflightA]
    generalize ⌜MallocngWFInflight 1 maddrs.base brkStart s_a.brk liveCost peakCost st1⌝ = pWF,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      (m ↦ₛ List.replicate 40 0#8) = pM,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
      MallocngLiveAuth γ st1.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
      MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
      MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hUnpackCore1]
  apply SepWP.pure_elim; intro hwf1
  have hProc_sa : MallocngProcPreserved s0 s_a := by
    refine procPres_trans ?_
      ⟨hProc_a0.1, hProc_a0.2.1, hProc_a0.2.2.1, hProc_a0.2.2.2.1,
       hProc_a0.2.2.2.2.1, hProc_a0.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_writeReg64] using hProc_a0.2.2.2.2.2.2⟩
    dsimp only [MallocngProcPreserved] at hProc_q ⊢; simp [arm64_norm, hProc_q]
  have hsp_sa : s_a.sp = s0.sp - 80#64 := hsp_a.trans (by simpa [arm64_norm] using hsp_q)
  have hcs_sa : MallocImplUntouchedCS s0 s_a :=
    untouchedCS_step hcs_q (hcs_a.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_a.2.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_a.2.2.2.2.2.2.2.2.2.1.trans (by simp))
      (by simpa [calleeSavedVRegs] using hcs_a.2.2.2.2.2.2.2.2.2.2.2)
  have hx19_sa : s_a.readReg64 (.gpr 19#5) = mb := hcs_a.1.trans (by simpa [arm64_norm] using hx19_q)
  have hx20_sa : s_a.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req := hcs_a.2.1.trans (by simpa [arm64_norm] using hx20_q)
  have hx24_sa : s_a.readReg64 (.gpr 24#5) = pageOf maddrs.lock :=
    hcs_a.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hx24_q)
  have hx25_sa : s_a.readReg64 (.gpr 25#5) = pageOf maddrs.ctx :=
    hcs_a.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hx25_q)
  refine sepWP_seq_cl (mid := b + miOff_call_unlock) hcl_a ?_
  refine SepWP.mono
    (mallocImpl_large_post_meta hb hwf1.ctx_lens.1 hwf1.ctx_lens.2.1
      hwf1.ctx_lens.2.2.1 hwf1.ctx_lens.2.2.2.1 (by simp [hwf1.ctx_lens.2.2.2.2.1])
      hLenLo hmNe0 (hPkNew m mb) hpc_a hrun_a hsp_sa hProc_sa hcs_sa
      hx0_a hx19_sa hx20_sa hx24_sa hx25_sa) ?_
  rintro s_u P_u hpc_u hrun_u
    ⟨⟨hsp_u, hbrk_u, hperm_u, hProc_u, hcs_u, hx0_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u⟩, hPu⟩ hcl_u
  apply SepWP.weaken_pre hPu
  have hRes1Eq : st1.reservedMetas = [m] := by
    have h0Res : st_seq.reservedMetas = [] := by
      have : st_seq.reservedMetas = st0.reservedMetas := by dsimp [st_seq, updateSeqSt]; split <;> rfl
      rw [this]
      have hInf0 := hwf0.inflight_wf
      cases hr : st0.reservedMetas with
      | nil => rfl
      | cons _ _ => rw [hr] at hInf0; simp at hInf0
    rwa [h0Res] at hRes1
  have hDynSeqEq : dynamicRootRegions st_seq = dynamicRootRegions st0 := by
    dsimp only [st_seq, updateSeqSt, dynamicRootRegions]; split <;> rfl
  have hNoOrph_a' : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s_q.mem s_a.mem := by
    rw [← hDynSeqEq]; exact hNoOrph_a
  have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk liveCost peakCost st1 :=
    hbrk_u ▸ hwf1
  obtain ⟨hNoRes2, _, hMetaLen2, hg2, hSlotsPos2, hClaimed2, _, hMap2,
    hZeroMm2, hNoOrph2, hwf2, hBundle2⟩ :=
    large_group_bundle (γ := γ) (ivs0 := dynamicRootRegions st0)
      (m0 := s0.mem) (m1 := sm.mem) (m2 := s_q.mem) (m3 := s_a.mem) (mf := s_u.mem)
      hwf1_u hRes1Eq hMbNe0 hMbDiv hLenLo hLenMod hMbBound
      hInReg0_sm hperm_q hNoOrph_a' hperm_u hDisjDyn
  let gNew := mkLargeGroup m mb len
  let st2 := mkLargeGroupSt st1 m mb len
  let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
  have hToJoin :
      ((m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
       (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
       (memMapped mb len ∗ MallocngLiveAuth γ st1.liveMap ∗
        (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
        MappedSet st1.masterDom (OwnedMappedByte st1) ∗
        stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) ⊢
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightA 1 γ maddrs brkStart s_u.brk liveCost peakCost st2 ∗
      MallocngRuntime maddrs tp := by
    have hRearr :
        ((m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
         (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
         (memMapped mb len ∗ MallocngLiveAuth γ st1.liveMap ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
          MappedSet st1.masterDom (OwnedMappedByte st1) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗
          MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) =
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         (MallocngLiveAuth γ st1.liveMap ∗
          (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗ MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
          (m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗ memMapped mb len ∗
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
          MappedSet st1.masterDom (OwnedMappedByte st1)) ∗
         MallocngRuntime maddrs tp) := by
      generalize (m ↦ₛ gNew.metaBytes) = pM,
        (mb ↦ₛ groupBytes) = pMb,
        (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) = pCtx,
        memMapped mb len = pMp,
        MallocngLiveAuth γ st1.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb8,
        MallocngAuxvState γ st1.auxvPtr st1.auxvSnap = pAx,
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hRearr]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hBundle2)))
  apply SepWP.weaken_pre hToJoin
  have hDelta_u : MallocngMappedDelta 16 maxBytes s0.mem s_u.mem := by
    have hSum : MallocngMappedDelta (1 + 1) (len + allocMetaFineByteBound maxMetaAreas) s0.mem s_a.mem :=
      MallocngMappedDelta.trans hDelta0_q hDelta_a
    exact mappedDelta_congr_perm_right
      (MallocngMappedDelta.mono (by decide : 1 + 1 ≤ 16) hSumStepFine hSum) hperm_u
  subst hb_eq
  rw [← mallocngBlockProg_eq_b09]
  refine SepWP.mono
    (mallocImpl_join_epilogue_raw hcl_u hNoOrph2 hwf2 hNoRes2
      hg2 hSlotsPos2 hClaimed2 hReqMax (hFitNew m mb)
      (fun ⟨_, hlt48⟩ => by omega)
      (fun h24 => by omega)
      (fun _ => by rw [hMap2]; exact hMapBound)
      hZeroMm2 hDelta_u
      hpc_u hrun_u hsp_u hsp_align hProc_u hcs_u
      hx0_u hx19_u hx20_u
      (by simpa using hx21_u)
      (by simpa [gNew, mkLargeGroup] using hx22_u)
      (by simpa using hx23_u))
    ?_
  rintro sf P_f _ _
    ⟨hsf_sp, _, _, hsf_proc, hsf_cs, hcl_f, hAcct_f,
      st', cg, p, bs, live', peak', hsf_x0, hBlkWf, _, hZeroBs,
      hFresh2, hLiveOut, hMetaOut, hCgDef, hGroupsOut, hNoOrphOut, hPf⟩
  have hLive2Eq : st2.liveMap = st0.liveMap := by
    change st1.liveMap = st0.liveMap
    exact hLive1.trans hSeqLiveEq
  have hFresh0 : st0.liveMap p = none := hLive2Eq ▸ hFresh2
  have hLiveFinal : st'.liveMap = st0.liveMap.insert p req 0 := by
    rw [hLiveOut, hLive2Eq]
  have hMetaFinal : st'.metaAreas.length ≤ maxMetaAreas := by
    have hEqM : st'.metaAreas.length = st1.metaAreas.length := by
      rw [hMetaOut]
      exact hMetaLen2
    omega
  have hMapPos : 0 < len / 4096 := by omega
  have hCgMm : cg.isMmapped = true := by
    rw [hCgDef]
    dsimp only [GroupDesc.isMmapped, mkReplaceSlotGroup, gNew, mkLargeGroup]
    simp only [beq_self_eq_true, Bool.true_or]
  have hBsEq : bs = List.replicate req 0#8 := hZeroBs hCgMm
  subst hBsEq
  have hGroupsHead : st'.groups = cg :: st0.groups := by
    have hMapHd : (gNew :: st1.groups).map (fun x => if x.metaPtr == gNew.metaPtr then cg else x) =
        cg :: st1.groups :=
      map_replace_head_of_nodup hwf2.groups_nodup.1
    calc st'.groups
      _ = (gNew :: st1.groups).map (fun x => if x.metaPtr == gNew.metaPtr then cg else x) := hGroupsOut
      _ = cg :: st1.groups := hMapHd
      _ = cg :: st_seq.groups := by rw [hGrps1]
      _ = cg :: st0.groups := by rw [hSeqGroupsEq]
  have hCgSc : cg.sc = 63 := by rw [hCgDef]; rfl
  have hCgParent : cg.parentMeta = none := by rw [hCgDef]; rfl
  have hCgNested : cg.nestedCap = 0 := by rw [hCgDef]; rfl
  have hCgLast : cg.lastIdx = 0 := by rw [hCgDef]; rfl
  have hCgMapPos : 0 < cg.maplen := by
    rw [hCgDef]
    change 0 < len / 4096
    exact hMapPos
  have hCgMapBytes : cg.maplen * 4096 = ((req + 20 + 4095) / 4096) * 4096 := by
    rw [hCgDef]
    change (len / 4096) * 4096 = ((req + 20 + 4095) / 4096) * 4096
    rw [← hLenEq]
    omega
  have hCgSlots : cg.slots = [.liveUser p req (max req MallocngMinBlockCost)] := by
    rw [hCgDef]
    simp [mkReplaceSlotGroup, mkLargeGroup]
  exact ⟨st', cg, p, live', peak', hsf_sp, hsf_cs, hsf_proc, hsf_x0, hcl_f, hAcct_f,
    hNoOrphOut, hPf, hGroupsHead, ⟨st0, hGroupsHead, FineSameGroupsSlotKind.refl st0.groups⟩,
    hCgSc, hCgParent, hCgNested, hCgLast, hCgMapPos, hCgMapBytes, hCgSlots,
    hFresh0, hLiveFinal, hMetaFinal, hBlkWf,
    hBlkWf.1, bv_and_15_eq_zero_of_dvd16 p hBlkWf.2.1, hBlkWf.2.2.1⟩

end LibsignalBinary.Heap.Fine
