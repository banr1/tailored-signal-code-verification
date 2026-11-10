/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotHelpers3

/-!
# Stage 1 Symbolic Execution for Outer `alloc_slot`

Defines symbolic instruction offsets and `mallocngFaultSvc` `SepWP` block lemmas for the inner
loops and helpers of outer `alloc_slot` (block `8`, `+0x108..+0x1ec`), including `stlxr` retry,
group activation, `pageSpanSteps` active-index bumping, and fast-pop effective-cost preservation.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Symbolic Instruction Offsets (`+0x000..+0x278`) -/

abbrev allocSlotOff_slow_head   : BitVec 64 := words_insn_off% blk08Words 0xa90153f3#32 0
abbrev allocSlotOff_deq_tail    : BitVec 64 := words_insn_off% blk08Words 0x910002c0#32 0
abbrev allocSlotOff_a8          : BitVec 64 := words_insn_off% blk08Words 0x39408041#32
abbrev allocSlotOff_c8          : BitVec 64 := words_insn_off% blk08Words 0xf9400845#32
abbrev allocSlotOff_activate    : BitVec 64 := words_insn_off% blk08Words 0xb9401840#32 1
abbrev allocSlotOff_11c         : BitVec 64 := words_insn_off% blk08Words 0x39402000#32
abbrev allocSlotOff_134         : BitVec 64 := words_insn_off% blk08Words 0x362ffca1#32
abbrev allocSlotOff_bump        : BitVec 64 := words_insn_off% blk08Words 0x79404081#32
abbrev allocSlotOff_ps_loop     : BitVec 64 := words_insn_off% blk08Words 0x11000463#32 0
abbrev allocSlotOff_ps_body     : BitVec 64 := words_insn_off% blk08Words 0x0b0100c2#32
abbrev allocSlotOff_ps_done     : BitVec 64 := words_insn_off% blk08Words 0x39408080#32
abbrev allocSlotOff_19c         : BitVec 64 := words_insn_off% blk08Words 0x394020a1#32 1
abbrev allocSlotOff_stxr_entry  : BitVec 64 := words_insn_off% blk08Words 0xb9401c41#32
abbrev allocSlotOff_stxr_loop   : BitVec 64 := words_insn_off% blk08Words 0x885ffca6#32
abbrev allocSlotOff_stxr_store  : BitVec 64 := words_insn_off% blk08Words 0x8806fca4#32
abbrev allocSlotOff_stxr_after  : BitVec 64 := words_insn_off% blk08Words 0x35ffff86#32
abbrev allocSlotOff_act_store   : BitVec 64 := words_insn_off% blk08Words 0x0a010000#32
abbrev allocSlotOff_bounces_chk : BitVec 64 := words_insn_off% blk08Words 0x79404041#32
abbrev allocSlotOff_restore4    : BitVec 64 := words_insn_off% blk08Words 0xa94153f3#32 0
abbrev allocSlotOff_fast_pop    : BitVec 64 := words_insn_off% blk08Words 0x4b0003e3#32 0
abbrev allocSlotOff_bounces_go  : BitVec 64 := words_insn_off% blk08Words 0x910002c3#32 1

/-! ## `.rodata` and Bitvector Arithmetic Helpers -/

theorem split_debruijnFree_ro (dbAddr : BitVec 64) {idx : Nat} (hidx : idx < 32) (R : SepProp) :
    ∃ Rest : SepProp, ((dbAddr ↦ᵣ mallocngDebruijn32Table) ∗ R) =
      (((dbAddr + BitVec.ofNat 64 idx) ↦₈ᵣ debruijn32Table.getD idx 0#8) ∗ Rest ∗ R) := by
  have hlen : idx + 1 ≤ debruijn32Table.length := by rw [debruijn32Table_length]; omega
  refine ⟨(dbAddr ↦ᵣ debruijn32Table.take idx) ∗
    ((dbAddr + BitVec.ofNat 64 (idx + 1)) ↦ᵣ debruijn32Table.drop (idx + 1)), ?_⟩
  change ((dbAddr ↦ᵣ debruijn32Table) ∗ R) = _
  rw [pointsToBytesRO_split3 dbAddr debruijn32Table idx 1 hlen,
    pointsToBytesRO_take1_eq_pointsTo8RO _ _ _ hlen]
  simp only [sepConj_assoc]

theorem split_roTables_debruijnFree (A : MallocngAddrs) {idx : Nat} (hidx : idx < 32) (R : SepProp) :
    ∃ Rest : SepProp, (MallocngRoTablesA A ∗ R) =
      (((A.debruijnFree + BitVec.ofNat 64 idx) ↦₈ᵣ debruijn32Table.getD idx 0#8) ∗ Rest ∗ R) := by
  obtain ⟨Rest0, h0⟩ := split_debruijnFree_ro A.debruijnFree hidx
    ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
     (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
     (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
     (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ R)
  refine ⟨Rest0 ∗ (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
    (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
    (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
    (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table), ?_⟩
  have hPerm : (MallocngRoTablesA A ∗ R) =
      ((A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
       ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ R)) := by
    simp only [MallocngRoTablesA, MallocngRoTablesAt, sepConj_assoc]
    generalize (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) = S0
    generalize (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) = S1
    generalize (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) = S2
    generalize (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = S3
    generalize (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = S4
    ac_rfl
  rw [hPerm, h0]
  simp only [sepConj_assoc]

theorem split_roTables_sizeClass (A : MallocngAddrs) {sc : Nat} (hsc : sc < 48) (R : SepProp) :
    ∃ Rest : SepProp, (MallocngRoTablesA A ∗ R) =
      (((A.sizeClasses + BitVec.ofNat 64 (2 * sc)) ↦₁₆ᵣ BitVec.ofNat 16 (sizeClass sc)) ∗ Rest ∗ R) := by
  obtain ⟨Rest0, h0⟩ := split_sizeClass_ro A.sizeClasses hsc
    ((A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
     (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
     (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
     (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ R)
  refine ⟨Rest0 ∗ (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
    (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
    (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
    (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table), ?_⟩
  have hPerm : (MallocngRoTablesA A ∗ R) =
      ((A.sizeClasses ↦ᵣ sizeClassBytes) ∗
       ((A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ R)) := by
    simp only [MallocngRoTablesA, MallocngRoTablesAt, sizeClassBytes, sepConj_assoc]
  rw [hPerm, h0]
  simp only [sepConj_assoc]

theorem fastPop_bv_props {av : BitVec 32} (hAvNe : av ≠ 0#32) :
    let iso := (-av) &&& av
    let hashIdx := ((iso * 0x076be629#32) >>> 27).toNat
    (0#32 - av) &&& av ≠ 0#32 ∧
    av &&& ~~~(0#32 - av) = av - iso ∧
    ((0#32 - ((0#32 - av) &&& av)) &&& ((0#32 - av) &&& av)) = iso ∧
    hashIdx < 32 ∧
    BitVec.zeroExtend 64 (((0#32 + iso * 0x076be629#32) >>> 27)) = BitVec.ofNat 64 hashIdx ∧
    debruijn32Table.getD hashIdx 0#8 = BitVec.ofNat 8 (ctz32DeBruijn av) ∧
    ctz32DeBruijn av < 32 := by
  dsimp only
  obtain ⟨hIsoNe, hIdx32, hHashLt, _, hNegIso, _, _, _⟩ := ctz32DeBruijn_spec hAvNe
  have h0 : 0#32 - av = -av := BitVec.zero_sub av
  have hBic : av &&& ~~~(-av) = av - ((-av) &&& av) := by bv_robdd
  have hZ : BitVec.zeroExtend 64 ((0#32 + ((-av) &&& av) * 0x076be629#32) >>> 27) =
      BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat := by
    rw [BitVec.zero_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hDb : debruijn32Table.getD ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat 0#8 =
      BitVec.ofNat 8 (ctz32DeBruijn av) := by
    let b := debruijn32Table.getD ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat 0#8
    change b = BitVec.ofNat 8 b.toNat
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt]
  rw [h0]
  rw [BitVec.zero_sub]
  exact ⟨hIsoNe, hBic, hNegIso, hHashLt, hZ, hDb, hIdx32⟩

theorem pageSpan_cond_eq (e : BitVec 32) :
    e.sle 0xfff#32 = e.slt 4096#32 := by
  bv_robdd

private theorem bounces_sc_all :
    ((List.range 48).all fun sc =>
      let w1 := BitVec.ofNat 32 sc - 7#32
      (w1.ule 0x1f#32 == decide (7 ≤ sc ∧ sc < 39)) &&
      (if 7 ≤ sc ∧ sc < 39 then BitVec.signExtend 64 w1 == BitVec.ofNat 64 (sc - 7) else true)) = true := by
  decide +kernel

theorem bounces_bv_props (ctx : BitVec 64) {sc : Nat} (hsc : sc < 48) :
    let w1 := BitVec.ofNat 32 sc - 7#32
    (w1.ule 0x1f#32 = true ↔ (7 ≤ sc ∧ sc < 39)) ∧
    (7 ≤ sc → sc < 39 →
      sc - 7 < 32 ∧
      ctx + BitVec.signExtend 64 w1 + 0x370#64 =
        ctx + 880#64 + BitVec.ofNat 64 (sc - 7)) := by
  dsimp only
  have h := List.all_eq_true.mp bounces_sc_all sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨by rw [h.1, decide_eq_true_eq], fun hLo hHi => ⟨by omega, ?_⟩⟩
  have h2 := h.2
  simp only [hLo, hHi, and_self, ↓reduceIte, beq_iff_eq] at h2
  rw [h2]; bv_omega

theorem bump_clamp_props {lastIdx activeIdx : Nat} {cntF : BitVec 32} (oldAct : BitVec 8)
    (hLast : lastIdx ≤ 31) (hLt : activeIdx < lastIdx)
    (hLo : activeIdx + 2 ≤ cntF.toNat) (hHi : cntF.toNat ≤ 300) :
    let wMax := BitVec.ofNat 32 (lastIdx + 1)
    let wSel := if wMax.sle cntF then wMax else cntF
    let wNew := wSel - 1#32
    let newAct : BitVec 8 := (oldAct &&& 0xe0#8) ||| (wNew.truncate 8 &&& 0x1f#8)
    activeIdx + 1 ≤ (newAct &&& 0x1f#8).toNat ∧
    (newAct &&& 0x1f#8).toNat ≤ lastIdx := by
  dsimp only
  have hMaxInt : (BitVec.ofNat 32 (lastIdx + 1)).toInt = (lastIdx + 1 : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    have : (BitVec.ofNat 32 (lastIdx + 1)).toNat = lastIdx + 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [this]; split <;> omega
  have hCntInt : cntF.toInt = (cntF.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hSle : (BitVec.ofNat 32 (lastIdx + 1)).sle cntF = decide (lastIdx + 1 ≤ cntF.toNat) := by
    rw [BitVec.sle, hMaxInt, hCntInt]; simp only [decide_eq_decide]; omega
  rw [hSle]
  let m := if lastIdx + 1 ≤ cntF.toNat then lastIdx + 1 else cntF.toNat
  have hmLo : activeIdx + 2 ≤ m := by dsimp [m]; split <;> omega
  have hmHi : m ≤ lastIdx + 1 := by dsimp [m]; split <;> omega
  have hSelEq : (if decide (lastIdx + 1 ≤ cntF.toNat) = true then BitVec.ofNat 32 (lastIdx + 1) else cntF) =
      BitVec.ofNat 32 m := by
    by_cases hC : lastIdx + 1 ≤ cntF.toNat
    · simp [m, hC]
    · simp only [m, hC, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cntF.isLt]
  rw [hSelEq]
  have hSubNat : (BitVec.ofNat 32 m - 1#32).toNat = m - 1 := by bv_omega
  have hTruncEq : ((BitVec.ofNat 32 m - 1#32).truncate 8 &&& 0x1f#8) = BitVec.ofNat 8 (m - 1) := by
    apply BitVec.eq_of_toNat_eq
    change ((BitVec.ofNat 32 m - 1#32).toNat % 256) &&& 31 = (m - 1) % 256
    rw [hSubNat, Nat.mod_eq_of_lt (by omega : m - 1 < 256),
        show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : m - 1 < 32)]
  have hMask : (((oldAct &&& 0xe0#8) ||| BitVec.ofNat 8 (m - 1)) &&& 0x1f#8) =
      BitVec.ofNat 8 (m - 1) &&& 0x1f#8 := by bv_robdd
  have hAndId : BitVec.ofNat 8 (m - 1) &&& 0x1f#8 = BitVec.ofNat 8 (m - 1) := by
    apply BitVec.eq_of_toNat_eq
    change ((m - 1) % 256) &&& 31 = (m - 1) % 256
    rw [Nat.mod_eq_of_lt (by omega : m - 1 < 256),
        show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : m - 1 < 32)]
  rw [hTruncEq, hMask, hAndId, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m - 1 < 256)]
  omega

arm64_proof_prelude
set_option diagnostics false

/-! ## `pageSpanSteps` Loop and `stlxr` Retry Loop Helpers -/

theorem wp_allocSlot_pageSpan_loop [MallocngMultiPlacement]
    {fuel : Nat} {stride cnt span cntF spanF : BitVec 32}
    (hps : pageSpanSteps stride fuel cnt span = some (cntF, spanF))
    (_hw348 : Blk08HasWords348 mallocngFaultSvc) (_hr348 : Blk08Range348)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_ps_body) (hrun : s.status = .Running)
    (hw6 : s.readReg32 .x6 = stride)
    (hw3 : s.readReg32 .x3 = cnt)
    (hw1 : s.readReg32 .x1 = span) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_ps_done) s Frame
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧ sf.mem = s.mem ∧
        sf.readReg32 .x3 = cntF ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  induction fuel generalizing cnt span s with
  | zero => simp [pageSpanSteps] at hps
  | succ fuel ih =>
    have hw6' : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 6#5)) = stride := hw6
    have hw3' : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 3#5)) = cnt := hw3
    have hw1' : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 1#5)) = span := hw1
    simp only [pageSpanSteps] at hps
    dsimp only [allocSlotOff_ps_body, allocSlotOff_ps_done] at hpc ⊢
    wp_sym_steps
    wp_if hle
    · have hCond : ((stride + span - 1#32) ^^^ span).slt 4096#32 = true := by
        rw [← pageSpan_cond_eq]; exact hle
      simp only [hCond, ↓reduceIte] at hps
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_ps_body)
        (Mid := fun sj Pj =>
          sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.mem = s.mem ∧
          sj.readReg32 .x6 = stride ∧ sj.readReg32 .x3 = cnt + 1#32 ∧
          sj.readReg32 .x1 = stride + span ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → sj.readReg64 r = s.readReg64 r) ∧
          Pj = Frame) ?_ ?_
      · dsimp only [allocSlotOff_ps_body]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun])
          ⟨by simp, by simp [State.spAligned], psp_rfl, rfl,
           by simpa [State.readReg32] using hw6',
           by simp [State.readReg32, BitVec.truncate_eq_setWidth, hw3'],
           by simp [State.readReg32, BitVec.truncate_eq_setWidth],
           fun r r0 r1 r2 r3 => ?_, rfl⟩
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3,
          State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r2]
      · rintro sj Pj hjpc hjrun ⟨hsp1, hal1, hpsp1, hmem1, hj6, hj3, hj1, hr1, rfl⟩
        refine SepWP.mono (ih hps sj hjpc hjrun hj6 hj3 hj1) ?_
        rintro sf P_f _ _ ⟨hf1, hf2, hf3, hpsp2, hmem2, hcF, hr2, hPf⟩
        refine ⟨hf1, hf2.trans hsp1, hf3.trans hal1, hpsp1.trans hpsp2, hmem2.trans hmem1, hcF,
          fun r r0 r1 r2 r3 => (hr2 r r0 r1 r2 r3).trans (hr1 r r0 r1 r2 r3), hPf⟩
    · have hCond : ((stride + span - 1#32) ^^^ span).slt 4096#32 = false := by
        rw [← pageSpan_cond_eq]; exact Bool.eq_false_iff.mpr hle
      simp only [hCond, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hps
      rcases hps with ⟨rfl, rfl⟩
      refine SepWP.done rfl (by simp [hrun])
        ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, rfl,
         by simpa [State.readReg32] using hw3', fun r r0 r1 r2 r3 => ?_, rfl⟩
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r2]

private theorem step_stxr32_either {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {v0 val : BitVec 32} {rel : Bool} {rs rn rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true) (hval : s.readReg32 rt = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64)).setMem m')
        ((ea ↦₃₂ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true →
      SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 rs 1#64).setPC (pc + 4#64))
        ((ea ↦₃₂ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .W32 rel rs rn rt) s =
        ((s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64)).setMem (s.mem.write32 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, htrunc,
        MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, State.setMem, hpc]
    rw [hstep]
    refine SepWP.to_reaches_pc
      (hok hf _ (Memory.perm_write32 s.mem ea val) (Memory.keepsFrozen_write32 hcw val)) ?_
    rw [sepConj_assoc]
    exact (IsBlock.pointsTo32 ea v0).write32 hm' val
  · have hstep : prog.evalInst (.stxr .W32 rel rs rn rt) s =
        (s.stepExclOracle.writeReg .W32 rs 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf,
        MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, hpc]
    rw [hstep]
    exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)

private theorem exclFails_tail_lt_slot {s : State} {k : Nat}
    (hk : s.exclFails.length < k + 1) (hf : s.exclWillFail = true) :
    s.exclFails.tail.length < k := by
  cases h : s.exclFails with
  | nil => simp [State.exclWillFail_eq_headD, h] at hf
  | cons _ tl => simp [h] at hk ⊢; omega

theorem wp_allocSlot_stxr_loop [MallocngMultiPlacement]
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (_hr348 : Blk08Range348) :
    ∀ (k : Nat) (s : State) (ea : BitVec 64) (oldVal newVal : BitVec 32) (Frame : SepProp),
      s.exclFails.length < k →
      s.pc = mbase 8 + allocSlotOff_stxr_loop → s.status = .Running →
      MemWidth.isAligned .W32 ea = true →
      s.readReg64 .x5 = ea →
      s.readReg64 .x1 = BitVec.zeroExtend 64 oldVal →
      s.readReg64 .x4 = BitVec.zeroExtend 64 newVal →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
        (mbase 8 + allocSlotOff_act_store) s
        (((ea ↦₃₂ oldVal) ∗ Frame))
        (fun sf P_f =>
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧ sf.mem.perm = s.mem.perm ∧
          (∀ r, r ≠ .x6 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = ((ea ↦₃₂ newVal) ∗ Frame))
        (fun _ => ⌜False⌝) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ hk; omega
  | succ k ih =>
    intro s ea oldVal newVal Frame hk hpc hrun hAlign hx5 hx1 hx4
    have hRelNil : blk08Relocs348 = [] := by decide
    have hw348' : ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc).hasWords
        (mbase 8 + 348#64) blk08Words348 := by
      simpa [hRelNil, Obj.patchRelocs] using hw348
    have hFetchStxr : ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc).fetch
        (mbase 8 + allocSlotOff_stxr_store) = some (.stxr .W32 true .x6 .x5 .x4) :=
      Program.fetch_of_hasWords_decodeAt 31 hw348' (by dsimp [allocSlotOff_stxr_store]; bv_omega) (by decide)
    dsimp only [allocSlotOff_stxr_loop, allocSlotOff_act_store] at hpc ⊢
    wp_sym_steps
    refine step_stxr32_either (pc := mbase 8 + allocSlotOff_stxr_store) (val := newVal)
      rfl (by simp [hrun])
      hFetchStxr rfl (by simpa using hx5) hAlign
      (by simp [State.readReg32, BitVec.truncate_eq_setWidth, hx4]) ?_ ?_
    · intro _ m' hperm' _
      have hpcNext : mbase 8 + allocSlotOff_stxr_store + 4#64 = mbase 8 + allocSlotOff_stxr_after := by
        dsimp [allocSlotOff_stxr_store, allocSlotOff_stxr_after]; bv_omega
      rw [hpcNext]; dsimp only [allocSlotOff_stxr_after]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun])
        ⟨by simp [hrun], by simp [State.stepExclOracle, State.writeReg],
         by simp [State.spAligned, State.stepExclOracle, State.writeReg],
         by simp [PureStatePres, MallocngProcPreserved, calleeSavedVRegs, State.stepExclOracle, State.writeReg],
         by simpa [State.stepExclOracle, State.writeReg] using hperm',
         fun r hr6 => ?_, rfl⟩
      simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
        State.readReg64_stepExclOracle, State.writeReg,
        State.readReg64_writeReg64_ne _ _ _ _ hr6]
    · intro hf
      have hpcNext : mbase 8 + allocSlotOff_stxr_store + 4#64 = mbase 8 + allocSlotOff_stxr_after := by
        dsimp [allocSlotOff_stxr_store, allocSlotOff_stxr_after]; bv_omega
      rw [hpcNext]; dsimp only [allocSlotOff_stxr_after]
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_stxr_loop)
        (Mid := fun sj Pj =>
          sj.exclFails.length < k ∧
          sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
          sj.mem.perm = s.mem.perm ∧
          (∀ r, r ≠ .x6 → sj.readReg64 r = s.readReg64 r) ∧
          Pj = ((ea ↦₃₂ oldVal) ∗ Frame)) ?_ ?_
      · dsimp only [allocSlotOff_stxr_loop]
        wp_sym_steps
        have hTailLt : s.exclFails.tail.length < k :=
          exclFails_tail_lt_slot hk (by simpa [State.exclWillFail_eq_headD] using hf)
        refine SepWP.done rfl (by simp [hrun])
          ⟨by simpa [State.stepExclOracle, State.writeReg] using hTailLt,
           by simp [State.stepExclOracle, State.writeReg],
           by simp [State.spAligned, State.stepExclOracle, State.writeReg],
           by simp [PureStatePres, MallocngProcPreserved, calleeSavedVRegs, State.stepExclOracle, State.writeReg],
           by simp [State.stepExclOracle, State.writeReg], fun r hr6 => ?_, rfl⟩
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_stepExclOracle, State.writeReg,
          State.readReg64_writeReg64_ne _ _ _ _ hr6]
      · rintro sj Pj hjpc hjrun ⟨hkj, hspj, halj, hpspj, hpermj, hrj, rfl⟩
        refine SepWP.mono (ih sj ea oldVal newVal Frame hkj hjpc hjrun hAlign
          ((hrj .x5 (by decide)).trans hx5)
          ((hrj .x1 (by decide)).trans hx1)
          ((hrj .x4 (by decide)).trans hx4)) ?_
        rintro sf P_f _ _ ⟨hf1, hf2, hf3, hpsp2, hperm2, hr2, hPf⟩
        refine ⟨hf1, hf2.trans hspj, hf3.trans halj, hpspj.trans hpsp2,
          hperm2.trans hpermj, fun r hr6 => (hr2 r hr6).trans (hrj r hr6), hPf⟩

/-! ## `ByteMap` Read-Focus Helpers and `activate_group` (`+0x108..+0x1ec`) -/

theorem byteMap_focus_meta {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    ∃ Rest : SepProp,
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ Rest) := by
  obtain ⟨_, _, _, hMRead, hMOwn⟩ := meta_ownedRw_of_mem_groups hwf hg
  refine ⟨ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal, ?_⟩
  rw [← hMRead]
  exact (slot_byteMap_update40 hwf.masterDom_wf.1 st.byteVal
    (readBytesFromMap_length st.byteVal g.metaPtr 40) hMOwn).1

theorem byteMap_focus_activeByte {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    ∃ Rest : SepProp,
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        (((g.mem + 8#64) ↦₈ g.activeByte) ∗ Rest) := by
  have hgWf := hwf.groups_wf g hg
  have hGsG := group_slot_toNat hgWf
  obtain ⟨gr, hgr, hgrPos, _, hEndLe, _⟩ := group_root_containment hwf hg
  have hGrBnd := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
  have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
  have hEndGe : g.mem.toNat + 28 ≤ (g.slotEnd g.lastIdx).toNat := by
    rw [hGsG.2.2.2.1]; have := Nat.mul_le_mul hGsG.2.1 hGsG.1; omega
  have haNat : (g.mem + 8#64).toNat = g.mem.toNat + 8 := add_ofNat_toNat (by omega)
  obtain ⟨_, hActRead, hHdrOwn⟩ := group_header_ownedRw hwf hg
  have hSub : ∀ a, InRegion (g.mem + 8#64) 1 a → OwnedRwByte st a ∧ a ∈ st.masterDom := by
    intro a ha
    have hb := (inRegion_bounds (by omega)).mp ha
    exact hHdrOwn a ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
  refine ⟨ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.mem + 8#64) 1 a) st.byteVal, ?_⟩
  have hExt := ByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal (g.mem + 8#64)
    (by decide : 1 ≤ 2 ^ 64) (fun a ha => (hSub a ha).2) (fun a ha => (hSub a ha).1)
  have hRd1 : readBytesFromMap st.byteVal (g.mem + 8#64) 1 = [g.activeByte] := by
    simp [readBytesFromMap, rangeAddrs, hActRead]
  rw [hExt, hRd1, pointsToBytes_singleton]

private theorem metaPtr_add28_aligned {m : BitVec 64}
    (hMod8 : m.toNat % 8 = 0) (hBnd : m.toNat + 40 ≤ 2 ^ 48) :
    MemWidth.isAligned .W32 (m + 28#64) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  change ((m + 28#64).toNat &&& 3) = 0
  rw [add_ofNat_toNat (by omega), show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

def MallocngCoreFixedA (γ : GhostName) (A : MallocngAddrs) (st : MallocngSt) : SepProp :=
  MallocngLiveAuth γ st.liveMap ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
  MallocngAuxvState γ st.auxvPtr st.auxvSnap

theorem sepWP_coreSt_wf {prog : Program} {exit_pc : BitVec 64} {s : State}
    {inflight : Nat} {γ : GhostName} {A : MallocngAddrs} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : MallocngWFInflight inflight A.base brkStart s.brk liveCost peakCost st →
      SepWP prog exit_pc s
        (MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ Frame)
        post oom) :
    SepWP prog exit_pc s
      (MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ Frame)
      post oom := by
  conv => arg 4; simp only [MallocngCoreStInflightA, sepConj_assoc]
  apply SepWP.pure_elim
  intro hwf
  have hh := h hwf
  conv at hh => arg 4; simp only [MallocngCoreStInflightA, sepConj_assoc, pure_sepConj_of_true hwf]
  exact hh

theorem coreSt_eq_parts {inflight : Nat} {γ : GhostName} {A : MallocngAddrs}
    {brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st) :
    MallocngCoreStInflightA inflight γ A brkStart brk liveCost peakCost st =
      ((A.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st) ∗
       MallocngCoreFixedA γ A st) := by
  simp only [MallocngCoreStInflightA, MallocngCoreFixedA, pure_sepConj_of_true hwf]
  generalize MallocngLiveAuth γ st.liveMap = G0
  generalize (A.ctx ↦ₛ st.ctx.toBytes) = G1
  generalize (A.lock ↦₃₂ 0#32) = G2
  generalize (A.replaced ↦₃₂ 0#32) = G3
  generalize (A.aaReplaced ↦₃₂ 0#32) = G4
  generalize ((A.libc + 8#64) ↦₆₄ st.auxvPtr) = G5
  generalize MallocngAuxvState γ st.auxvPtr st.auxvSnap = G6
  generalize ByteMap st.masterDom (OwnedRwByte st) st.byteVal = G7
  generalize ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = G8
  generalize MappedSet st.masterDom (OwnedMappedByte st) = G9
  ac_rfl

/-- Shared pure-state invariants preserved by intra-`alloc_slot` transitions (`rotate`, `dequeue`,
    `bump_activeIdx`, `activate_group`, `dec_bounces`). -/
abbrev AllocSlotStPres (sc : Nat) (st0 st : MallocngSt) : Prop :=
  st.reservedMetas = st0.reservedMetas ∧
  st.liveMap = st0.liveMap ∧
  totalLiveEffCost st = totalLiveEffCost st0 ∧
  totalLiveCount st = totalLiveCount st0 ∧
  st.metaAreas = st0.metaAreas ∧
  dynamicRootRegions st = dynamicRootRegions st0 ∧
  st.ctx.active.length = st0.ctx.active.length ∧
  (∀ k : Nat, k < sc → ∀ hk1 : k < st.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
    st.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
  Cost.GroupsGrpMono st0.groups st.groups

theorem AllocSlotStPres.rfl {sc : Nat} {st : MallocngSt} : AllocSlotStPres sc st st :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, fun _ _ _ _ => Eq.refl _,
   Cost.GroupsGrpMono.refl _⟩

theorem AllocSlotStPres.trans {sc : Nat} {st0 st1 st2 : MallocngSt}
    (h01 : AllocSlotStPres sc st0 st1) (h12 : AllocSlotStPres sc st1 st2) : AllocSlotStPres sc st0 st2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   fun k hk hk2 hk0 => by
     have hk1 : k < st1.ctx.active.length := h01.2.2.2.2.2.2.1.symm ▸ hk0
     exact (h12.2.2.2.2.2.2.2.1 k hk hk2 hk1).trans (h01.2.2.2.2.2.2.2.1 k hk hk1 hk0),
   h01.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2⟩

theorem groupsGrpMono_map {gs : List GroupDesc} (f : GroupDesc → GroupDesc)
    (hf : ∀ g ∈ gs, (f g).sc = g.sc ∧ (f g).maplen ≤ g.maplen) :
    Cost.GroupsGrpMono gs (gs.map f) := fun _ hU => hU.map f hf

theorem groupsGrpMono_map_ite {gs : List GroupDesc} {g g1 : GroupDesc} (hg : g ∈ gs) (m : BitVec 64)
    (hSc : g1.sc = g.sc) (hMl : g1.maplen ≤ g.maplen) :
    Cost.GroupsGrpMono gs (gs.map fun h => if h.metaPtr == m then g1 else h) := fun _ hU =>
  hU.map_ite m fun hm hs => by
    rw [hSc] at hs ⊢
    exact Nat.le_trans (Nat.mul_le_mul_right _ hMl) (hU g hg (by omega) hs)

theorem wp_allocSlot_activate [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32)
    (hActFrNe : ((2#32 <<< g.activeIdx) - 1#32) &&& g.freedMask ≠ 0#32)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_activate) (hrun : s.status = .Running)
    (hx2 : s.readReg64 .x2 = g.metaPtr) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_bounces_chk) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          g1.metaPtr = g.metaPtr ∧ g1.sc = sc ∧ g1.availMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          sf.readReg64 .x0 = BitVec.zeroExtend 64 g1.availMask ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x6 →
            sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  obtain ⟨_, hMod8, hMBnd, _, _⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hAlign28 := metaPtr_add28_aligned hMod8 hMBnd
  obtain ⟨RestAct, hBmAct⟩ := byteMap_focus_activeByte hwf hg
  obtain ⟨hg1Mem, hwf1, hCnt1, hEff1, hDyn1, hProt1, hMap1, hBmExt, hBmAbs⟩ :=
    tryAvail_activate_group_absorb hwf hsc hg hScEq (hHead h1) hAv0
  let cntMask : BitVec 32 := (2#32 <<< g.activeIdx) - 1#32
  let hiMask : BitVec 32 := -(2#32 <<< g.activeIdx)
  let newAvail : BitVec 32 := cntMask &&& g.freedMask
  let newFreed : BitVec 32 := g.freedMask &&& hiMask
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_11c)
    (Mid := fun s1 P1 =>
      s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg64 .x0 = g.mem ∧ s1.readReg64 .x2 = g.metaPtr ∧
      s1.readReg64 .x3 = 2#64 ∧ s1.readReg64 .x5 = g.metaPtr + 28#64 ∧
      (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x5 → s1.readReg64 r = s.readReg64 r) ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
  · conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_activate, allocSlotOff_11c] at hpc ⊢
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], psp_rfl, rfl,
       by simp, by simpa using hx2, by simp, by simp,
       fun r r0 r3 r5 => ?_,
       by rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo, hAv0]; simp only [sepConj_assoc]⟩
    simp only [State.readReg64_setPC,
      State.readReg64_writeReg64_ne _ _ _ _ r5, State.readReg64_writeReg64_ne _ _ _ _ r3,
      State.readReg64_writeReg64_ne _ _ _ _ r0]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hmem1, hs1_0, hs1_2, hs1_3, hs1_5, hr1, rfl⟩
    refine SepWP.seq (mid := mbase 8 + allocSlotOff_stxr_entry)
      (Mid := fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ PureStatePres s s2 ∧ s2.mem = s.mem ∧
        s2.readReg64 .x0 = BitVec.zeroExtend 64 cntMask ∧
        s2.readReg64 .x2 = g.metaPtr ∧
        s2.readReg64 .x3 = BitVec.zeroExtend 64 hiMask ∧
        s2.readReg64 .x5 = g.metaPtr + 28#64 ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x5 → s2.readReg64 r = s.readReg64 r) ∧
        P2 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
    · have hw1_3 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 3#5)) = 2#32 := by simp [hs1_3]
      have hIdxNat : (g.activeByte.toNat % 4294967296 &&& 31) % 32 = g.activeByte.toNat &&& 31 := by
        have hLt4G : g.activeByte.toNat < 4294967296 := Nat.lt_trans g.activeByte.isLt (by decide)
        rw [Nat.mod_eq_of_lt hLt4G]
        have hAndLt : (g.activeByte.toNat &&& 31) < 32 := by
          rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_lt _ (by decide)
        exact Nat.mod_eq_of_lt hAndLt
      conv => arg 4; rw [coreSt_eq_parts hwf, hBmAct]; simp only [sepConj_assoc]
      dsimp only [allocSlotOff_11c, allocSlotOff_stxr_entry] at hpc1 ⊢
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simpa using hsp1, by simpa [State.spAligned] using hal1, hpsp1.trans psp_rfl, hmem1,
         by simp [cntMask, GroupDesc.activeIdx, hIdxNat],
         by simpa using hs1_2,
         by simp [hiMask, GroupDesc.activeIdx, hIdxNat],
         by simpa using hs1_5,
         fun r r0 r3 r5 => ?_,
         by rw [coreSt_eq_parts hwf, hBmAct]; simp only [sepConj_assoc]⟩
      refine Eq.trans ?_ (hr1 r r0 r3 r5)
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ r3, State.readReg64_writeReg64_ne _ _ _ _ r0]
    · rintro s2 P2 hpc2 hrun2 ⟨hsp2, hal2, hpsp2, hmem2, hs2_0, hs2_2, hs2_3, hs2_5, hr2, rfl⟩
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_stxr_loop)
        (Mid := fun s3 P3 =>
          s3.sp = s.sp ∧ s3.spAligned = s.spAligned ∧ PureStatePres s s3 ∧ s3.mem = s.mem ∧
          s3.readReg64 .x0 = BitVec.zeroExtend 64 cntMask ∧
          s3.readReg64 .x1 = BitVec.zeroExtend 64 g.freedMask ∧
          s3.readReg64 .x2 = g.metaPtr ∧
          s3.readReg64 .x4 = BitVec.zeroExtend 64 newFreed ∧
          s3.readReg64 .x5 = g.metaPtr + 28#64 ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s3.readReg64 r = s.readReg64 r) ∧
          P3 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame)) ?_ ?_
      · have hw2_3 : BitVec.setWidth 32 (s2.readReg64 (Reg.gpr 3#5)) = hiMask := by simp [hs2_3]
        conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]
        dsimp only [allocSlotOff_stxr_entry, allocSlotOff_stxr_loop] at hpc2 ⊢
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun2])
          ⟨by simpa using hsp2, by simpa [State.spAligned] using hal2, hpsp2.trans psp_rfl, hmem2,
           by simpa using hs2_0, by simp, by simpa using hs2_2,
           by simp [newFreed, hiMask], by simpa using hs2_5,
           fun r r0 r1 r3 r4 r5 => ?_,
           by rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]⟩
        refine Eq.trans ?_ (hr2 r r0 r3 r5)
        simp only [State.readReg64_setPC,
          State.readReg64_writeReg64_ne _ _ _ _ r4, State.readReg64_writeReg64_ne _ _ _ _ r1]
      · rintro s3 P3 hpc3 hrun3 ⟨hsp3, hal3, hpsp3, hmem3, hs3_0, hs3_1, hs3_2, hs3_4, hs3_5, hr3, rfl⟩
        let RestBm := ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal
        let StxrFrame : SepProp :=
          (g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
          ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
          ((g.metaPtr + 32#64) ↦₆₄ g.packedWord) ∗
          RestBm ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          MallocngCoreFixedA γ maddrs st ∗ Frame
        have hPreStxr : (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ Frame) =
            (((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ StxrFrame) := by
          rw [coreSt_eq_parts hwf, hBmExt, GroupDesc.metaBytes_pointsTo]
          simp only [StxrFrame, RestBm, sepConj_assoc]
          ac_rfl
        rw [hPreStxr]
        refine SepWP.seq
          (wp_allocSlot_stxr_loop hw348 hr348 (s3.exclFails.length + 1) s3
            (g.metaPtr + 28#64) g.freedMask newFreed StxrFrame (Nat.lt_succ_self _)
            hpc3 hrun3 hAlign28 hs3_5 hs3_1 hs3_4) ?_
        rintro s4 P4 hpc4 hrun4 ⟨_, hsp4, hal4, hpsp4, hperm4, hr4, rfl⟩
        have hs4_0 : s4.readReg64 .x0 = BitVec.zeroExtend 64 cntMask := (hr4 .x0 (by decide)).trans hs3_0
        have hs4_1 : s4.readReg64 .x1 = BitVec.zeroExtend 64 g.freedMask := (hr4 .x1 (by decide)).trans hs3_1
        have hs4_2 : s4.readReg64 .x2 = g.metaPtr := (hr4 .x2 (by decide)).trans hs3_2
        have hw4_0 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 0#5)) = cntMask := by simp [hs4_0]
        have hw4_1 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 1#5)) = g.freedMask := by simp [hs4_1]
        conv => arg 4; simp only [StxrFrame, sepConj_assoc]
        dsimp only [allocSlotOff_act_store, allocSlotOff_bounces_chk] at hpc4 ⊢
        wp_sym_steps
        let newSlots : List SlotState :=
          List.ofFn fun i : Fin g.slots.length =>
            if i.1 ≤ g.activeIdx ∧ g.slots[i.1]'i.2 = .freeInactive then .freeAvail else g.slots[i.1]'i.2
        let g1 : GroupDesc := { g with availMask := newAvail, freedMask := newFreed, slots := newSlots }
        let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g1 else u
        let h2L : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
        let st1 : MallocngSt :=
          { st with
            ctx := { st.ctx with active := st.ctx.active.set sc g.metaPtr }
            groups := st.groups.map fG
            activeLists := st.activeLists.set sc (st.activeLists[sc]'h2L)
            byteVal := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes }
        have hCtxEq : st1.ctx = st.ctx := by
          have hSetId : st.ctx.active.set sc g.metaPtr = st.ctx.active := by
            rw [← hHead h1, List.set_getElem_self]
          cases hc : st.ctx; simp [st1, hc] at hSetId ⊢; exact hSetId
        have hBrkEq : s4.brk = s.brk := (hpsp3.trans hpsp4).2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s4.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwf1
        refine SepWP.done rfl (by simp [hrun4])
          ⟨st1, g1, hg1Mem, by simp [hrun4], by simpa using hsp4.trans hsp3,
           by simpa [State.spAligned] using hal4.trans hal3,
           (hpsp3.trans hpsp4).trans psp_rfl,
           ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, by simp [hCtxEq], fun _ _ _ _ => by simp [hCtxEq],
            groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _)⟩,
           rfl, hScEq, hActFrNe,
           fun h1' => by simp [st1, g1],
           by simpa using hs4_2,
           by simp [g1, newAvail, cntMask, BitVec.and_comm],
           fun r r0 r1 r3 r4 r5 r6 => ?_, ?_⟩
        · refine Eq.trans ?_ ((hr4 r r6).trans (hr3 r r0 r1 r3 r4 r5))
          simp only [State.readReg64_setPC, State.readReg64_setMem,
            State.readReg64_writeReg64_ne _ _ _ _ r0]
        · simp only [State.setPC, State.setMem, State.writeReg64] at hwf1' ⊢
          have hMetaFold : (((g.metaPtr + 28#64) ↦₃₂ newFreed) ∗
              (g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
              (g.metaPtr + 16#64) ↦₆₄ g.mem ∗ ((g.metaPtr + 24#64) ↦₃₂ newAvail) ∗
              ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) = (g.metaPtr ↦ₛ g1.metaBytes) := by
            rw [GroupDesc.metaBytes_pointsTo g.metaPtr g1]
            have hPkd : g1.packedWord = g.packedWord := rfl
            rw [hPkd]; dsimp only [g1]; ac_rfl
          have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
          have hCtxPts : (maddrs.ctx ↦ₛ st.ctx.toBytes) = (maddrs.ctx ↦ₛ st1.ctx.toBytes) := by
            rw [hCtxEq]
          dsimp only [newAvail, cntMask] at hMetaFold
          rw [coreSt_eq_parts hwf1', ← hBmAbs, ← hMetaFold, hCtxPts, hProt1, hMap1, hFix]
          dsimp only [RestBm, st1, g1, fG, newSlots, newAvail, newFreed, cntMask, hiMask]
          simp only [sepConj_assoc]; ac_rfl

theorem split_m32_byte0 (m v : BitVec 64) (R : SepProp) :
    (((m + 32#64) ↦₆₄ v) ∗ R) =
      (((m + 32#64) ↦₈ v.extractLsb' 0 8) ∗
       ((m + 33#64) ↦ₛ (unpack64 v).tail) ∗ R) := by
  have hCons : unpack64 v = [v.extractLsb' 0 8] ++ (unpack64 v).tail := rfl
  have hAdd : m + 32#64 + 1#64 = m + 33#64 := by bv_omega
  conv => lhs; rw [pointsTo64_eq_pointsToBytes (m + 32#64) v, hCons,
      pointsToBytes_append, List.length_singleton, pointsToBytes_singleton, hAdd]
  simp only [sepConj_assoc]

private theorem sizeClass_stride_all :
    ((List.range 48).all fun sc =>
      ((BitVec.ofNat 64 (2 * sc) == (BitVec.ofNat 64 sc) <<< 1) &&
       ((BitVec.setWidth 32 (BitVec.ofNat 16 (sizeClass sc)) <<< 4) ==
         BitVec.ofNat 32 (slotStride sc)))) = true := by decide +kernel

private theorem sizeClass_stride_props {sc : Nat} (hsc : sc < 48) :
    BitVec.ofNat 64 (2 * sc) = (BitVec.ofNat 64 sc) <<< 1 ∧
    (BitVec.setWidth 32 (BitVec.ofNat 16 (sizeClass sc)) <<< 4) =
      BitVec.ofNat 32 (slotStride sc) := by
  have h := List.all_eq_true.mp sizeClass_stride_all sc (List.mem_range.mpr hsc)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

private theorem and_imm32_0x1f_byte (b0 : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 b0 &&& 0x1f0000001f#64) =
      b0.zeroExtend 32 &&& 0x1f#32 := by
  bv_robdd

private theorem bfxil_w32_0_5_byte (oldB : BitVec 8) (v : BitVec 32) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 oldB &&& 0xffffffffffffffe0#64 |||
        (BitVec.setWidth 64 v >>> 0 &&& 31#64)) =
    (oldB &&& 0xe0#8) ||| (v.truncate 8 &&& 0x1f#8) := by
  bv_robdd

theorem group_lastIdx_maplen_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    g.lastIdx ≤ 31 ∧ g.maplen < 2 ^ 52 := by
  have hgWf := hwf.groups_wf g hg
  refine ⟨hgWf.2.1, ?_⟩
  by_cases hPos : 0 < g.maplen
  · have hBnd := hgWf.2.2.2.2.2.2.1
    have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos]
    omega
  · omega

abbrev allocSlotOff_164 : BitVec 64 := words_insn_off% blk08Words 0x78617806#32

theorem wp_allocSlot_bump_active [MallocngMultiPlacement]
    (_hw0 : Blk08HasWords0 mallocngFaultSvc) (_hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hLt : g.activeIdx < g.lastIdx)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_bump) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = g.metaPtr) (hx5 : s.readReg64 .x5 = g.mem)
    (hw3 : s.readReg32 .x3 = BitVec.ofNat 32 g.activeIdx) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_activate) s
      (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       MallocngRoTablesA maddrs ∗ Frame)
      (fun sf P_f =>
        ∃ st1 : MallocngSt, ∃ g1 ∈ st1.groups,
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st1 ∧
          g1.metaPtr = g.metaPtr ∧ g1.sc = sc ∧ g1.availMask = 0#32 ∧
          ((2#32 <<< g1.activeIdx) - 1#32) &&& g1.freedMask ≠ 0#32 ∧
          (∀ h1 : sc < st1.ctx.active.length, st1.ctx.active[sc]'h1 = g1.metaPtr) ∧
          sf.readReg64 .x2 = g1.metaPtr ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x6 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = (MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st1 ∗
            MallocngRoTablesA maddrs ∗ Frame))
      (fun _ => ⌜False⌝) := by
  apply sepWP_coreSt_wf; intro hwf
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
  obtain ⟨hLast, hMapLt⟩ := group_lastIdx_maplen_bounds hwf hg
  have hScPos : 1 ≤ sc := ((hwf.active_wf sc h1 h2).2.2.2.2.2.2 g hg hScEq hLt).2
  obtain ⟨cntF, spanF, hPs, hCntLo, hCntHi⟩ :=
    pageSpanSteps_terminates hScPos hsc (by omega : g.activeIdx < 31)
  obtain ⟨RestMeta, hBmMeta⟩ := byteMap_focus_meta hwf hg
  refine SepWP.seq (mid := mbase 8 + allocSlotOff_164)
    (Mid := fun s1 P1 =>
      s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ PureStatePres s s1 ∧ s1.mem = s.mem ∧
      s1.readReg64 .x0 = maddrs.sizeClasses ∧
      s1.readReg64 .x1 = BitVec.ofNat 64 sc ∧
      s1.readReg32 .x3 = BitVec.ofNat 32 (g.activeIdx + 2) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → s1.readReg64 r = s.readReg64 r) ∧
      P1 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
        MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
  · have hw0_3 : BitVec.setWidth 32 (s.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 g.activeIdx := hw3
    have hPkdSc := (GroupDesc.packedWord_fields g hLast (by omega) hMapLt).2.2.2
    conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
    dsimp only [allocSlotOff_bump, allocSlotOff_164] at hpc ⊢
    wp_sym_steps
    refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
      (i := 8) (by decide) (off := 340) (rd := 0#5) (X := fun _ => none) (svc := mallocngFaultSvc)
      MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
    simp only [resolve_size_classes, show Obj.addSignedAddr maddrs.sizeClasses 0 = maddrs.sizeClasses from rfl,
      show BitVec.ofNat 64 (340 + 8) = 348#64 from rfl]
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], psp_rfl, rfl,
       by simp,
       by simp,
       by simp [State.readReg32, BitVec.truncate_eq_setWidth, hw0_3, BitVec.ofNat_add],
       fun r r0 r1 r3 => ?_,
       by rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32 g.metaPtr g.packedWord]⟩
    simp only [State.readReg64_setPC,
      State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3,
      State.readReg64_writeReg64_ne _ _ _ _ r0]
  · rintro s1 P1 hpc1 hrun1 ⟨hsp1, hal1, hpsp1, hmem1, hs1_0, hs1_1, hs1_3, hr1, rfl⟩
    obtain ⟨RestSc, hRoSc⟩ := split_roTables_sizeClass maddrs hsc Frame
    obtain ⟨hScOff, hStrideShift⟩ := sizeClass_stride_props hsc
    refine SepWP.seq (mid := mbase 8 + allocSlotOff_ps_body)
      (Mid := fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ PureStatePres s s2 ∧ s2.mem = s.mem ∧
        s2.readReg32 .x6 = BitVec.ofNat 32 (slotStride sc) ∧
        s2.readReg32 .x3 = BitVec.ofNat 32 (g.activeIdx + 2) ∧
        s2.readReg32 .x1 = BitVec.ofNat 32 (g.activeIdx + 2) * BitVec.ofNat 32 (slotStride sc) + 16#32 ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → s2.readReg64 r = s.readReg64 r) ∧
        P2 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
          MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
    · have hw1_3 : BitVec.setWidth 32 (s1.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (g.activeIdx + 2) := hs1_3
      conv => arg 4; rw [hRoSc, hScOff]; simp only [sepConj_assoc]
      dsimp only [allocSlotOff_164, allocSlotOff_ps_body] at hpc1 ⊢
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun1])
        ⟨by simpa using hsp1, by simpa [State.spAligned] using hal1, hpsp1.trans psp_rfl, hmem1,
         by simpa [State.readReg32, BitVec.truncate_eq_setWidth] using hStrideShift,
         by simpa [State.readReg32] using hs1_3,
         by simp [State.readReg32, BitVec.truncate_eq_setWidth, hw1_3, hStrideShift],
         fun r r0 r1 r3 r6 => ?_,
         by rw [hRoSc, hScOff]⟩
      refine Eq.trans ?_ (hr1 r r0 r1 r3)
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r0,
        State.readReg64_writeReg64_ne _ _ _ _ r6]
    · rintro s2 P2 hpc2 hrun2 ⟨hsp2, hal2, hpsp2, hmem2, hs2_6, hs2_3, hs2_1, hr2, rfl⟩
      refine SepWP.seq
        (wp_allocSlot_pageSpan_loop hPs hw348 hr348 s2 _ hpc2 hrun2 hs2_6 hs2_3 hs2_1) ?_
      rintro s3 P3 hpc3 hrun3 ⟨_, hsp3, hal3, hpsp3, hmem3, hs3_3, hr3, rfl⟩
      have hs3_4 : s3.readReg64 .x4 = g.metaPtr :=
        (hr3 .x4 (by decide) (by decide) (by decide) (by decide)).trans
          ((hr2 .x4 (by decide) (by decide) (by decide) (by decide)).trans hx4)
      have hs3_5 : s3.readReg64 .x5 = g.mem :=
        (hr3 .x5 (by decide) (by decide) (by decide) (by decide)).trans
          ((hr2 .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5)
      refine SepWP.seq (mid := mbase 8 + allocSlotOff_19c)
        (Mid := fun s4 P4 =>
          s4.sp = s.sp ∧ s4.spAligned = s.spAligned ∧ PureStatePres s s4 ∧ s4.mem = s.mem ∧
          s4.readReg64 .x0 = BitVec.zeroExtend 64 (g.packedWord.extractLsb' 0 8) ∧
          s4.readReg64 .x2 = g.metaPtr ∧
          s4.readReg32 .x3 = cntF ∧
          s4.readReg64 .x5 = g.mem ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x6 → s4.readReg64 r = s.readReg64 r) ∧
          P4 = (MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
            MallocngRoTablesA maddrs ∗ Frame)) ?_ ?_
      · conv => arg 4; rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]; simp only [sepConj_assoc]
        dsimp only [allocSlotOff_ps_done, allocSlotOff_19c] at hpc3 ⊢
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun3])
          ⟨by simpa using hsp3.trans hsp2, by simpa [State.spAligned] using hal3.trans hal2,
           (hpsp2.trans hpsp3).trans psp_rfl, hmem3.trans hmem2,
           by simp, by simp,
           by simpa [State.readReg32] using hs3_3, by simpa using hs3_5,
           fun r r0 r1 r2 r3 r6 => ?_,
           by rw [coreSt_eq_parts hwf, hBmMeta, GroupDesc.metaBytes_pointsTo]; simp only [sepConj_assoc]; rw [split_m32_byte0 g.metaPtr g.packedWord]⟩
        refine Eq.trans ?_ ((hr3 r r0 r1 r2 r3).trans (hr2 r r0 r1 r3 r6))
        simp only [State.readReg64_setPC,
          State.readReg64_writeReg64_ne _ _ _ _ r2, State.readReg64_writeReg64_ne _ _ _ _ r0]
      · rintro s4 P4 hpc4 hrun4 ⟨hsp4, hal4, hpsp4, _, hs4_0, hs4_2, hs4_3, hs4_5, hr4, rfl⟩
        let wMax := BitVec.ofNat 32 (g.lastIdx + 1)
        let wSel := if wMax.sle cntF then wMax else cntF
        let wNew := wSel - 1#32
        let newActB : BitVec 8 := (g.activeByte &&& 0xe0#8) ||| (wNew.truncate 8 &&& 0x1f#8)
        obtain ⟨hClampLo, hClampHi⟩ := bump_clamp_props g.activeByte hLast hLt hCntLo hCntHi
        obtain ⟨hg1Mem, hActFrNe1, hwf1, hCnt1, hEff1, hDyn1, hProt1, hMap1, hBmExt1, hBmAbs1⟩ :=
          tryAvail_bump_activeIdx_absorb hwf hsc hg hScEq (hHead h1) hLt
            (newActByte := newActB) hClampLo hClampHi
        have hw4_3 : BitVec.setWidth 32 (s4.readReg64 (Reg.gpr 3#5)) = cntF := hs4_3
        have hByte0Last : (g.packedWord.extractLsb' 0 8).zeroExtend 32 &&& 0x1f#32 =
            BitVec.ofNat 32 g.lastIdx := (GroupDesc.packedWord_byte0 g hLast).2
        conv => arg 4; rw [coreSt_eq_parts hwf, hBmExt1, pointsToBytes_singleton]; simp only [sepConj_assoc]
        dsimp only [allocSlotOff_19c, allocSlotOff_activate] at hpc4 ⊢
        wp_sym_steps
        have hMaxAdd : BitVec.ofNat 32 g.lastIdx + 1#32 = BitVec.ofNat 32 (g.lastIdx + 1) := by
          simp [BitVec.ofNat_add]
        let g1 : GroupDesc := { g with activeByte := newActB }
        let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g1 else u
        let st1 : MallocngSt :=
          { st with groups := st.groups.map fG, byteVal := writeBytesToMap st.byteVal (g.mem + 8#64) [newActB] }
        have hBrkEq : s4.brk = s.brk := hpsp4.2.1
        have hwf1' : MallocngWFInflight inflight maddrs.base brkStart s4.brk liveCost peakCost st1 :=
          hBrkEq.symm ▸ hwf1
        refine SepWP.done rfl (by simp [hrun4])
          ⟨st1, g1, hg1Mem, by simp [hrun4], by simpa using hsp4,
           by simpa [State.spAligned] using hal4, hpsp4.trans psp_rfl,
           ⟨rfl, rfl, hEff1, hCnt1, rfl, hDyn1, rfl, fun _ _ _ _ => rfl,
            groupsGrpMono_map_ite hg g.metaPtr rfl (Nat.le_refl _)⟩,
           rfl, hScEq, hAv0, hActFrNe1, fun h1' => hHead h1',
           by simpa using hs4_2,
           fun r r0 r1 r2 r3 r6 => ?_, ?_⟩
        · refine Eq.trans ?_ (hr4 r r0 r1 r2 r3 r6)
          simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r0]
        · simp only [State.setPC, State.setMem, State.setPState, State.writeReg64] at hwf1' ⊢
          have hFix : MallocngCoreFixedA γ maddrs st = MallocngCoreFixedA γ maddrs st1 := rfl
          have hCtxPts : (maddrs.ctx ↦ₛ st.ctx.toBytes) = (maddrs.ctx ↦ₛ st1.ctx.toBytes) := rfl
          rw [and_imm32_0x1f_byte, hByte0Last, hMaxAdd, bfxil_w32_0_5_byte]
          rw [← pointsToBytes_singleton (g.mem + 8#64) newActB]
          rw [coreSt_eq_parts hwf1', ← hBmAbs1, hCtxPts, hProt1, hMap1, hFix]
          dsimp only [st1, g1, fG, newActB, wNew, wSel, wMax]
          simp only [sepConj_assoc]

/-! ## Fast-Pop Effective Cost Preservation -/

theorem sub1_w32_byte (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 b - 1#32) = b - 1#8 := by
  bv_robdd

theorem claimFreeAvail_effCost_eq {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hAvNe : g.availMask ≠ 0#32) :
    let idx := ctz32DeBruijn g.availMask
    let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
    let g' := mkReplaceSlotGroup g idx newAvail .claimed
    let val' := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
    let st1 := mkReplaceSlotSt st g idx newAvail .claimed val' st.liveMap
    totalLiveEffCost st1 = totalLiveEffCost st := by
  intro idx newAvail g' val' st1
  have hIdx : idx < g.slots.length := (claimFreeAvailInflight_absorb hwf hg hAvNe).1
  obtain ⟨_, hIdx32, _, hIso, _, hSet, _, _⟩ := ctz32DeBruijn_spec hAvNe
  obtain ⟨hBitTrue, _, _, _, _⟩ := bit32_sub_pow2_props idx hIdx32 g.availMask hIso hSet
  have hgw := hwf.groups_wf g hg
  have hFree : g.slots[idx]'hIdx = .freeAvail :=
    (hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx).2.1.mp hBitTrue
  have hMapEq : g'.slots.map slotEffCost = g.slots.map slotEffCost := by
    dsimp only [g', mkReplaceSlotGroup]
    rw [List.map_set]
    have hGet : (g.slots.map slotEffCost)[idx]'(by simp [hIdx]) = slotEffCost .claimed := by
      simp [hFree, slotEffCost]
    rw [← hGet, List.set_getElem_self]
  have hGroupsMap :
      (replaceGroup st.groups g.metaPtr g').map (fun x => (x.slots.map slotEffCost).sum) =
        st.groups.map (fun x => (x.slots.map slotEffCost).sum) := by
    dsimp only [replaceGroup]; rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    dsimp only [Function.comp]
    by_cases hEqM : x.metaPtr == g.metaPtr
    · have hxEq : x = g := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg (beq_iff_eq.mp hEqM)
      simp [hxEq, hMapEq]
    · simp [hEqM]
  dsimp only [totalLiveEffCost, st1, mkReplaceSlotSt]
  rw [hGroupsMap]

end VerifiedLibraries.Mallocng.Proofs
