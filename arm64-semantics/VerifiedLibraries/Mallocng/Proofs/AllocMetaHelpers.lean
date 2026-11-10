/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Internal

/-!
# Invariant and Byte-Map Helpers for `__malloc_alloc_meta`

Decomposes `CtxFields.toBytes`, establishes `SepWP` step rules for `SYS_brk`, and proves
`MallocngWFInflight`, `ByteMap`, `ProtNoneByteMap`, and `MappedSet` transitions for
`__malloc_alloc_meta`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## `SepWP` `CodeLoaded` access -/

/-- Access `prog.CodeLoaded s.mem` inside a `SepWP` proof. -/
theorem SepWP.with_codeLoaded {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : prog.CodeLoaded s.mem → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  exact SepWP.to_reaches_pc (h hL) hm hL

/-! ## `CtxFields.toBytes` decomposition and `SYS_brk` step rules -/

/-- Untouched middle `840` bytes (`+0x50 .. +0x398`) of `struct malloc_context`. -/
def ctxMiddleBytes (c : CtxFields) : List (BitVec 8) :=
  c.active.flatMap unpack64 ++
  c.usageByClass.flatMap unpack64 ++
  c.unmapSeq ++
  c.bounces ++
  [c.seq] ++
  c.seqPad

private theorem flatMap_unpack64_len (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.flatMap_cons, List.length_append, unpack64_length, ih, List.length_cons]
    omega

theorem ctxMiddleBytes_length {c : CtxFields}
    (hAct : c.active.length = 48)
    (hUse : c.usageByClass.length = 48)
    (hUnmap : c.unmapSeq.length = 32)
    (hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7) :
    (ctxMiddleBytes c).length = 840 := by
  unfold ctxMiddleBytes
  simp only [List.length_append, flatMap_unpack64_len, hAct, hUse, hUnmap, hBnc, hPad,
    List.length_singleton]

/-- Typed cell view of `ctx ↦ₛ c.toBytes` for `__malloc_alloc_meta`. -/
def CtxCells (ctx : BitVec 64) (c : CtxFields) : SepProp :=
  (ctx ↦₆₄ c.secret) ∗
  ((ctx + 8#64) ↦₃₂ c.initDone) ∗
  ((ctx + 12#64) ↦₃₂ c.mmapCounter) ∗
  ((ctx + 16#64) ↦₆₄ c.freeMetaHead) ∗
  ((ctx + 24#64) ↦₆₄ c.availMeta) ∗
  ((ctx + 32#64) ↦₆₄ c.availMetaCount) ∗
  ((ctx + 40#64) ↦₆₄ c.availMetaAreaCount) ∗
  ((ctx + 48#64) ↦₆₄ c.metaAllocShift) ∗
  ((ctx + 56#64) ↦₆₄ c.metaAreaHead) ∗
  ((ctx + 64#64) ↦₆₄ c.metaAreaTail) ∗
  ((ctx + 72#64) ↦₆₄ c.availMetaAreas) ∗
  ((ctx + 80#64) ↦ₛ ctxMiddleBytes c) ∗
  ((ctx + 920#64) ↦₆₄ c.brk)

theorem ctx_toBytes_eq_cells (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48)
    (hUse : c.usageByClass.length = 48)
    (hUnmap : c.unmapSeq.length = 32)
    (hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7) :
    (ctx ↦ₛ c.toBytes) = CtxCells ctx c := by
  have hMid : (ctxMiddleBytes c).length = 840 :=
    ctxMiddleBytes_length hAct hUse hUnmap hBnc hPad
  have hReassociate :
      c.toBytes =
        unpack64 c.secret ++
        (unpack32 c.initDone ++
        (unpack32 c.mmapCounter ++
        (unpack64 c.freeMetaHead ++
        (unpack64 c.availMeta ++
        (unpack64 c.availMetaCount ++
        (unpack64 c.availMetaAreaCount ++
        (unpack64 c.metaAllocShift ++
        (unpack64 c.metaAreaHead ++
        (unpack64 c.metaAreaTail ++
        (unpack64 c.availMetaAreas ++
        (ctxMiddleBytes c ++
        unpack64 c.brk))))))))))) := by
    simp only [CtxFields.toBytes, ctxMiddleBytes, List.append_assoc]
  rw [hReassociate]
  simp only [CtxCells, pointsToBytes_append, unpack64_length, unpack32_length, hMid,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, addr_norm]

/-- `SepWP` step rule for `SYS_brk(0)` (`svc #0` with `X8 = 214`, `X0 = 0`), returning `s.brk` in
    `X0` without modifying memory or advancing the oracle. -/
theorem SepWP.step_svc_brk_query {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx0 : s.readReg64 .x0 = 0#64)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hok : SepWP prog target_pc ((s.writeReg64 .x0 s.brk).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc, execBrk_query s hx0]
  have hst : (s.writeReg64 .x0 s.brk).advancePC = (s.writeReg64 .x0 s.brk).setPC (pc + 4#64) := by
    cases s
    simp [State.writeReg64, State.advancePC, State.setPC] at hpc ⊢
    exact hpc
  rw [hst]
  exact SepWP.to_reaches_pc hok hm

/-- `SepWP` step rule for page-aligned `SYS_brk(newBrk)` growth (`X8 = 214`, `brkStart ≤ brk < newBrk`),
    branching on VMA guard-gap capacity and `physMemAvail`. -/
theorem SepWP.step_svc_brk_grow {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc newBrk : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx0 : s.readReg64 .x0 = newBrk)
    (hne : newBrk ≠ 0#64)
    (hBrkMin : s.brkStart.toNat ≤ newBrk.toNat)
    (hLt : s.brk.toNat < newBrk.toNat)
    (hAlignOld : 4096 ∣ s.brk.toNat)
    (hAlignNew : 4096 ∣ newBrk.toNat)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hSuccess : ∀ m' : Memory,
      newBrk.toNat ≤ 2 ^ 48 →
      s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat) = true →
      m' = s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat) →
      MallocngMappedDelta 1 (newBrk.toNat - s.brk.toNat) s.mem m' →
      SepWP prog target_pc
        (((((s.setBrk newBrk).setMem m').setPhysMemAvail
          (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64))
        ((s.brk ↦ₛ List.replicate (newBrk.toNat - s.brk.toNat) 0#8) ∗ P) post oom)
    (hFail :
      SepWP prog target_pc
        ((s.writeReg64 .x0 s.brk).setPC (pc + 4#64)) P post oom)
    (hOom : s.physMemAvail < newBrk.toNat - s.brk.toNat →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R)) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc]
  have hx0_ne : s.readReg64 .x0 ≠ 0#64 := hx0 ▸ hne
  have hAlignOldEq : pageAlignUp s.brk.toNat = s.brk.toNat := pageAlignUp_of_dvd hAlignOld
  have hAlignNewEq : pageAlignUp (s.readReg64 .x0).toNat = newBrk.toNat := by
    rw [hx0]; exact pageAlignUp_of_dvd hAlignNew
  have hBaseEq : BitVec.ofNat 64 (pageAlignUp s.brk.toNat) = s.brk := by
    rw [hAlignOldEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hUle : s.brkStart.ule (s.readReg64 .x0) = true := by
    rw [hx0, BitVec.ule_iff_toNat_le]; exact hBrkMin
  have hLtPage : pageAlignUp s.brk.toNat < pageAlignUp (s.readReg64 .x0).toNat := by
    rw [hAlignOldEq, hAlignNewEq]; exact hLt
  have hstFail : (s.writeReg64 .x0 s.brk).advancePC =
      (s.writeReg64 .x0 s.brk).setPC (pc + 4#64) := by
    cases s
    simp [State.writeReg64, State.advancePC, State.setPC] at hpc ⊢
    exact hpc
  by_cases hFit : newBrk.toNat + BRK_GUARD_GAP ≤ USER_VA_LIMIT
  · cases hMap : s.mem.canMap (BitVec.ofNat 64 (pageAlignUp s.brk.toNat))
        (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat + BRK_GUARD_GAP) with
    | false =>
      rw [execBrk_fail s hx0_ne (Or.inr ⟨hLtPage, Or.inr hMap⟩), hstFail]
      exact SepWP.to_reaches_pc hFail hm
    | true =>
      by_cases hPhys : pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat ≤ s.physMemAvail
      · rw [execBrk_grow_ok s hx0_ne hUle (fun _ => by rw [hAlignNewEq]; exact hFit)
          (Nat.le_of_lt hLtPage) (fun _ => hMap) hPhys]
        rw [hBaseEq, hAlignNewEq, hAlignOldEq, hx0]
        have hFit' : newBrk.toNat ≤ 2 ^ 48 := by
          unfold BRK_GUARD_GAP PAGE_SIZE USER_VA_LIMIT at hFit; omega
        have hMap' : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat) = true := by
          rw [hBaseEq, hAlignNewEq, hAlignOldEq] at hMap
          rw [Memory.canMap, Memory.allPerm_iff] at hMap ⊢
          intro i hi
          exact hMap i (by unfold BRK_GUARD_GAP PAGE_SIZE; omega)
        have hm' := Satisfies.mapZero_bytes hm hMap' (by omega)
        have hm'' :
            (s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)) ⊨
              ((s.brk ↦ₛ List.replicate (newBrk.toNat - s.brk.toNat) 0#8) ∗ P) ∗ R := by
          simpa [sepConj_assoc] using hm'
        have hDelta : MallocngMappedDelta 1 (newBrk.toNat - s.brk.toNat) s.mem
            (s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)) := by
          refine ⟨[(s.brk, newBrk.toNat - s.brk.toNat)], by simp, by simp, fun a ha => ?_⟩
          by_cases hIn : (a - s.brk).toNat < newBrk.toNat - s.brk.toNat
          · exact Or.inr ⟨(s.brk, newBrk.toNat - s.brk.toNat), List.Mem.head _, hIn⟩
          · left
            have hPerm := Memory.perm_mapZero s.mem s.brk (newBrk.toNat - s.brk.toNat) a
            rw [hPerm] at ha
            simp only [hIn, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at ha
            exact ha
        have hst :
            ((((s.setBrk newBrk).setMem
              (s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat))).setPhysMemAvail
              (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64
              .x0 newBrk).advancePC =
            (((((s.setBrk newBrk).setMem
              (s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat))).setPhysMemAvail
              (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64
              .x0 newBrk).setPC (pc + 4#64)) := by
          cases s
          simp [State.setBrk, State.setMem, State.setPhysMemAvail, State.writeReg64,
            State.advancePC, State.setPC] at hpc ⊢
          exact hpc
        rw [hst]
        exact SepWP.to_reaches_pc (hSuccess _ hFit' hMap' rfl hDelta) hm''
      · rw [execBrk_oom s hx0_ne hUle hLtPage (by rw [hAlignNewEq]; exact hFit) hMap hPhys]
        rw [hAlignNewEq, hAlignOldEq] at hPhys
        exact reaches_pc_oom rfl (by simpa [State.setStatus] using hOom (by omega) R hm)
  · have hNotFit : ¬ (pageAlignUp (s.readReg64 .x0).toNat + BRK_GUARD_GAP ≤ USER_VA_LIMIT) := by
      rwa [hAlignNewEq]
    rw [execBrk_fail s hx0_ne (Or.inr ⟨hLtPage, Or.inl hNotFit⟩), hstFail]
    exact SepWP.to_reaches_pc hFail hm

/-! ## Region disjointness and `GroupWf` / `ActiveClassWf` preservation -/

private theorem pairwiseDisjoint_append {xs ys : List (BitVec 64 × Nat)} :
    PairwiseDisjointRegions (xs ++ ys) ↔
      PairwiseDisjointRegions xs ∧ PairwiseDisjointRegions ys ∧
      ∀ x ∈ xs, ∀ y ∈ ys, DisjointRegions x.1 x.2 y.1 y.2 := by
  induction xs with
  | nil => simp [PairwiseDisjointRegions]
  | cons a rest ih =>
    simp only [List.cons_append, PairwiseDisjointRegions, List.mem_append, List.mem_cons, ih]
    constructor
    · rintro ⟨hall, hrest, hys, hxy⟩
      refine ⟨⟨fun x hx => hall x (Or.inl hx), hrest⟩, hys, fun x hx y hy => ?_⟩
      rcases hx with rfl | hx
      · exact hall y (Or.inr hy)
      · exact hxy x hx y hy
    · rintro ⟨⟨ha, hrest⟩, hys, hxy⟩
      refine ⟨fun z hz => ?_, hrest, hys, fun x hx y hy => hxy x (Or.inr hx) y hy⟩
      rcases hz with hz | hz
      · exact ha z hz
      · exact hxy a (Or.inl rfl) z hz

theorem group_stride_ge_16 {st : MallocngSt} {g : GroupDesc} (hgwf : GroupWf st g) :
    16 ≤ g.stride := by
  obtain ⟨hsc, _, _, h63, _, _, _, _, hStrict, _⟩ := hgwf
  unfold GroupDesc.stride
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    have hlt := hStrict hc.2
    omega
  · rename_i hc
    rcases hsc with hscLt | hsc63
    · have hb := (sizeClass_bounds hscLt).1
      unfold slotStride; omega
    · obtain ⟨hl0, hml, _⟩ := h63 hsc63
      exfalso; apply hc
      simp [hl0, hml]

theorem group_slotStart_End_toNat {st : MallocngSt} {g : GroupDesc} (hgwf : GroupWf st g)
    (idx : Nat) (hIdx : idx ≤ g.lastIdx) :
    (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
    (g.slotEnd idx).toNat = g.mem.toNat + 16 + idx * g.stride + g.stride - 4 ∧
    (g.slotEnd idx).toNat ≤ g.mem.toNat + 12 + g.cnt * g.stride := by
  have hStr := group_stride_ge_16 hgwf
  obtain ⟨_, _, _, _, _, _, hTotFit, hCntFit, _⟩ := hgwf
  have hMulLe : (idx + 1) * g.stride ≤ g.cnt * g.stride :=
    Nat.mul_le_mul_right g.stride (by unfold GroupDesc.cnt; omega)
  have hExpand : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hIdxOffLt : idx * g.stride < 2 ^ 64 := by omega
  have hStorageNat : g.storage.toNat = g.mem.toNat + 16 := by
    unfold GroupDesc.storage
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hStartNat : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride := by
    unfold GroupDesc.slotStart
    rw [BitVec.toNat_add, hStorageNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hIdxOffLt,
      Nat.mod_eq_of_lt (by omega)]
  have hEndNat : (g.slotEnd idx).toNat = g.mem.toNat + 16 + idx * g.stride + g.stride - 4 := by
    unfold GroupDesc.slotEnd
    rw [BitVec.toNat_add, hStartNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨hStartNat, hEndNat, ?_⟩
  omega

/-- Every active group `g ∈ st.groups` is contained (including its `slotEnd lastIdx` canary byte)
    strictly inside some root `mmap` group `rg ∈ st.groups` (`0 < rg.maplen`). -/
theorem rootAncestor_of_group {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ g ∈ st.groups, ∃ rg ∈ st.groups,
      0 < rg.maplen ∧
      rg.mem.toNat ≤ g.mem.toNat ∧
      g.mem.toNat + g.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096 ∧
      (g.slotEnd g.lastIdx).toNat < rg.mem.toNat + rg.maplen * 4096 := by
  suffices hAux : ∀ fuel : Nat, ∀ g ∈ st.groups, 48 - g.sc ≤ fuel →
      ∃ rg ∈ st.groups, 0 < rg.maplen ∧ rg.mem.toNat ≤ g.mem.toNat ∧
        g.mem.toNat + g.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096 ∧
        (g.slotEnd g.lastIdx).toNat < rg.mem.toNat + rg.maplen * 4096 from
    fun g hg => hAux 48 g hg (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro g hg hfuel
    have hgwf := hwf.groups_wf g hg
    obtain ⟨hsc, _, _, h63, _, _, _, _, hStrict, _⟩ := hwf.groups_wf g hg
    rcases hsc with hscLt | hsc63
    · omega
    · obtain ⟨_, hml, _⟩ := h63 hsc63
      have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hml]
      have hSt := hStrict hml
      have ⟨_, _, hEndLe⟩ := group_slotStart_End_toNat hgwf g.lastIdx (Nat.le_refl _)
      exact ⟨g, hg, hml, Nat.le_refl _, by omega, by omega⟩
  | succ k ih =>
    intro g hg hfuel
    have hgwf := hwf.groups_wf g hg
    obtain ⟨_, _, _, _, _, _, _, _, hStrict, _, _, _, hNested, _⟩ := hwf.groups_wf g hg
    by_cases hml : 0 < g.maplen
    · have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hml]
      have hSt := hStrict hml
      have ⟨_, _, hEndLe⟩ := group_slotStart_End_toNat hgwf g.lastIdx (Nat.le_refl _)
      exact ⟨g, hg, hml, Nat.le_refl _, by omega, by omega⟩
    · have hml0 : g.maplen = 0 := by omega
      obtain ⟨_, pg, hpg, pIdx, hpIdx, _, hpgSc, hgLtPg, _, _, hLo, hHi, _⟩ := hNested hml0
      have hpgwf := hwf.groups_wf pg hpg
      obtain ⟨_, _, hpgLen, _, _, _, _, hpgCntFit, _⟩ := hwf.groups_wf pg hpg
      have hpIdxLe : pIdx ≤ pg.lastIdx := by unfold GroupDesc.cnt at hpgLen; omega
      have ⟨hpStart, he1, hpEndLe⟩ := group_slotStart_End_toNat hpgwf pIdx hpIdxLe
      have ⟨_, he2, _⟩ := group_slotStart_End_toNat hpgwf pg.lastIdx (Nat.le_refl _)
      have ⟨_, _, hgEndLe⟩ := group_slotStart_End_toNat hgwf g.lastIdx (Nat.le_refl _)
      have hgTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, hml0]
      have hFuelPg : 48 - pg.sc ≤ k :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (Nat.sub_lt_sub_left (Nat.lt_trans hgLtPg hpgSc) hgLtPg) hfuel)
      obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, hrgStrict⟩ := ih pg hpg hFuelPg
      have hpEndLeLast : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
        have hmul : pIdx * pg.stride ≤ pg.lastIdx * pg.stride :=
          Nat.mul_le_mul_right pg.stride hpIdxLe
        clear hgwf hpgwf hNested hStrict
        omega
      clear hgwf hpgwf hNested hStrict
      exact ⟨rg, hrg, hrgMl, by omega, by omega, by omega⟩

private theorem inRegion_iff_toNat {b a : BitVec 64} {n : Nat}
    (hFit : b.toNat + n ≤ 2 ^ 64) :
    InRegion b n a ↔ b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n := by
  unfold InRegion
  have hSub := BitVec.toNat_sub a b
  have haLt : a.toNat < 2 ^ 64 := a.isLt
  have hbLt : b.toNat < 2 ^ 64 := b.isLt
  omega

theorem disjointRegions_of_nat_bounds {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hf1 : b1.toNat + n1 ≤ 2 ^ 48) (hf2 : b2.toNat + n2 ≤ 2 ^ 48)
    (hsep : b1.toNat + n1 ≤ b2.toNat ∨ b2.toNat + n2 ≤ b1.toNat) :
    DisjointRegions b1 n1 b2 n2 := by
  unfold DisjointRegions
  have hs1 := BitVec.toNat_sub b2 b1
  have hs2 := BitVec.toNat_sub b1 b2
  omega

theorem metaArea_base_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas) :
    OwnedRwByte st ma.base ∧ ma.base ∈ st.masterDom := by
  have hinMa : InRegion ma.base 4096 ma.base := by simp [InRegion]
  have hmaBounds := hwf.metaAreas_wf.2.1 ma hma
  have hNoUser : ¬ CarvedUserByte st ma.base := by
    rintro ⟨g, hg, s, hs, hInUser⟩
    cases s with
    | freeAvail | freeInactive | claimed | liveNested _ => cases hInUser
    | liveUser userPtr reqSize effCost =>
      obtain ⟨idx, hIdx, hsEq⟩ := List.mem_iff_getElem.mp hs
      have hgwf := hwf.groups_wf g hg
      obtain ⟨_, _, hgLen, _, _, _, hgTotFit, hgCntFit, _, _, _, _, _, _, _, _, _, _, _, hSlotWf⟩ :=
        hwf.groups_wf g hg
      have hIdxLe : idx ≤ g.lastIdx := by unfold GroupDesc.cnt at hgLen; omega
      have hswf := hSlotWf idx hIdx
      rw [hsEq] at hswf
      obtain ⟨_, hStartLe, hReqLe, _⟩ := hswf.2.2.2.2
      have ⟨hStartNat, _, hEndLe⟩ := group_slotStart_End_toNat hgwf idx hIdxLe
      obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, _⟩ := rootAncestor_of_group hwf g hg
      obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg
      have hrgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgMl]
      have hUserBounds : userPtr.toNat ≤ ma.base.toNat ∧ ma.base.toNat < userPtr.toNat + reqSize :=
        (inRegion_iff_toNat (by omega)).mp hInUser
      have hinRg : InRegion rg.mem (rg.maplen * 4096) ma.base :=
        (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
      have hpd := hwf.regions_disjoint.1
      unfold dynamicRootRegions at hpd
      rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append] at hpd
      have hrgMem : (rg.mem, rg.maplen * 4096) ∈
          (st.guardPages.map (fun gp => (gp, 4096)) ++
           (st.availMetaPages.map (fun ap => (ap, 4096)) ++
            (st.groups.filter fun g => decide (0 < g.maplen)).map
              (fun g => (g.mem, g.maplen * 4096)))) :=
        List.mem_append_right _ (List.mem_append_right _
          (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgMl⟩)))
      have hDisj := hpd.2.2 (ma.base, 4096) (List.mem_map_of_mem hma) _ hrgMem
      have hNotIn : ¬ InRegion ma.base 4096 ma.base := by
        intro hInMa2
        have h1 := (inRegion_iff_toNat (by omega)).mp hInMa2
        have h2 := (inRegion_iff_toNat (by omega)).mp hinRg
        unfold DisjointRegions at hDisj
        dsimp only at hDisj
        have hs1 := BitVec.toNat_sub rg.mem ma.base
        have hs2 := BitVec.toNat_sub ma.base rg.mem
        omega
      exact hNotIn hinMa
  have hNoMeta : ¬ CarvedMetaByte st ma.base := by
    rintro ⟨m, hmRes, hInM⟩
    have hmSlot : m ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 m).mp (List.mem_append_right _ hmRes)
    unfold allMetaSlots at hmSlot
    obtain ⟨ma', hma', hmSlot'⟩ := List.mem_flatMap.mp hmSlot
    obtain ⟨k, hkRange, rfl⟩ := List.mem_map.mp hmSlot'
    have hkLt : k < 101 := List.mem_range.mp hkRange
    have hma'Bounds := hwf.metaAreas_wf.2.1 ma' hma'
    have hSlotNat : (ma'.slotAddr k).toNat = ma'.base.toNat + 24 + 40 * k := by
      unfold MetaAreaDesc.slotAddr
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hInNat := (inRegion_iff_toNat (by omega)).mp hInM
    have hPageSep : ma.base.toNat ≤ ma'.base.toNat ∨ ma'.base.toNat + 4096 ≤ ma.base.toNat := by
      omega
    omega
  have hOwn : OwnedRwByte st ma.base := ⟨Or.inl ⟨ma, hma, hinMa⟩, hNoUser, hNoMeta⟩
  exact ⟨hOwn, hwf.masterDom_wf.2.1 ma.base (Or.inl hOwn)⟩

theorem disjoint_dynamicRootRegions_of_canMap {inflight : Nat} {base brkStart brk newBase : BitVec 64}
    {liveCost peakCost len : Nat} {st : MallocngSt} {m : Memory} {R : SepProp}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hCanMap : m.canMap newBase len = true)
    (hAlign : 4096 ∣ newBase.toNat) (hLenPos : 0 < len)
    (hFit : newBase.toNat + len ≤ 2 ^ 48)
    (hm : m ⊨ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :
    ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 newBase len := by
  intro r hr
  unfold dynamicRootRegions at hr
  rcases List.mem_append.mp hr with hr123 | hrgList
  · rcases List.mem_append.mp hr123 with hr12 | hapList
    · rcases List.mem_append.mp hr12 with hmaList | hgpList
      · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hmaList
        dsimp only
        have hmaB := hwf.metaAreas_wf.2.1 ma hma
        refine disjointRegions_of_nat_bounds (by decide) hLenPos hmaB.2.2.1 hFit
          (Classical.byContradiction fun hno => ?_)
        have hinNew : InRegion newBase len ma.base := (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
        have ⟨hOwn, hDom⟩ := metaArea_base_ownedRw hwf hma
        have hEx := ByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal ma.base (n := 1) (by decide)
          (fun a ha => by have : a = ma.base := by
                            have h1 := (inRegion_iff_toNat (by omega)).mp ha
                            exact BitVec.eq_of_toNat_eq (by omega)
                          exact this ▸ hDom)
          (fun a ha => by have : a = ma.base := by
                            have h1 := (inRegion_iff_toNat (by omega)).mp ha
                            exact BitVec.eq_of_toNat_eq (by omega)
                          exact this ▸ hOwn)
        rw [hEx, sepConj_assoc] at hm
        have hPermRw := (IsBlock.pointsToBytes ma.base (readBytesFromMap st.byteVal ma.base 1)).perm_rw
          hm (a := ma.base) (by simp [InRegion, readBytesFromMap_length])
        have hUnmap := m.unmapped_of_canMap hCanMap hinNew
        rw [hPermRw] at hUnmap; cases hUnmap
      · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hgpList
        dsimp only
        have hgpB := hwf.guard_avail_wf.2.1 gp hgp
        refine disjointRegions_of_nat_bounds (by decide) hLenPos hgpB.2.2 hFit
          (Classical.byContradiction fun hno => ?_)
        have hinNew : InRegion newBase len gp := (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
        have hOwn : OwnedProtNoneByte st gp := Or.inl ⟨gp, hgp, by simp [InRegion]⟩
        have hDom : gp ∈ st.masterDom := hwf.masterDom_wf.2.1 gp (Or.inr (Or.inl hOwn))
        have hEx := ProtNoneByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal gp (n := 1) (by decide)
          (fun a ha => by have : a = gp := by
                            have h1 := (inRegion_iff_toNat (by omega)).mp ha
                            exact BitVec.eq_of_toNat_eq (by omega)
                          exact this ▸ hDom)
          (fun a ha => by have : a = gp := by
                            have h1 := (inRegion_iff_toNat (by omega)).mp ha
                            exact BitVec.eq_of_toNat_eq (by omega)
                          exact this ▸ hOwn)
        have hm' : m ⊨ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
            (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
             MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
        rw [hEx, sepConj_assoc] at hm'
        have hPermPn := (IsBlockProtNone.pointsToBytesProtNone gp
          (readBytesFromMap st.byteVal gp 1)).perm_protNone hm' (a := gp)
          (by simp [InRegion, readBytesFromMap_length])
        have hUnmap := m.unmapped_of_canMap hCanMap hinNew
        rw [hPermPn] at hUnmap; cases hUnmap
    · obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hapList
      dsimp only
      have hapB := hwf.guard_avail_wf.2.2.2 ap hap
      refine disjointRegions_of_nat_bounds (by decide) hLenPos hapB.2.2.1 hFit
        (Classical.byContradiction fun hno => ?_)
      have hinNew : InRegion newBase len ap := (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
      have hEx := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
        ap (n := 4096) (by decide)
        (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ap, hap, ha⟩))))))
        (fun a ha => Or.inr (Or.inr (Or.inl ⟨ap, hap, ha⟩)))
      have hm' : m ⊨ MappedSet st.masterDom (OwnedMappedByte st) ∗
          (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
           ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
      rw [hEx, sepConj_assoc] at hm'
      have hMapped := Satisfies.perm_mapped_of_memMapped hm' (by simp [InRegion] : InRegion ap 4096 ap)
      rw [m.unmapped_of_canMap hCanMap hinNew] at hMapped; cases hMapped
  · obtain ⟨rg, hrgFilt, rfl⟩ := List.mem_map.mp hrgList
    dsimp only
    obtain ⟨hrg, hrgMlB⟩ := List.mem_filter.mp hrgFilt
    have hrgMl : 0 < rg.maplen := of_decide_eq_true hrgMlB
    have hrgwf := hwf.groups_wf rg hrg
    obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hrgwf
    have hrgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgMl]
    have hrgFit : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := hrgTot ▸ hrgTotFit
    refine disjointRegions_of_nat_bounds (by omega) hLenPos hrgFit hFit
      (Classical.byContradiction fun hno => ?_)
    let x : BitVec 64 := BitVec.ofNat 64 (max rg.mem.toNat newBase.toNat)
    have hxNat : x.toNat = max rg.mem.toNat newBase.toNat := by
      dsimp only [x]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hxRg : InRegion rg.mem (rg.maplen * 4096) x :=
      (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
    have hxNew : InRegion newBase len x :=
      (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩
    have hEx := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
      rg.mem (n := rg.maplen * 4096) (by omega)
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hrgMl, ha⟩))))))
      (fun a ha => Or.inr (Or.inr (Or.inr ⟨rg, hrg, hrgMl, ha⟩)))
    have hm' : m ⊨ MappedSet st.masterDom (OwnedMappedByte st) ∗
        (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    rw [hEx, sepConj_assoc] at hm'
    have hMapped := Satisfies.perm_mapped_of_memMapped hm' hxRg
    rw [m.unmapped_of_canMap hCanMap hxNew] at hMapped; cases hMapped

private theorem readBytesFromMap_congr {bv1 bv2 : BitVec 64 → BitVec 8} {base : BitVec 64} {n : Nat}
    (hn : n ≤ 2 ^ 64)
    (hag : ∀ a : BitVec 64, InRegion base n a → bv1 a = bv2 a) :
    readBytesFromMap bv1 base n = readBytesFromMap bv2 base n := by
  unfold readBytesFromMap
  exact List.map_congr_left fun a ha => hag a ((mem_rangeAddrs_iff_inRegion base hn a).mp ha)

theorem carvedUserByte_congr {st st' : MallocngSt} (hgs : st'.groups = st.groups) (a : BitVec 64) :
    CarvedUserByte st' a ↔ CarvedUserByte st a := by
  simp only [CarvedUserByte, hgs]

theorem groups_active_wf_congr {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hgs : st'.groups = st.groups)
    (hActL : st'.activeLists = st.activeLists)
    (hActC : st'.ctx.active = st.ctx.active)
    (hByteAg : ∀ g ∈ st.groups, ∀ a : BitVec 64,
      (InRegion g.metaPtr 40 a ∨ (0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) →
        st'.byteVal a = st.byteVal a)
    (hOv : st'.liveMap.ov = st.liveMap.ov := by rfl) :
    (∀ g ∈ st'.groups, GroupWf st' g) ∧
    (∀ sc : Nat, (h1 : sc < st'.ctx.active.length) → (h2 : sc < st'.activeLists.length) →
      ActiveClassWf st' sc (st'.ctx.active[sc]'h1) (st'.activeLists[sc]'h2)) ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64,
      (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) →
        st'.byteVal a = st.byteVal a) ∧
    totalClaimedSlots st' = totalClaimedSlots st ∧
    totalLiveEffCost st' = totalLiveEffCost st := by
  have hFind : ∀ m, findGroupByMeta st' m = findGroupByMeta st m := fun m => by
    simp [findGroupByMeta, hgs]
  have hGwf : ∀ g ∈ st'.groups, GroupWf st' g := by
    rw [hgs]
    intro g hg
    have hgwf := hwf.groups_wf g hg
    obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, hrgStrict⟩ := rootAncestor_of_group hwf g hg
    obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg
    have hrgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgMl]
    have hRgFit : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := hrgTot ▸ hrgTotFit
    have hRgAg : ∀ a : BitVec 64, g.mem.toNat ≤ a.toNat →
        a.toNat < rg.mem.toNat + rg.maplen * 4096 → st'.byteVal a = st.byteVal a := by
      intro a haLo haHi
      exact hByteAg rg hrg a (Or.inr ⟨hrgMl, (inRegion_iff_toNat (by omega)).mpr ⟨by omega, haHi⟩⟩)
    have hRgSlice : ∀ (p : BitVec 64) (k : Nat),
        g.mem.toNat ≤ p.toNat → p.toNat + k ≤ rg.mem.toNat + rg.maplen * 4096 →
        readBytesFromMap st'.byteVal p k = readBytesFromMap st.byteVal p k := by
      intro p k hpLo hpHi
      refine readBytesFromMap_congr (by omega) (fun a ha => ?_)
      have haB := (inRegion_iff_toNat (by omega)).mp ha
      exact hRgAg a (by omega) (by omega)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ :=
      hwf.groups_wf g hg
    have hStr := group_stride_ge_16 hgwf
    have ⟨_, hLastEndNat, _⟩ := group_slotStart_End_toNat hgwf g.lastIdx (Nat.le_refl _)
    have hCntPos : 1 ≤ g.cnt := by unfold GroupDesc.cnt; omega
    have hMem9 : g.mem.toNat + 9 ≤ g.mem.toNat + g.totalBytes := by
      have : 16 ≤ g.cnt * g.stride := by
        simpa using Nat.mul_le_mul hCntPos hStr
      omega
    have hMem8Nat : (g.mem + 8#64).toNat = g.mem.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_, c11, c12, ?_, c14, c15, c16, ?_, ?_, ?_, ?_⟩
    · rw [hRgAg (g.slotEnd g.lastIdx) (by omega) hrgStrict]; exact c10
    · intro hml0; rw [hgs]; exact c13 hml0
    · rw [readBytesFromMap_congr (by decide) (fun a ha => hByteAg g hg a (Or.inl ha))]; exact c17
    · rw [hRgSlice g.mem 8 (Nat.le_refl _) (by omega)]; exact c18
    · rw [hRgAg (g.mem + 8#64) (by omega) (by omega)]; exact c19
    · intro idx hIdx
      have hIdxLe : idx ≤ g.lastIdx := by unfold GroupDesc.cnt at c3; omega
      have ⟨hStartNat, hEndNat, _⟩ := group_slotStart_End_toNat hgwf idx hIdxLe
      have hEndLeLast : (g.slotEnd idx).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
        have : idx * g.stride ≤ g.lastIdx * g.stride := Nat.mul_le_mul_right g.stride hIdxLe
        omega
      have hSubNat : ∀ (p : BitVec 64) (d : Nat), d ≤ p.toNat → d < 16 →
          (p - BitVec.ofNat 64 d).toNat = p.toNat - d := by
        intro p d hdle hdlt
        rw [BitVec.toNat_sub_of_le]
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hdle
      have hs := c20 idx hIdx
      obtain ⟨hs0, hs1, hs2, hs3, hs4⟩ := hs
      refine ⟨?_, hs1, hs2, hs3, ?_⟩
      · have hp := hSubNat (g.slotStart idx) 4 (by omega) (by decide)
        rw [hRgAg (g.slotStart idx - 4#64) (by simpa using by omega) (by simpa using by omega)]
        exact hs0
      · cases hSlot : g.slots[idx]'hIdx with
        | freeAvail | freeInactive | claimed => trivial
        | liveNested cm =>
          rw [hSlot] at hs4
          obtain ⟨hsc48, cg, hcg, hcm, hpm, hlo, hmod, hhi, hcap, htot, hb4, hb3, hb2⟩ := hs4
          refine ⟨hsc48, cg, hgs ▸ hcg, hcm, hpm, hlo, hmod, hhi, hcap, htot, ?_, ?_, ?_⟩
          · have hp := hSubNat cg.mem 4 (by omega) (by decide)
            rw [hRgAg (cg.mem - 4#64) (by omega) (by omega)]; exact hb4
          · have hp := hSubNat cg.mem 3 (by omega) (by decide)
            rw [hRgAg (cg.mem - 3#64) (by omega) (by omega)]; exact hb3
          · have hp := hSubNat cg.mem 2 (by omega) (by decide)
            rw [hRgSlice (cg.mem - 2#64) 2 (by omega) (by omega)]; exact hb2
        | liveUser userPtr reqSize effCost =>
          rw [hSlot] at hs4
          obtain ⟨huWf, huLo, huHi, heff1, heff2, hresLt, hsc2, hsc63, hub3, hIf, hres1, hres5⟩ := hs4
          refine ⟨huWf, huLo, huHi, heff1, by rw [hOv]; exact heff2, hresLt, hsc2, hsc63, ?_, ?_, ?_, ?_⟩
          · have hp := hSubNat userPtr 3 (by omega) (by decide)
            rw [hRgAg (userPtr - 3#64) (by omega) (by omega)]; exact hub3
          · by_cases hTot16 : (userPtr.toNat - g.storage.toNat) / 16 ≤ 0xffff
            · simp only [hTot16, ↓reduceIte] at hIf ⊢
              have hp4 := hSubNat userPtr 4 (by omega) (by decide)
              have hp2 := hSubNat userPtr 2 (by omega) (by decide)
              rw [hRgAg (userPtr - 4#64) (by omega) (by omega),
                  hRgSlice (userPtr - 2#64) 2 (by omega) (by omega)]
              exact hIf
            · simp only [hTot16, ↓reduceIte] at hIf ⊢
              have hp4 := hSubNat userPtr 4 (by omega) (by decide)
              have hp2 := hSubNat userPtr 2 (by omega) (by decide)
              have hp8 := hSubNat userPtr 8 (by omega) (by decide)
              rw [hRgAg (userPtr - 4#64) (by omega) (by omega),
                  hRgSlice (userPtr - 2#64) 2 (by omega) (by omega),
                  hRgSlice (userPtr - 8#64) 4 (by omega) (by omega)]
              exact hIf
          · intro hr1
            have hAddNat : (userPtr + BitVec.ofNat 64 reqSize).toNat = userPtr.toNat + reqSize := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega)]
            rw [hRgAg (userPtr + BitVec.ofNat 64 reqSize) (by omega) (by omega)]
            exact hres1 hr1
          · intro hr5
            have hp5 := hSubNat (g.slotEnd idx) 5 (by omega) (by decide)
            have hp4 := hSubNat (g.slotEnd idx) 4 (by omega) (by decide)
            rw [hRgAg (g.slotEnd idx - 5#64) (by omega) (by omega),
                hRgSlice (g.slotEnd idx - 4#64) 4 (by omega) (by omega)]
            exact hres5 hr5
  refine ⟨hGwf, ?_, ?_, by simp [totalClaimedSlots, hgs], by simp [totalLiveEffCost, hgs]⟩
  · intro sc h1 h2
    have h1' : sc < st.ctx.active.length := hActC ▸ h1
    have h2' : sc < st.activeLists.length := hActL ▸ h2
    have hAct := hwf.active_wf sc h1' h2'
    have hHd : st'.ctx.active[sc]'h1 = st.ctx.active[sc]'h1' := by simp [hActC]
    have hMs : st'.activeLists[sc]'h2 = st.activeLists[sc]'h2' := by simp [hActL]
    rw [hHd, hMs]
    unfold ActiveClassWf at hAct ⊢
    simp only [hgs, hFind]
    exact hAct
  · intro g hg a ha
    rcases ha with hMeta | hMem
    · exact hByteAg g hg a (Or.inl hMeta)
    · obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, _⟩ := rootAncestor_of_group hwf g hg
      obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg
      have hrgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgMl]
      have haB := (inRegion_iff_toNat (by omega)).mp hMem
      exact hByteAg rg hrg a (Or.inr ⟨hrgMl, (inRegion_iff_toNat (by omega)).mpr ⟨by omega, by omega⟩⟩)

theorem nodup_length_le_bound : ∀ (B : Nat) {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < B) → xs.length ≤ B
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hb => absurd (hb x List.mem_cons_self) (by omega)
  | B + 1, xs, hnd, hb => by
    have hpart : ∀ l : List Nat,
        l.length = (l.filter (· == B)).length + (l.filter (fun x => !(x == B))).length := fun l => by
      induction l with
      | nil => rfl
      | cons x tl ih => simp only [List.filter_cons]; cases x == B <;> simp [ih] <;> omega
    have h1 : (xs.filter (· == B)).length ≤ 1 := by
      have hndF := hnd.filter (· == B)
      cases hF : xs.filter (· == B) with
      | nil => exact Nat.zero_le 1
      | cons a tl =>
        cases hTl : tl with
        | nil => exact Nat.le_refl 1
        | cons b _ =>
          have hMemA : a ∈ xs.filter (· == B) := hF ▸ List.mem_cons_self
          have hMemB : b ∈ xs.filter (· == B) := hF ▸ List.mem_cons_of_mem a (hTl ▸ List.mem_cons_self)
          have ha : a = B := beq_iff_eq.mp (List.mem_filter.mp hMemA).2
          have hb' : b = B := beq_iff_eq.mp (List.mem_filter.mp hMemB).2
          rw [hF, hTl, ha, hb', List.pairwise_cons] at hndF
          exact absurd rfl (hndF.1 B List.mem_cons_self)
    have h2 : (xs.filter (fun x => !(x == B))).length ≤ B :=
      nodup_length_le_bound B (hnd.filter _) (fun x hx => by
        obtain ⟨hxMem, hxNe⟩ := List.mem_filter.mp hx
        have hxLt := hb x hxMem
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hxNe; omega)
    have hp := hpart xs; omega

theorem slowPathC_prep_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) (hNoAvail : st.availMetaPages = []) :
    let m := st.ctx.metaAllocShift.toNat
    let len := 4096 * 2 ^ (m + 1)
    m ≤ 35 ∧ 8192 ≤ len ∧ len ≤ 2 ^ 48 ∧ 4096 ∣ len ∧ len ≤ allocMetaByteBound peakCost := by
  intro m len
  have hSuccLe := metaAreas_length_succ_le hwf hInflight hNoFree hNoBump
  have hMaLenLe : st.metaAreas.length ≤ 2 ^ 36 := by
    have hDivAux : ∀ (mas : List MetaAreaDesc),
        (∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48 ∧
          readBytesFromMap st.byteVal ma.base 24 =
            unpack64 st.ctx.secret ++ unpack64 ma.next ++ unpack32 101#32 ++ unpack32 0#32) →
        (mas.map (·.base)).Nodup → (mas.map (fun ma => ma.base.toNat / 4096)).Nodup := by
      intro mas hB hNd; induction mas with
      | nil => exact List.nodup_nil
      | cons ma rest ih =>
        simp only [List.map_cons, List.nodup_cons] at hNd ⊢
        refine ⟨fun hMem => ?_, ih (fun x hx => hB x (List.mem_cons_of_mem ma hx)) hNd.2⟩
        obtain ⟨ma2, hma2, hEq⟩ := List.mem_map.mp hMem
        have hb1 := hB ma List.mem_cons_self; have hb2 := hB ma2 (List.mem_cons_of_mem ma hma2)
        have hBaseEq : ma.base = ma2.base := BitVec.eq_of_toNat_eq (by omega)
        exact hNd.1 (hBaseEq ▸ List.mem_map_of_mem hma2)
    rw [← List.length_map (f := fun ma : MetaAreaDesc => ma.base.toNat / 4096)]
    refine nodup_length_le_bound (2 ^ 36) (hDivAux st.metaAreas hwf.metaAreas_wf.2.1 hwf.metaAreas_wf.1)
      (fun q hq => ?_)
    obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hq; have hb := hwf.metaAreas_wf.2.1 ma hma; omega
  have hmLe35 : m ≤ 35 := by
    by_cases hm0 : m = 0
    · omega
    · obtain ⟨hm40, _, hSum, _, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl
      have hAv0 : st.availMetaPages.length = 0 := by simp [hNoAvail]
      exact Classical.byContradiction fun hGt => by
        have hPow : 2 ^ 37 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
        omega
  have hPowGe : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  have hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  have hPowPeak : 2 ^ (m + 1) ≤ 38 + peakCost / 655360 := by
    by_cases hm0 : m = 0
    · rw [hm0]; omega
    · obtain ⟨_, _, hSum, _, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl
      have hAv0 : st.availMetaPages.length = 0 := by simp [hNoAvail]
      omega
  unfold allocMetaByteBound
  exact ⟨hmLe35, by dsimp [len]; omega, by dsimp [len]; omega, ⟨2 ^ (m + 1), rfl⟩, by dsimp [len]; omega⟩
end VerifiedLibraries.Mallocng.Proofs
