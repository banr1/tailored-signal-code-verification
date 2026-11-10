/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Internal
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers

/-!
# Large Individual-`mmap` Path (`sc = 63`)

Verifies `__mmap` OOM behavior for `2 ^ 62 < rawLen ≤ MallocngMaxAllocSize + 20`, fresh `mmap`
disjointness from `dynamicRootRegions`, `sc = 63` `GroupDesc` construction (`createLargeMmapGroup_wf`)
under `MallocngWFInflight 1`, and the `+0x1e0 .. +0x288` large-allocation segment of
`__libc_malloc_impl`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Huge `mmap` (`2 ^ 62 < rawLen ≤ MallocngMaxAllocSize + 20`) OOM Lemma -/

theorem huge_rawLen_sanitize_none (m : Memory) (cand : BitVec 64) {rawLen : Nat}
    (hGt62 : 2 ^ 62 < rawLen) :
    sanitizeMmapAddr m cand (pageAlignUp rawLen) = none := by
  have hLe : rawLen ≤ pageAlignUp rawLen := pageAlignUp_le rawLen
  cases hSan : sanitizeMmapAddr m cand (pageAlignUp rawLen) with
  | none => rfl
  | some base =>
    exfalso
    have ⟨_, _, hFit, _⟩ := sanitizeMmapAddr_spec hSan
    unfold USER_VA_LIMIT at hFit
    omega

theorem huge_rawLen_no_gap (m : Memory) {rawLen : Nat} (hGt62 : 2 ^ 62 < rawLen) :
    ¬ MallocngHasGap m (pageAlignUp rawLen) := by
  have hLe : rawLen ≤ pageAlignUp rawLen := pageAlignUp_le rawLen
  rintro ⟨gap, _, _, hFit, _⟩
  omega

private theorem step_not_running_of_not_running {prog : Program} {s s' : State}
    (hs : s.status ≠ .Running) (hstep : Step prog s s') : False := by
  cases hstep <;> exact hs ‹_›

private theorem steps_status_eq_of_not_running {prog : Program} {s sf : State}
    (hs : s.status ≠ .Running) (hsteps : Steps prog s sf) : sf = s := by
  cases hsteps with
  | refl => rfl
  | step h1 _ => exact False.elim (step_not_running_of_not_running hs h1)

private theorem steps_lift_noSyscalls {prog : Program}
    (hExt : prog.externs = fun _ => none)
    (hOvr : prog.overrides = fun _ => none)
    {s0 sf : State}
    (hsteps : Steps (prog.withSvc mallocngFaultSvc) s0 sf)
    (hr : sf.status = .Running) :
    Steps prog s0 sf ∧ sf.mem.perm = s0.mem.perm := by
  induction hsteps with
  | refl => exact ⟨.refl _, rfl⟩
  | @step s sm sf h1 hrest ih =>
    have ⟨hrest', hperm_rest⟩ := ih hr
    have hsm_run : sm.status = .Running :=
      Classical.byContradiction fun hnr => by
        have heq := steps_status_eq_of_not_running hnr hrest
        rw [heq] at hr
        exact hnr hr
    have hExtAt : ∀ pc, (prog.withSvc mallocngFaultSvc).externAt? pc = none := by
      intro pc
      simp [Program.externAt?, Program.hookAtOff?, Program.withSvc, hExt, hOvr]
    cases h1 with
    | halt_unmapped _ _ _ =>
      simp at hsm_run
    | extern _ hext _ _ =>
      rw [hExtAt _] at hext; cases hext
    | extern_fault _ hext _ =>
      rw [hExtAt _] at hext; cases hext
    | @exec inst hrun hfetch =>
      cases hSvc0 : inst.isSvc0 with
      | true =>
        have hInstEq : inst = .system false 0#16 := by
          cases inst with
          | system halt imm =>
            simp [Instr.isSvc0] at hSvc0
            rcases hSvc0 with ⟨rfl, rfl⟩
            rfl
          | _ => simp [Instr.isSvc0] at hSvc0
        rw [hInstEq, Program.evalInst_svc0] at hsm_run
        unfold evalSvc at hsm_run
        simp [Program.withSvc, mallocngFaultSvc, State.setStatus] at hsm_run
      | false =>
        have hEval1 : (prog.withSvc mallocngFaultSvc).evalInst inst s = execInst inst s :=
          evalInst_eq_execInst_of_not_isSvc0 hSvc0 s
        have hEval2 : prog.evalInst inst s = execInst inst s :=
          evalInst_eq_execInst_of_not_isSvc0 hSvc0 s
        have hFetch2 : prog.fetchMem s.mem s.pc = some inst := by
          cases prog; exact hfetch
        have hStep2 : Step prog s ((prog.withSvc mallocngFaultSvc).evalInst inst s) := by
          rw [hEval1, ← hEval2]
          exact Step.exec hrun hFetch2
        have hPerm1 : ((prog.withSvc mallocngFaultSvc).evalInst inst s).mem.perm = s.mem.perm := by
          rw [hEval1]
          exact execInst_perm_of_not_isSvc0 hSvc0 s
        exact ⟨.step hStep2 hrest', hperm_rest.trans hPerm1⟩

/-- Lift any `SepWP` proof on `prog.withSvc mallocngFaultSvc` (with `oom = ⌜False⌝`) to `prog` with
    arbitrary `oom`, additionally witnessing `sf.mem.perm = s0.mem.perm`. -/
theorem SepWP.lift_noSyscalls {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hExt : prog.externs = fun _ => none)
    (hOvr : prog.overrides = fun _ => none)
    (h : SepWP (prog.withSvc mallocngFaultSvc) target_pc s0 P post) :
    SepWP prog target_pc s0 P (fun sf P_f => post sf P_f ∧ sf.mem.perm = s0.mem.perm) oom := by
  apply SepWP.of_reaches_pc
  intro R hm hLoad
  have hLoad' : (prog.withSvc mallocngFaultSvc).CodeLoaded s0.mem := by
    rw [Program.codeLoaded_iff] at hLoad ⊢
    simpa [Program.withSvc] using hLoad
  rcases SepWP.to_reaches_pc h hm hLoad' with ⟨sf, hsteps, ⟨hpc, hr, P_f, hmem, hpost⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨hsteps', hperm⟩ := steps_lift_noSyscalls hExt hOvr hsteps hr
    exact ⟨sf, hsteps', Or.inl ⟨hpc, hr, P_f, hmem, hpost, hperm⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- `SepWP` rule for an anonymous `SYS_MMAP` `SVC #0` with `2 ^ 62 < rawLen` under `MallocngSvcValid`,
    which transitions directly to `s.setStatus .OutOfMemory` without modifying memory permissions,
    filesystem, or trace. -/
theorem SepWP.step_svc_oom_huge_mmap {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {P : SepProp} {post : State → SepProp → Prop}
    {svc : State → State} {pc : BitVec 64} {rawLen : Nat}
    (hProgSvc : prog.svc = svc)
    (hpc : s.pc = pc)
    (hSvc : MallocngSvcValid svc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = rawLen)
    (hGt62 : 2 ^ 62 < rawLen)
    (hfs : s.fs = s0.fs)
    (htrace : s.trace = s0.trace)
    (hperm : s.mem.perm = s0.mem.perm) :
    SepWP prog target_pc s P post
      (fun sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
         MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc svc → MallocngNoGapOrPhys sf (pageAlignUp rawLen))⌝) := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hx8' : s.readReg64 Reg.x8 = SYS_MMAP := hx8
  have hLenNe : s.readReg64 .x1 ≠ 0#64 := by
    intro hZ
    rw [hZ] at hlen_eq
    simp at hlen_eq
    omega
  have hSanNone : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = none := by
    rw [hlen_eq]
    exact huge_rawLen_sanitize_none s.mem _ hGt62
  have hEval : prog.evalInst (.system false 0#16) s = s.setStatus .OutOfMemory := by
    rw [Program.evalInst_svc0, hProgSvc]
    unfold evalSvc
    dsimp only
    rw [(hSvc s).2.2.1 hx8', execMmap_oom s hprot hflags hoff hLenNe hSanNone]
    cases s
    simp [State.setStatus]
  rw [hEval]
  refine reaches_pc_oom rfl ?_
  rw [satisfies_pure_sepConj]
  refine ⟨⟨by simp [State.setStatus, hfs], by simp [State.setStatus, htrace],
    ⟨[], Nat.zero_le 0, Nat.zero_le 0, fun a ha => Or.inl ?_⟩,
    fun _ => Or.inl (huge_rawLen_no_gap _ hGt62)⟩, ?_⟩
  · simpa [State.setStatus, hperm] using ha
  · simpa [State.setStatus] using Satisfies.drop_left hm

theorem Program.hasWords_withSvc {prog : Program} {svc : State → State}
    {entry : BitVec 64} {words : List (BitVec 32)}
    (h : prog.hasWords entry words) :
    (prog.withSvc svc).hasWords entry words := by
  cases prog; exact h

theorem SepWP.lift_noSyscalls_seq {prog : Program} {mid target_pc : BitVec 64}
    {s0 : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hExt : prog.externs = fun _ => none)
    (hOvr : prog.overrides = fun _ => none)
    (h : SepWP (prog.withSvc mallocngFaultSvc) mid s0 P
      (fun s1 P1 => s1.pc = mid → s1.status = .Running → s1.mem.perm = s0.mem.perm →
        SepWP prog target_pc s1 P1 post oom)) :
    SepWP prog target_pc s0 P post oom :=
  SepWP.seq (SepWP.lift_noSyscalls hExt hOvr h)
    (fun _ _ hpc1 hrun1 ⟨hk, hperm1⟩ => hk hpc1 hrun1 hperm1)

set_option maxHeartbeats 400000 in
theorem mmapRw_huge_oom_ok_abstract
    (prog : Program) (entry : BitVec 64) (resolve : String → BitVec 64)
    (svc : State → State) (hProgSvc : prog.svc = svc)
    (hExt : prog.externs = fun _ => none)
    (hOvr : prog.overrides = fun _ => none)
    (hSvc : MallocngSvcValid svc)
    (_hrange : ∀ r ∈ mmapFnRelocs,
      Obj.CodeRelocInRange r.kind (entry + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (resolve r.sym) r.addend))
    (hwords : prog.hasWords entry (Obj.patchRelocs mmapFnRelocs mmapFnWords entry resolve))
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat)
    (hGt62 : 2 ^ 62 < rawLen)
    (hLeMax : rawLen ≤ MallocngMaxAllocSize + 20) :
    let len := pageAlignUp rawLen
    subroutine_ok prog entry {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧
         s0.readReg64 .x0 = 0#64 ∧
         (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 3#32 ∧
         s0.readReg32 .x3 = 0x22#32 ∧
         s0.readReg32 .x4 = BitVec.allOnes 32 ∧
         s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ _ _ => ⌜False⌝
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
         MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         (MallocngSanitizedSvc svc → MallocngNoGapOrPhys sf len)⌝
    } := by
  dsimp only
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]
  cells_unfold
  wp_init x s0
  have hwordsNS := Program.hasWords_withSvc (svc := mallocngFaultSvc) hwords
  refine SepWP.lift_noSyscalls_seq (mid := ?_) hExt hOvr ?_
  rotate_left
  wp_steps
  have hMaxEq := mallocngMaxAllocSize_eq
  have hUlt : (9223372036854775806#64).ult (s0.readReg64 (Reg.gpr 1#5)) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega
  simp only [hUlt, Bool.false_eq_true, ↓reduceIte]
  wp_steps
  refine SepWP.done (by simp; rfl) (by simp [hrun]) (fun hpc1 hrun1 hperm1 => ?_)
  exact SepWP.step_svc_oom_huge_mmap hProgSvc hpc1 hSvc hrun1 (by wp_fetch)
    (by simp [Reg.x8]) (by simp [Reg.x2]) (by simp [Reg.x3])
    (by simp [Reg.x5, h]) (by simp [Reg.x1, h_3]) hGt62 rfl rfl hperm1

/-! ## Fresh `mmap` Disjointness from `dynamicRootRegions` -/

theorem disjointRegions_of_nonwrap {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hb₁ : b₁.toNat + n₁ ≤ 2 ^ 64) (hb₂ : b₂.toNat + n₂ ≤ 2 ^ 64)
    (h : b₁.toNat + n₁ ≤ b₂.toNat ∨ b₂.toNat + n₂ ≤ b₁.toNat) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  unfold DisjointRegions
  rcases h with h12 | h21 <;> constructor <;> bv_omega

theorem inRegion_disjoint_false {b₁ b₂ a : BitVec 64} {n₁ n₂ : Nat}
    (hDisj : DisjointRegions b₁ n₁ b₂ n₂)
    (h₁ : InRegion b₁ n₁ a) (h₂ : InRegion b₂ n₂ a) : False := by
  unfold DisjointRegions InRegion at *
  bv_omega

theorem page_overlap_of_not_disjoint {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hb₁Al : b₁.toNat % 4096 = 0) (hn₁Al : n₁ % 4096 = 0)
    (hb₂Al : b₂.toNat % 4096 = 0) (hn₂Al : n₂ % 4096 = 0)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hb₁ : b₁.toNat + n₁ ≤ 2 ^ 64) (hb₂ : b₂.toNat + n₂ ≤ 2 ^ 64)
    (hNot : ¬ DisjointRegions b₁ n₁ b₂ n₂) :
    ∃ k < n₁ / 4096, ∀ j < 4096,
      InRegion b₁ n₁ (b₁ + BitVec.ofNat 64 (4096 * k + j)) ∧
      InRegion b₂ n₂ (b₁ + BitVec.ofNat 64 (4096 * k + j)) := by
  have hlt1 : b₁.toNat < b₂.toNat + n₂ := by
    apply Classical.byContradiction
    intro hge
    exact hNot (disjointRegions_of_nonwrap hn₁ hn₂ hb₁ hb₂ (Or.inr (by omega)))
  have hlt2 : b₂.toNat < b₁.toNat + n₁ := by
    apply Classical.byContradiction
    intro hge
    exact hNot (disjointRegions_of_nonwrap hn₁ hn₂ hb₁ hb₂ (Or.inl (by omega)))
  let x := max b₁.toNat b₂.toNat
  have hxAl : x % 4096 = 0 := by
    by_cases hle : b₁.toNat ≤ b₂.toNat
    · simpa [x, Nat.max_eq_right hle] using hb₂Al
    · simpa [x, Nat.max_eq_left (Nat.le_of_not_le hle)] using hb₁Al
  have hxGe1 : b₁.toNat ≤ x := Nat.le_max_left _ _
  have hxGe2 : b₂.toNat ≤ x := Nat.le_max_right _ _
  have hxLt1 : x + 4096 ≤ b₁.toNat + n₁ := by omega
  have hxLt2 : x + 4096 ≤ b₂.toNat + n₂ := by omega
  refine ⟨(x - b₁.toNat) / 4096, by omega, fun j hj => ?_⟩
  have hEq : b₁.toNat + (4096 * ((x - b₁.toNat) / 4096) + j) = x + j := by omega
  constructor <;> (unfold InRegion; bv_omega)

private theorem list_filterMap_congr {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [List.filterMap, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem group_bytes_in_rootGroup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ k : Nat, ∀ g ∈ st.groups, 48 - g.sc ≤ k →
      ∀ a : BitVec 64,
        (g.mem.toNat ≤ a.toNat ∧
          (a.toNat < g.mem.toNat + g.totalBytes ∨ a.toNat ≤ (g.slotEnd g.lastIdx).toNat)) →
        ∃ rg ∈ st.groups, 0 < rg.maplen ∧ InRegion rg.mem (rg.maplen * 4096) a := by
  intro k
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  induction k with
  | zero =>
    intro g hg hk a ha
    have hgw := hwf.groups_wf g hg
    by_cases hm : 0 < g.maplen
    · have htot : g.totalBytes = g.maplen * 4096 := by unfold GroupDesc.totalBytes; simp [hm]
      have hStrict : 12 + g.cnt * g.stride < g.totalBytes := hgw.2.2.2.2.2.2.2.2.1 hm
      have hLastB := group_slot_bounds hgw (idx := g.lastIdx) (by rw [hgw.2.2.1]; unfold GroupDesc.cnt; omega)
      have hCnt : g.lastIdx + 1 = g.cnt := rfl
      have hLastEnd : (g.slotEnd g.lastIdx).toNat = g.mem.toNat + 12 + g.cnt * g.stride := by
        rw [hLastB.2.2.2.2.1, hCnt]
      have hFit := hgw.2.2.2.2.2.2.1
      exact ⟨g, hg, hm, (inRegion_iff_toNat (base := g.mem) (n := g.maplen * 4096) (by omega) a).mpr
        ⟨ha.1, by omega⟩⟩
    · have hm0 : g.maplen = 0 := by omega
      obtain ⟨_, pg, _, _, _, _, _, hscLt, hpgLe, _, _, _, _⟩ := hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hm0
      omega
  | succ k ih =>
    intro g hg hk a ha
    have hgw := hwf.groups_wf g hg
    by_cases hm : 0 < g.maplen
    · have htot : g.totalBytes = g.maplen * 4096 := by unfold GroupDesc.totalBytes; simp [hm]
      have hStrict : 12 + g.cnt * g.stride < g.totalBytes := hgw.2.2.2.2.2.2.2.2.1 hm
      have hLastB := group_slot_bounds hgw (idx := g.lastIdx) (by rw [hgw.2.2.1]; unfold GroupDesc.cnt; omega)
      have hCnt : g.lastIdx + 1 = g.cnt := rfl
      have hLastEnd : (g.slotEnd g.lastIdx).toNat = g.mem.toNat + 12 + g.cnt * g.stride := by
        rw [hLastB.2.2.2.2.1, hCnt]
      have hFit := hgw.2.2.2.2.2.2.1
      exact ⟨g, hg, hm, (inRegion_iff_toNat (base := g.mem) (n := g.maplen * 4096) (by omega) a).mpr
        ⟨ha.1, by omega⟩⟩
    · have hm0 : g.maplen = 0 := by omega
      obtain ⟨_, pg, hpg, pIdx, hpIdx, _, hpgSc, hscLt, _, _, hStartLe, hEndLe, _⟩ :=
        hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hm0
      have htot0 : g.totalBytes = g.nestedCap := by unfold GroupDesc.totalBytes; simp [hm0]
      have hgwPg := hwf.groups_wf pg hpg
      have hLastB := group_slot_bounds hgw (idx := g.lastIdx) (by rw [hgw.2.2.1]; unfold GroupDesc.cnt; omega)
      have hpgB := group_slot_bounds hgwPg hpIdx
      have hpgLastB := group_slot_bounds hgwPg (idx := pg.lastIdx)
        (by rw [hgwPg.2.2.1]; unfold GroupDesc.cnt; omega)
      have hpMulLe : (pIdx + 1) * pg.stride ≤ (pg.lastIdx + 1) * pg.stride :=
        Nat.mul_le_mul_right pg.stride (by have := hpgB.1; unfold GroupDesc.cnt at this; omega)
      exact ih pg hpg (by omega) a ⟨by omega, Or.inr (by omega)⟩

private theorem metaArea_base_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas) :
    OwnedRwByte st ma.base := by
  have hmaWf := hwf.metaAreas_wf.2.1 ma hma
  have hmaBound : ma.base.toNat + 4096 ≤ 2 ^ 48 := hmaWf.2.2.1
  have hmaIn : InRegion ma.base 4096 ma.base := by unfold InRegion; bv_omega
  obtain ⟨hP123, _, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
  obtain ⟨hP12, _, _⟩ := pairwiseDisjoint_append hP123
  obtain ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP12
  refine ⟨Or.inl ⟨ma, hma, hmaIn⟩, ?_, ?_⟩
  · rintro ⟨g, hg, s, hs, hCarv⟩
    cases s with
    | freeAvail | freeInactive | claimed | liveNested _ => cases hCarv
    | liveUser userPtr reqSize effCost =>
      obtain ⟨idx, hIdx, hEqS⟩ := List.mem_iff_getElem.mp hs
      have hgw := hwf.groups_wf g hg
      have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
      rw [hEqS] at hsw
      have hSlotB := group_slot_bounds hgw hIdx
      have hUserSt : (g.slotStart idx).toNat ≤ userPtr.toNat := hsw.2.2.2.2.2.1
      have hUserEn : userPtr.toNat + reqSize ≤ (g.slotEnd idx).toNat := hsw.2.2.2.2.2.2.1
      have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
      have hCarvN := (inRegion_iff_toNat (base := userPtr) (n := reqSize) (by omega) ma.base).mp hCarv
      obtain ⟨rg, hrg, hrgPos, hInRg⟩ :=
        group_bytes_in_rootGroup hwf 48 g hg (by omega) ma.base ⟨by omega, Or.inl (by omega)⟩
      have hMaMem : (ma.base, 4096) ∈
          st.metaAreas.map (fun m => (m.base, 4096)) ++
          st.guardPages.map (fun gp => (gp, 4096)) ++
          st.availMetaPages.map (fun ap => (ap, 4096)) :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))
      have hRgMem : (rg.mem, rg.maplen * 4096) ∈
          (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgPos⟩)
      exact inRegion_disjoint_false (hCrossG _ hMaMem _ hRgMem) hmaIn hInRg
  · rintro ⟨m, hmRes, hmIn⟩
    have hmAll : m ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 m).mp (List.mem_append_right _ hmRes)
    obtain ⟨ma', hma', k, hk, _, hmNat, hmFit, hMa48⟩ := metaSlot_in_metaArea hwf hmAll
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hmInNat := (inRegion_iff_toNat (base := m) (n := 40) (by omega) ma.base).mp hmIn
    by_cases hBaseEq : ma'.base = ma.base
    · rw [hBaseEq] at hmNat; omega
    · have hDisjMa := pairwiseDisjoint_map_ne hPMa hma hma' (Ne.symm hBaseEq)
      have hInMa' : InRegion ma'.base 4096 ma.base :=
        (inRegion_iff_toNat (base := ma'.base) (n := 4096) (by omega) ma.base).mpr (by omega)
      exact inRegion_disjoint_false hDisjMa hmaIn hInMa'

/-! ## Large `mmap` Group Creation (`createLargeMmapGroup_wf`) and Spatial Absorption -/

theorem updateSeqBeforeAllocMeta_wf
    {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    (seq' : BitVec 8) (unmapSeq' : List (BitVec 8))
    (hCase : (st.ctx.seq ≠ 0xff#8 ∧ seq' = st.ctx.seq + 1#8 ∧ unmapSeq' = st.ctx.unmapSeq) ∨
             (st.ctx.seq = 0xff#8 ∧ seq' = 1#8 ∧ unmapSeq' = List.replicate 32 0#8)) :
    MallocngWF base brkStart brk liveCost peakCost
      { st with ctx := { st.ctx with seq := seq', unmapSeq := unmapSeq' } } := by
  have hUnmLen : unmapSeq'.length = 32 := by
    rcases hCase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact hwf.ctx_lens.2.2.1
    · simp
  exact {
    base_wf := hwf.base_wf, brk_bounds := hwf.brk_bounds,
    ctx_lens := ⟨hwf.ctx_lens.1, hwf.ctx_lens.2.1, hUnmLen, hwf.ctx_lens.2.2.2.1,
      hwf.ctx_lens.2.2.2.2.1, hwf.ctx_lens.2.2.2.2.2⟩,
    initDone_wf := hwf.initDone_wf,
    initZero_wf := fun h0 => by
      have hZ := hwf.initZero_wf h0
      have hCtx0 := hZ.1
      have hUnm0 : unmapSeq' = List.replicate 32 0#8 := by
        rcases hCase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
        · rw [hCtx0]; rfl
        · rfl
      refine ⟨?_, hZ.2⟩
      dsimp only
      rw [hCtx0, hUnm0]
      rfl,
    bounces_wf := hwf.bounces_wf, usage_wf := hwf.usage_wf, brk_mode_wf := hwf.brk_mode_wf,
    metaAreas_wf := hwf.metaAreas_wf, guard_avail_wf := hwf.guard_avail_wf,
    inflight_wf := hwf.inflight_wf, free_bump_metas_wf := hwf.free_bump_metas_wf,
    groups_nodup := hwf.groups_nodup, groups_wf := hwf.groups_wf,
    regions_disjoint := hwf.regions_disjoint, active_wf := hwf.active_wf,
    liveMap_wf := hwf.liveMap_wf, live_le_peak := hwf.live_le_peak,
    effCost_le_live := hwf.effCost_le_live, meta_pages_bound := hwf.meta_pages_bound,
    empty_groups_bound := hwf.empty_groups_bound, masterDom_wf := hwf.masterDom_wf }

theorem pairwiseDisjoint_append_intro {xs ys : List (BitVec 64 × Nat)}
    (hxs : PairwiseDisjointRegions xs) (hys : PairwiseDisjointRegions ys)
    (hcross : ∀ x ∈ xs, ∀ y ∈ ys, DisjointRegions x.1 x.2 y.1 y.2) :
    PairwiseDisjointRegions (xs ++ ys) := by
  induction xs with
  | nil => exact hys
  | cons a xs ih =>
    obtain ⟨hHead, hTail⟩ := hxs
    refine ⟨?_, ih hTail (fun x hx y hy => hcross x (List.mem_cons_of_mem a hx) y hy)⟩
    intro z hz
    rcases List.mem_append.mp hz with hz1 | hz2
    · exact hHead z hz1
    · exact hcross a List.mem_cons_self z hz2

/-- Newly constructed `sc = 63` root `GroupDesc` for an individual large `mmap` allocation. -/
def mkLargeGroup (m mb : BitVec 64) (len : Nat) : GroupDesc where
  metaPtr    := m
  prev       := 0#64
  next       := 0#64
  mem        := mb
  availMask  := 0#32
  freedMask  := 0#32
  lastIdx    := 0
  sc         := 63
  maplen     := len / 4096
  activeByte := 0#8
  parentMeta := none
  nestedCap  := 0
  slots      := [.claimed]
  freshZero  := true

/-- Abstract state after linking `mkLargeGroup m mb len` into `st1` and incrementing `mmapCounter`. -/
def mkLargeGroupSt (st1 : MallocngSt) (m mb : BitVec 64) (len : Nat) : MallocngSt :=
  let gNew := mkLargeGroup m mb len
  let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
  let extraMeta := (rangeAddrs m 40).filter (fun a => !decide (a ∈ st1.masterDom))
  { st1 with
    ctx           := { st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }
    reservedMetas := []
    groups        := gNew :: st1.groups
    masterDom     := (st1.masterDom ++ extraMeta) ++ rangeAddrs mb len
    byteVal       := writeBytesToMap (writeBytesToMap st1.byteVal m gNew.metaBytes) mb groupBytes }

theorem mkLargeGroup_slot_zero {st1 : MallocngSt} {m mb : BitVec 64} {len i : Nat}
    (hLenPos : 4096 ≤ len) (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (hiGe : 8 ≤ i) (hiLt : i < len) :
    (mkLargeGroupSt st1 m mb len).byteVal (mb + BitVec.ofNat 64 i) = 0#8 := by
  let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
  have hGbLen : groupBytes.length = len := by simp [groupBytes]; omega
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  change writeBytesToMap _ mb groupBytes (mb + BitVec.ofNat 64 i) = 0#8
  rw [writeBytesToMap_in _ mb groupBytes (hi := by omega) (hlen := by omega)]
  rw [List.getElem_append_right (by simp [unpack64_length]; omega)]
  simp [unpack64_length]

private theorem mkLargeGroupSt_byteVal_out {st1 : MallocngSt} {m mb a : BitVec 64} {len : Nat}
    (hNotM : ¬ InRegion m 40 a) (hNotMb : ¬ InRegion mb len a)
    (hLenPos : 4096 ≤ len) :
    (mkLargeGroupSt st1 m mb len).byteVal a = st1.byteVal a := by
  let gNew := mkLargeGroup m mb len
  let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
  have hGbLen : groupBytes.length = len := by simp [groupBytes]; omega
  change writeBytesToMap (writeBytesToMap st1.byteVal m gNew.metaBytes) mb groupBytes a = _
  rw [writeBytesToMap_out _ mb groupBytes (by rwa [hGbLen])]
  rw [writeBytesToMap_out _ m gNew.metaBytes (by simpa using hNotM)]

theorem slotWf_lift_large {st1 st2 : MallocngSt} {g : GroupDesc} {idx : Nat} {s : SlotState}
    (hSubG : ∀ cg ∈ st1.groups, cg ∈ st2.groups)
    (hEq : ∀ a : BitVec 64, g.mem.toNat ≤ a.toNat → a.toNat < (g.slotEnd idx).toNat →
      st2.byteVal a = st1.byteVal a)
    (hBounds : g.storage.toNat = g.mem.toNat + 16 ∧
      (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
      (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
      16 ≤ g.stride ∧ (g.slotEnd idx).toNat ≤ 2 ^ 48)
    (hsw : SlotWf st1 g idx s)
    (hOv : st2.liveMap.ov = st1.liveMap.ov := by rfl) :
    SlotWf st2 g idx s := by
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSuccMul : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hRead : ∀ (p : BitVec 64) (k : Nat), g.mem.toNat ≤ p.toNat →
      p.toNat + k ≤ (g.slotEnd idx).toNat →
      readBytesFromMap st2.byteVal p k = readBytesFromMap st1.byteVal p k := fun p k h1 h2 =>
    readBytesFromMap_congr_pred
      (W := fun a => ¬ (g.mem.toNat ≤ a.toNat ∧ a.toNat < (g.slotEnd idx).toNat))
      (by omega)
      (fun a ha hN => by
        have haN := (inRegion_iff_toNat (base := p) (n := k) (by omega) a).mp ha
        exact hN ⟨by omega, by omega⟩)
      (fun a hNN => let ⟨hL, hR⟩ := Classical.not_not.mp hNN; hEq a hL hR)
  have hSm4Nat : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 :=
    bv64_sub_toNat (a := g.slotStart idx) (n := 4) (by omega)
  refine ⟨(hEq _ (by omega) (by omega)).trans hsw.1, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1, ?_⟩
  have hRest := hsw.2.2.2.2
  cases s with
  | freeAvail | freeInactive | claimed => trivial
  | liveNested cm =>
    obtain ⟨hsc, cg, hcg, hcm, hpar, hstLe, hal, hendLe, hcap, hoff, hb4, hb3, hb2⟩ := hRest
    have hcgm4 : (cg.mem - 4#64).toNat = cg.mem.toNat - 4 := bv64_sub_toNat (a := cg.mem) (n := 4) (by omega)
    have hcgm3 : (cg.mem - 3#64).toNat = cg.mem.toNat - 3 := bv64_sub_toNat (a := cg.mem) (n := 3) (by omega)
    have hcgm2 : (cg.mem - 2#64).toNat = cg.mem.toNat - 2 := bv64_sub_toNat (a := cg.mem) (n := 2) (by omega)
    exact ⟨hsc, cg, hSubG cg hcg, hcm, hpar, hstLe, hal, hendLe, hcap, hoff,
      (hEq _ (by omega) (by omega)).trans hb4,
      (hEq _ (by omega) (by omega)).trans hb3,
      (hRead (cg.mem - 2#64) 2 (by omega) (by omega)).trans hb2⟩
  | liveUser userPtr reqSize effCost =>
    obtain ⟨hbwf, hstLe, hendLe, h1, h2, h3, h4, h5, hb3, hOffCase, hRes1, hRes5⟩ := hRest
    have hum3 : (userPtr - 3#64).toNat = userPtr.toNat - 3 := bv64_sub_toNat (a := userPtr) (n := 3) (by omega)
    have hum4 : (userPtr - 4#64).toNat = userPtr.toNat - 4 := bv64_sub_toNat (a := userPtr) (n := 4) (by omega)
    have hum2 : (userPtr - 2#64).toNat = userPtr.toNat - 2 := bv64_sub_toNat (a := userPtr) (n := 2) (by omega)
    refine ⟨hbwf, hstLe, hendLe, h1, by rw [hOv]; exact h2, h3, h4, h5,
      (hEq _ (by omega) (by omega)).trans hb3, ?_, ?_, ?_⟩
    · by_cases hOffLt : (userPtr.toNat - g.storage.toNat) / 16 ≤ 0xffff <;>
        simp only [hOffLt, ↓reduceIte] at hOffCase ⊢
      · exact ⟨(hEq _ (by omega) (by omega)).trans hOffCase.1,
          (hRead (userPtr - 2#64) 2 (by omega) (by omega)).trans hOffCase.2⟩
      · obtain ⟨hsc63, hidx0, hoff32, hb4, hb2, hb8⟩ := hOffCase
        have hum8 : (userPtr - 8#64).toNat = userPtr.toNat - 8 :=
          bv64_sub_toNat (a := userPtr) (n := 8) (by omega)
        exact ⟨hsc63, hidx0, hoff32,
          (hEq _ (by omega) (by omega)).trans hb4,
          (hRead (userPtr - 2#64) 2 (by omega) (by omega)).trans hb2,
          (hRead (userPtr - 8#64) 4 (by omega) (by omega)).trans hb8⟩
    · intro hr1
      have huReq : (userPtr + BitVec.ofNat 64 reqSize).toNat = userPtr.toNat + reqSize :=
        bv64_add_toNat (a := userPtr) (n := reqSize) (by omega)
      exact (hEq _ (by omega) (by omega)).trans (hRes1 hr1)
    · intro hr5
      have hse5 : (g.slotEnd idx - 5#64).toNat = (g.slotEnd idx).toNat - 5 :=
        bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
      have hse4 : (g.slotEnd idx - 4#64).toNat = (g.slotEnd idx).toNat - 4 :=
        bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
      exact ⟨(hEq _ (by omega) (by omega)).trans (hRes5 hr5).1,
        (hRead (g.slotEnd idx - 4#64) 4 (by omega) (by omega)).trans (hRes5 hr5).2⟩

theorem createLargeMmapGroup_wf {base brkStart brk m mb : BitVec 64}
    {liveCost peakCost len : Nat} {st1 : MallocngSt}
    (hwf1 : MallocngWFInflight 1 base brkStart brk liveCost peakCost st1)
    (hRes : st1.reservedMetas = [m])
    (hMbNe : mb ≠ 0#64) (hMbAl : mb.toNat % 4096 = 0)
    (hLenPos : 4096 ≤ len) (hLenAl : len % 4096 = 0)
    (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (_hDisjStatic : DisjointRegions base 0x5000 mb len)
    (hDisjDyn : ∀ r ∈ dynamicRootRegions st1, DisjointRegions r.1 r.2 mb len) :
    MallocngWFInflight 1 base brkStart brk liveCost peakCost (mkLargeGroupSt st1 m mb len) := by
  let gNew := mkLargeGroup m mb len
  let st2 := mkLargeGroupSt st1 m mb len
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMbPos : 0 < mb.toNat := Nat.pos_of_ne_zero (fun h => hMbNe (BitVec.eq_of_toNat_eq h))
  have hMbGe : 4096 ≤ mb.toNat := by omega
  let A := st1.groups.map (·.metaPtr) ++ st1.freeMetas.map (·.ptr) ++ st1.bumpMetas
  have hu1Nodup : (A ++ [m]).Nodup := by simpa [A, hRes, List.append_assoc] using hwf1.free_bump_metas_wf.2.2.2.2.1
  have hANodup : A.Nodup := (List.nodup_append.mp hu1Nodup).1
  have hmNotA : m ∉ A := fun hmA => (List.nodup_append.mp hu1Nodup).2.2 m hmA m List.mem_cons_self rfl
  have hmAll : m ∈ allMetaSlots st1 :=
    (hwf1.free_bump_metas_wf.2.2.2.2.2 m).mp (by simp [hRes])
  obtain ⟨maM, hmaM, kM, hkM, _, hmNat, hmFit, hMaM48⟩ := metaSlot_in_metaArea hwf1 hmAll
  have hmInMaM : ∀ a : BitVec 64, InRegion m 40 a → InRegion maM.base 4096 a := by
    intro a ha
    have haN := (inRegion_iff_toNat (base := m) (n := 40) (by omega) a).mp ha
    exact (inRegion_iff_toNat (base := maM.base) (n := 4096) (by omega) a).mpr ⟨by omega, by omega⟩
  have hMaMDyn : (maM.base, 4096) ∈ dynamicRootRegions st1 := by
    unfold dynamicRootRegions
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaM)))
  have hMDisjMb : ∀ a : BitVec 64, InRegion m 40 a → ¬ InRegion mb len a :=
    fun a ha hmb => inRegion_disjoint_false (hDisjDyn _ hMaMDyn) (hmInMaM a ha) hmb
  obtain ⟨hP123, hPRoot, _⟩ := pairwiseDisjoint_append hwf1.regions_disjoint.1
  obtain ⟨hP12, _, hCross12Ap⟩ := pairwiseDisjoint_append hP123
  obtain ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP12
  have hOtherMetaOut : ∀ m' ∈ A, ∀ a : BitVec 64, InRegion m' 40 a → st2.byteVal a = st1.byteVal a := by
    intro m' hm'A a ha
    have hm'Ne : m' ≠ m := fun h => hmNotA (h ▸ hm'A)
    have hm'All : m' ∈ allMetaSlots st1 :=
      (hwf1.free_bump_metas_wf.2.2.2.2.2 m').mp (by
        simpa [A, hRes, List.append_assoc] using (List.mem_append_left [m] hm'A : m' ∈ A ++ [m]))
    obtain ⟨ma', hma', _, _, _, hm'Nat, hm'Fit, hMa'48⟩ := metaSlot_in_metaArea hwf1 hm'All
    have haMa' : InRegion ma'.base 4096 a := by
      have haN := (inRegion_iff_toNat (base := m') (n := 40) (by omega) a).mp ha
      exact (inRegion_iff_toNat (base := ma'.base) (n := 4096) (by omega) a).mpr ⟨by omega, by omega⟩
    have hMa'Dyn : (ma'.base, 4096) ∈ dynamicRootRegions st1 := by
      unfold dynamicRootRegions
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma')))
    exact mkLargeGroupSt_byteVal_out
      (fun hm => metaSlots_disjoint hwf1 hm'All hmAll hm'Ne ha hm)
      (fun hmb => inRegion_disjoint_false (hDisjDyn _ hMa'Dyn) haMa' hmb) hLenPos
  have hGroupOut : ∀ g ∈ st1.groups, ∀ a : BitVec 64,
      g.mem.toNat ≤ a.toNat →
      (a.toNat < g.mem.toNat + g.totalBytes ∨ a.toNat ≤ (g.slotEnd g.lastIdx).toNat) →
      st2.byteVal a = st1.byteVal a := by
    intro g hg a ha1 ha2
    obtain ⟨rg, hrg, hrgPos, haRg⟩ :=
      group_bytes_in_rootGroup hwf1 48 g hg (by have := (hwf1.groups_wf g hg).1; omega) a ⟨ha1, ha2⟩
    have hRgDyn : (rg.mem, rg.maplen * 4096) ∈ dynamicRootRegions st1 := by
      unfold dynamicRootRegions
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgPos⟩))
    exact mkLargeGroupSt_byteVal_out
      (fun hm => inRegion_disjoint_false (metaArea_disjoint_root_group hwf1 hmaM hrg hrgPos) (hmInMaM a hm) haRg)
      (fun hmb => inRegion_disjoint_false (hDisjDyn _ hRgDyn) haRg hmb) hLenPos
  have hClaimed0 : totalClaimedSlots st1 = 0 := by
    have hInf := hwf1.inflight_wf
    rw [hRes] at hInf; simp at hInf; omega
  have hInit1 : st1.ctx.initDone = 1#32 := by
    rcases hwf1.initDone_wf with h0 | h1
    · have := (hwf1.initZero_wf h0).2.2.2.2.2.2.2.2.1
      rw [hRes] at this; cases this
    · exact h1
  refine {
    base_wf := hwf1.base_wf
    brk_bounds := hwf1.brk_bounds
    ctx_lens := hwf1.ctx_lens
    initDone_wf := Or.inr hInit1
    initZero_wf := fun h0 => by dsimp [st2, mkLargeGroupSt] at h0; rw [hInit1] at h0; cases h0
    bounces_wf := hwf1.bounces_wf
    usage_wf := ?_
    brk_mode_wf := hwf1.brk_mode_wf
    metaAreas_wf := ?_
    guard_avail_wf := ?_
    inflight_wf := ?_
    free_bump_metas_wf := ?_
    groups_nodup := ?_
    groups_wf := ?_
    regions_disjoint := ?_
    active_wf := ?_
    liveMap_wf := ?_
    live_le_peak := hwf1.live_le_peak
    effCost_le_live := ?_
    meta_pages_bound := hwf1.meta_pages_bound
    empty_groups_bound := ?_
    masterDom_wf := ?_
  }
  · intro sc hsc
    have h48 : sc < 48 := by have := hwf1.ctx_lens.2.1; dsimp [st2, mkLargeGroupSt] at hsc; omega
    have hNe : ((mkLargeGroup m mb len).sc == sc) = false := beq_false_of_ne (by dsimp [mkLargeGroup]; omega)
    dsimp only [st2, mkLargeGroupSt, List.filter]
    rw [hNe]
    exact hwf1.usage_wf sc hsc
  · refine ⟨hwf1.metaAreas_wf.1, ?_, hwf1.metaAreas_wf.2.2⟩
    intro ma hma
    have hmaW := hwf1.metaAreas_wf.2.1 ma hma
    refine ⟨hmaW.1, hmaW.2.1, hmaW.2.2.1, ?_⟩
    rw [readBytesFromMap_congr_pred (W := fun a => InRegion m 40 a ∨ InRegion mb len a) (by decide)
      (fun a ha hW => by
        have hma48 := hmaW.2.2.1
        have haN := (inRegion_iff_toNat (base := ma.base) (n := 24) (by omega) a).mp ha
        have haMa : InRegion ma.base 4096 a :=
          (inRegion_iff_toNat (base := ma.base) (n := 4096) (by omega) a).mpr ⟨by omega, by omega⟩
        rcases hW with hm | hmb
        · by_cases hEqB : ma.base = maM.base
          · have hmN := (inRegion_iff_toNat (base := m) (n := 40) (by omega) a).mp hm
            rw [hEqB] at haN; omega
          · exact inRegion_disjoint_false (pairwiseDisjoint_map_ne hPMa hma hmaM hEqB) haMa (hmInMaM a hm)
        · have hMaDyn : (ma.base, 4096) ∈ dynamicRootRegions st1 := by
            unfold dynamicRootRegions
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))
          exact inRegion_disjoint_false (hDisjDyn _ hMaDyn) haMa hmb)
      (fun a hNot => mkLargeGroupSt_byteVal_out (fun h => hNot (Or.inl h)) (fun h => hNot (Or.inr h)) hLenPos)]
    exact hmaW.2.2.2
  · refine ⟨hwf1.guard_avail_wf.1, hwf1.guard_avail_wf.2.1, hwf1.guard_avail_wf.2.2.1, ?_⟩
    intro ap hap
    have hapW := hwf1.guard_avail_wf.2.2.2 ap hap
    refine ⟨hapW.1, hapW.2.1, hapW.2.2.1, ?_⟩
    have hMa12 : (maM.base, 4096) ∈ st1.metaAreas.map (fun ma => (ma.base, 4096)) ++
        st1.guardPages.map (fun gp => (gp, 4096)) :=
      List.mem_append_left _ (List.mem_map_of_mem hmaM)
    have hApDyn : (ap, 4096) ∈ dynamicRootRegions st1 := by
      unfold dynamicRootRegions
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hap))
    rw [readBytesFromMap_congr_pred (W := fun a => InRegion m 40 a ∨ InRegion mb len a) (by decide)
      (fun a ha hW => by
        rcases hW with hm | hmb
        · exact inRegion_disjoint_false (hCross12Ap _ hMa12 _ (List.mem_map_of_mem hap)) (hmInMaM a hm) ha
        · exact inRegion_disjoint_false (hDisjDyn _ hApDyn) ha hmb)
      (fun a hNot => mkLargeGroupSt_byteVal_out (fun h => hNot (Or.inl h)) (fun h => hNot (Or.inr h)) hLenPos)]
    exact hapW.2.2.2
  · dsimp [st2, mkLargeGroupSt, gNew, mkLargeGroup, totalClaimedSlots, SlotState.isClaimed]
    change 0 + (1 + totalClaimedSlots st1) ≤ 1
    omega
  · have hfb := hwf1.free_bump_metas_wf
    refine ⟨hfb.1, ?_, hfb.2.2.1, ?_, ?_, ?_⟩
    · intro fm hfm
      have hfmA : fm.ptr ∈ A := List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))
      rw [readBytesFromMap_congr_pred (W := fun a => ¬ InRegion fm.ptr 40 a) (by decide)
        (fun _ ha hN => hN ha) (fun a hNN => hOtherMetaOut fm.ptr hfmA a (Classical.not_not.mp hNN))]
      exact hfb.2.1 fm hfm
    · intro bm hbm
      have hbmA : bm ∈ A := List.mem_append_right _ hbm
      rw [readBytesFromMap_congr_pred (W := fun a => ¬ InRegion bm 40 a) (by decide)
        (fun _ ha hN => hN ha) (fun a hNN => hOtherMetaOut bm hbmA a (Classical.not_not.mp hNN))]
      exact hfb.2.2.2.1 bm hbm
    · simpa [st2, mkLargeGroupSt, gNew, mkLargeGroup, A, List.append_assoc] using
        List.nodup_cons.mpr ⟨hmNotA, hANodup⟩
    · intro x
      have hxEq : x ∈ (m :: st1.groups.map (·.metaPtr)) ++ st1.freeMetas.map (·.ptr) ++ st1.bumpMetas ++ [] ↔
          x ∈ A ++ [m] := by simp [A, or_comm, or_assoc]
      have h1 : x ∈ A ++ [m] ↔ x ∈ allMetaSlots st1 := by
        simpa [A, hRes, List.append_assoc] using hfb.2.2.2.2.2 x
      dsimp only [st2, mkLargeGroupSt, gNew, mkLargeGroup, List.map_cons]
      exact hxEq.trans h1
  · refine ⟨List.nodup_cons.mpr ⟨fun hmG => hmNotA (List.mem_append_left _ (List.mem_append_left _ hmG)),
      hwf1.groups_nodup.1⟩, List.nodup_cons.mpr ⟨?_, hwf1.groups_nodup.2⟩⟩
    intro hmbG
    obtain ⟨g, hg, hgMemEq⟩ := List.mem_map.mp hmbG
    have hgMemEq' : g.mem = mb := hgMemEq
    have hgw := hwf1.groups_wf g hg
    have hgTotPos : 0 < g.totalBytes := by have := hgw.2.2.2.2.2.2.2.1; omega
    obtain ⟨rg, hrg, hrgPos, hmbRg⟩ :=
      group_bytes_in_rootGroup hwf1 48 g hg (by have := hgw.1; omega) mb
        ⟨by rw [hgMemEq']; exact Nat.le_refl _, Or.inl (by rw [hgMemEq']; omega)⟩
    have hRgDyn : (rg.mem, rg.maplen * 4096) ∈ dynamicRootRegions st1 := by
      unfold dynamicRootRegions
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgPos⟩))
    exact inRegion_disjoint_false (hDisjDyn _ hRgDyn) hmbRg (by unfold InRegion; bv_omega)
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg1
    · have hMapMul : (len / 4096) * 4096 = len := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hLenAl)
      have hMapPos : 0 < len / 4096 := by omega
      have hTotEq : gNew.totalBytes = len := by
        unfold GroupDesc.totalBytes; dsimp [gNew, mkLargeGroup]; simp [hMapPos, hMapMul]
      have hStrEq : gNew.stride = len - 16 := by
        unfold GroupDesc.stride; dsimp [gNew, mkLargeGroup]; simp [hMapPos, hMapMul]
      have hEndEq : gNew.slotEnd 0 = mb + BitVec.ofNat 64 (len - 4) := by
        unfold GroupDesc.slotEnd GroupDesc.slotStart GroupDesc.storage
        rw [hStrEq]; dsimp [gNew, mkLargeGroup]; bv_omega
      let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
      have hGbLen : groupBytes.length = len := by simp [groupBytes]; omega
      refine ⟨Or.inr rfl, (by decide : (0 : Nat) ≤ 31), rfl, fun _ => ⟨rfl, hMapPos, rfl, rfl⟩,
        hMbGe, by dsimp [gNew, mkLargeGroup]; omega, by rw [hTotEq]; dsimp [gNew, mkLargeGroup]; exact hMbBound,
        by rw [hTotEq, hStrEq]; dsimp [gNew, mkLargeGroup, GroupDesc.cnt]; omega,
        fun _ => by rw [hTotEq, hStrEq]; dsimp [gNew, mkLargeGroup, GroupDesc.cnt]; omega,
        by change st2.byteVal (gNew.slotEnd 0) = 0#8; rw [hEndEq]; exact mkLargeGroup_slot_zero hLenPos hMbBound (by omega) (by omega),
        ⟨fun _ => rfl, fun _ => hMapPos⟩,
        fun _ => ⟨hMbAl, rfl, fun h => by dsimp [gNew, mkLargeGroup] at h; omega,
          fun h => by dsimp [gNew, mkLargeGroup] at h; omega⟩,
        fun h => by dsimp [gNew, mkLargeGroup] at h; omega,
        (by decide : (0#32 &&& 0#32) = 0#32), (by decide : (0#32 ||| 0#32).toNat < 2 ^ 1),
        (by decide : (0#8 &&& 0x1f#8).toNat ≤ 0), ?_, ?_, ?_, ?_⟩
      · change readBytesFromMap st2.byteVal m 40 = gNew.metaBytes
        rw [readBytesFromMap_congr_pred (W := fun a => InRegion mb len a) (by decide)
          (fun a ha => hMDisjMb a ha)
          (fun a hNotMb => by
            change writeBytesToMap (writeBytesToMap st1.byteVal m gNew.metaBytes) mb groupBytes a =
              writeBytesToMap st1.byteVal m gNew.metaBytes a
            exact writeBytesToMap_out _ mb groupBytes (by rwa [hGbLen]))]
        exact readBytesFromMap_writeBytesToMap st1.byteVal m gNew.metaBytes (by simp)
      · apply List.ext_getElem (by simp)
        intro i hi1 hi2
        rw [readBytesFromMap_getElem _ _ _ _ hi1]
        change writeBytesToMap _ mb groupBytes (mb + BitVec.ofNat 64 i) = (unpack64 m)[i]
        rw [writeBytesToMap_in _ mb groupBytes (hi := by simp at hi1; omega) (hlen := by omega)]
        exact List.getElem_append_left _
      · exact mkLargeGroup_slot_zero hLenPos hMbBound (i := 8) (by decide) (by omega)
      · intro idx hIdx
        have h0 : idx = 0 := by dsimp [gNew, mkLargeGroup] at hIdx; omega
        subst h0
        have hSm4 : gNew.slotStart 0 - 4#64 = mb + BitVec.ofNat 64 12 := by
          unfold GroupDesc.slotStart GroupDesc.storage; dsimp [gNew, mkLargeGroup]; bv_omega
        refine ⟨by rw [hSm4]; exact mkLargeGroup_slot_zero hLenPos hMbBound (by decide) (by omega),
          ⟨fun (h : (0#32).getLsbD 0 = true) => absurd h (by decide), fun h => by cases h⟩,
          ⟨fun (h : (0#32).getLsbD 0 = true) => absurd h (by decide), fun h => by cases h⟩,
          fun (h : (0#8 &&& 0x1f#8).toNat < 0) => absurd h (by decide), trivial⟩
    · have hgw := hwf1.groups_wf g hg1
      have hgMetaA : g.metaPtr ∈ A := List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg1))
      refine ⟨hgw.1, hgw.2.1, hgw.2.2.1, hgw.2.2.2.1, hgw.2.2.2.2.1, hgw.2.2.2.2.2.1,
        hgw.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.1, ?_,
        hgw.2.2.2.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.2.2.2.1, ?_,
        hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
      · have hB := group_slot_bounds hgw (idx := g.lastIdx) (by rw [hgw.2.2.1]; unfold GroupDesc.cnt; omega)
        exact (hGroupOut g hg1 _ (by omega) (Or.inr (Nat.le_refl _))).trans hgw.2.2.2.2.2.2.2.2.2.1
      · intro hm0
        obtain ⟨hl1, pg, hpg, pIdx, hpIdx, hrest⟩ := hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hm0
        exact ⟨hl1, pg, List.mem_cons_of_mem gNew hpg, pIdx, hpIdx, hrest⟩
      · rw [readBytesFromMap_congr_pred (W := fun a => ¬ InRegion g.metaPtr 40 a) (by decide)
          (fun _ ha hN => hN ha) (fun a hNN => hOtherMetaOut g.metaPtr hgMetaA a (Classical.not_not.mp hNN))]
        exact hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · have hTotGe : 12 + g.cnt * g.stride ≤ g.totalBytes := hgw.2.2.2.2.2.2.2.1
        have hFit := hgw.2.2.2.2.2.2.1
        rw [readBytesFromMap_congr_pred (W := fun a => ¬ InRegion g.mem 8 a) (by decide)
          (fun _ ha hN => hN ha)
          (fun a hNN => by
            have haN := (inRegion_iff_toNat (base := g.mem) (n := 8) (by omega) a).mp (Classical.not_not.mp hNN)
            exact hGroupOut g hg1 a haN.1 (Or.inl (by omega)))]
        exact hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · have hTotGe : 12 + g.cnt * g.stride ≤ g.totalBytes := hgw.2.2.2.2.2.2.2.1
        have hFit := hgw.2.2.2.2.2.2.1
        have h8 : (g.mem + 8#64).toNat = g.mem.toNat + 8 := bv64_add_toNat (a := g.mem) (n := 8) (by omega)
        exact (hGroupOut g hg1 _ (by omega) (Or.inl (by omega))).trans
          hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · intro idx hIdx
        have hB := group_slot_bounds hgw hIdx
        have hLastB := group_slot_bounds hgw (idx := g.lastIdx) (by rw [hgw.2.2.1]; unfold GroupDesc.cnt; omega)
        have hStr := (group_stride_pos_and_align hgw).1
        have hMulLe : (idx + 1) * g.stride ≤ (g.lastIdx + 1) * g.stride :=
          Nat.mul_le_mul_right g.stride (by have := hB.1; unfold GroupDesc.cnt at this; omega)
        exact slotWf_lift_large (fun cg hcg => List.mem_cons_of_mem gNew hcg)
          (fun a ha1 ha2 => hGroupOut g hg1 a ha1 (Or.inr (by omega)))
          ⟨hB.2.1, hB.2.2.1, hB.2.2.2.2.1, hStr, by omega⟩
          (hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx)
  · have hMapMul : (len / 4096) * 4096 = len := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hLenAl)
    have hMapPos : 0 < len / 4096 := by omega
    have hDynEq : dynamicRootRegions st2 =
        (st1.metaAreas.map (fun ma => (ma.base, 4096)) ++
         st1.guardPages.map (fun gp => (gp, 4096)) ++
         st1.availMetaPages.map (fun ap => (ap, 4096))) ++
        ((mb, len) :: (st1.groups.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))) := by
      unfold dynamicRootRegions; dsimp [st2, mkLargeGroupSt, gNew, mkLargeGroup]
      simp [hMapPos, hMapMul]
    rw [hDynEq]
    obtain ⟨_, _, hCrossG⟩ := pairwiseDisjoint_append hwf1.regions_disjoint.1
    refine ⟨pairwiseDisjoint_append_intro hP123 ⟨?_, hPRoot⟩ ?_, trivial⟩
    · intro x hx
      exact (hDisjDyn x (List.mem_append_right _ hx)).symm
    · intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hyRest
      · exact hDisjDyn x (List.mem_append_left _ hx)
      · exact hCrossG x hx y hyRest
  · intro sc h1 h2
    have h48 : sc < 48 := by have := hwf1.ctx_lens.1; dsimp [st2, mkLargeGroupSt] at h1; omega
    have haw := hwf1.active_wf sc h1 h2
    have hFind : ∀ x ∈ st1.activeLists[sc]'h2, findGroupByMeta st2 x = findGroupByMeta st1 x := by
      intro x hx
      obtain ⟨gx, hgx, hgxEq, _⟩ := haw.1 x hx
      have hxA : x ∈ A := hgxEq ▸ List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hgx))
      have hNe : (m == x) = false := beq_false_of_ne (fun h => hmNotA (h ▸ hxA))
      unfold findGroupByMeta; dsimp [st2, mkLargeGroupSt, gNew, mkLargeGroup]; simp [hNe]
    have hMapEq : (st1.activeLists[sc]'h2).filterMap (fun x => (findGroupByMeta st2 x).map fun g => (g.metaPtr, g.prev, g.next)) =
        (st1.activeLists[sc]'h2).filterMap (fun x => (findGroupByMeta st1 x).map fun g => (g.metaPtr, g.prev, g.next)) :=
      list_filterMap_congr (fun x hx => by rw [hFind x hx])
    refine ⟨fun x hx => let ⟨gx, hgx, heq, hsc⟩ := haw.1 x hx; ⟨gx, List.mem_cons_of_mem gNew hgx, heq, hsc⟩,
      by change CircularDllWf (st1.ctx.active[sc]'h1) ((st1.activeLists[sc]'h2).filterMap _); rw [hMapEq]; exact haw.2.1,
      by change ((st1.activeLists[sc]'h2).filterMap _).length = _; rw [hMapEq]; exact haw.2.2.1, ?_, ?_, ?_, ?_⟩
    · intro g hg hsc; rcases List.mem_cons.mp hg with rfl | hg1
      · dsimp [gNew, mkLargeGroup] at hsc; omega
      · exact haw.2.2.2.1 g hg1 hsc
    · intro i hi hpos g hg hmeta; rcases List.mem_cons.mp hg with rfl | hg1
      · obtain ⟨gx, hgx, hgxEq, _⟩ := haw.1 (st1.activeLists[sc]'h2)[i] (List.getElem_mem _)
        have hmx : m = gx.metaPtr := (hmeta : m = _).trans hgxEq.symm
        exact False.elim (hmNotA (hmx ▸ List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hgx))))
      · exact haw.2.2.2.2.1 i hi hpos g hg1 hmeta
    · intro g1 hg1 g2 hg2 hsc1 hsc2 ha1 ha2; rcases List.mem_cons.mp hg1 with rfl | hg1'
      · dsimp [gNew, mkLargeGroup] at hsc1; omega
      · rcases List.mem_cons.mp hg2 with rfl | hg2'
        · dsimp [gNew, mkLargeGroup] at hsc2; omega
        · exact haw.2.2.2.2.2.1 g1 hg1' g2 hg2' hsc1 hsc2 ha1 ha2
    · intro g hg hsc ha; rcases List.mem_cons.mp hg with rfl | hg1
      · dsimp [gNew, mkLargeGroup] at hsc; omega
      · exact haw.2.2.2.2.2.2 g hg1 hsc ha
  · intro p n; change st1.liveMap p = some n ↔ _; rw [hwf1.liveMap_wf p n]
    exact ⟨fun ⟨g, hg, idx, hIdx, eff, hs⟩ => ⟨g, List.mem_cons_of_mem gNew hg, idx, hIdx, eff, hs⟩,
      fun ⟨g, hg, idx, hIdx, eff, hs⟩ => by
        rcases List.mem_cons.mp hg with rfl | hg1
        · have h0 : idx = 0 := by dsimp [gNew, mkLargeGroup] at hIdx; omega
          subst h0; dsimp [gNew, mkLargeGroup] at hs; cases hs
        · exact ⟨g, hg1, idx, hIdx, eff, hs⟩⟩
  · simpa [st2, mkLargeGroupSt, gNew, mkLargeGroup, totalLiveEffCost, slotEffCost] using hwf1.effCost_le_live
  · intro g hg hEmp; rcases List.mem_cons.mp hg with rfl | hg1
    · dsimp [GroupDesc.isEmpty, gNew, mkLargeGroup, SlotState.isFree] at hEmp; cases hEmp
    · have ⟨hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩ := hwf1.empty_groups_bound g hg1 hEmp
      refine ⟨hm1, hm2, hm3, hm4, hm5, fun g' hg' hEmp' hSc' => ?_, hm7⟩
      rcases List.mem_cons.mp hg' with rfl | hg1'
      · dsimp [GroupDesc.isEmpty, gNew, mkLargeGroup, SlotState.isFree] at hEmp'; cases hEmp'
      · exact hm6 g' hg1' hEmp' hSc'
  · let extraMeta := (rangeAddrs m 40).filter (fun a => !decide (a ∈ st1.masterDom))
    have hMapMul : (len / 4096) * 4096 = len := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hLenAl)
    have hMapPos : 0 < len / 4096 := by omega
    have hExNodup : extraMeta.Nodup := (nodup_rangeAddrs m (by decide)).filter _
    have hDom1ExNodup : (st1.masterDom ++ extraMeta).Nodup :=
      List.nodup_append.mpr ⟨hwf1.masterDom_wf.1, hExNodup, fun x hx1 y hyEx hxy => by
        subst hxy; simp [extraMeta] at hyEx; exact hyEx.2 hx1⟩
    have hInDyn1 : ∀ x ∈ st1.masterDom ++ extraMeta, ∃ r ∈ dynamicRootRegions st1, InRegion r.1 r.2 x := by
      intro x hx
      rcases List.mem_append.mp hx with hx1 | hxEx
      · exact hwf1.masterDom_wf.2.2 x hx1
      · simp [extraMeta] at hxEx
        exact ⟨(maM.base, 4096), hMaMDyn, hmInMaM x ((mem_rangeAddrs_iff_inRegion m (by decide) x).mp hxEx.1)⟩
    refine ⟨List.nodup_append.mpr ⟨hDom1ExNodup, nodup_rangeAddrs mb (by omega), fun x hx1 y hyMb hxy => by
      subst hxy
      obtain ⟨r, hr, hxr⟩ := hInDyn1 x hx1
      exact inRegion_disjoint_false (hDisjDyn r hr) hxr ((mem_rangeAddrs_iff_inRegion mb (by omega) x).mp hyMb)⟩, ?_, ?_⟩
    · intro a hOwn
      have hSubM : InRegion m 40 a → a ∈ st2.masterDom := fun hm => by
        dsimp [st2, mkLargeGroupSt]
        by_cases h1 : a ∈ st1.masterDom
        · exact List.mem_append_left _ (List.mem_append_left _ h1)
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.mpr
            ⟨(mem_rangeAddrs_iff_inRegion m (by decide) a).mpr hm, by simp [h1]⟩))
      have hSubMb : InRegion mb len a → a ∈ st2.masterDom := fun hmb =>
        List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (by omega) a).mpr hmb)
      rcases hOwn with hRw | hPn | hMp
      · by_cases hm : InRegion m 40 a
        · exact hSubM hm
        · by_cases hmb : InRegion mb len a
          · exact hSubMb hmb
          · have hRw1 : OwnedRwByte st1 a := by
              refine ⟨?_, ?_, fun ⟨mx, hmx, hmxIn⟩ => hm (by rw [hRes] at hmx; simp at hmx; rwa [← hmx])⟩
              · rcases hRw.1 with hMa | ⟨g, hg, hpos, hIn⟩
                · exact Or.inl hMa
                · rcases List.mem_cons.mp hg with rfl | hg1
                  · dsimp [gNew, mkLargeGroup] at hIn; rw [hMapMul] at hIn; exact False.elim (hmb hIn)
                  · exact Or.inr ⟨g, hg1, hpos, hIn⟩
              · rintro ⟨g, hg, s, hs, hC⟩
                exact hRw.2.1 ⟨g, List.mem_cons_of_mem gNew hg, s, hs, hC⟩
            exact List.mem_append_left _ (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inl hRw1)))
      · exact List.mem_append_left _ (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inl hPn))))
      · rcases hMp with h1 | h2 | h3 | ⟨g, hg, hpos, hIn⟩
        · exact List.mem_append_left _ (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inl h1)))))
        · exact List.mem_append_left _ (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
        · exact List.mem_append_left _ (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))))
        · rcases List.mem_cons.mp hg with rfl | hg1
          · dsimp [gNew, mkLargeGroup] at hIn; rw [hMapMul] at hIn; exact hSubMb hIn
          · exact List.mem_append_left _ (List.mem_append_left _
              (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg1, hpos, hIn⟩)))))))
    · intro a ha
      rcases List.mem_append.mp ha with ha1 | haMb
      · obtain ⟨r, hr, har⟩ := hInDyn1 a ha1
        refine ⟨r, ?_, har⟩
        unfold dynamicRootRegions at hr ⊢
        rcases List.mem_append.mp hr with hr123 | hrG
        · exact List.mem_append_left _ hr123
        · obtain ⟨g, hgF, rfl⟩ := List.mem_map.mp hrG
          obtain ⟨hg1, hpos⟩ := List.mem_filter.mp hgF
          exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_cons_of_mem gNew hg1, hpos⟩))
      · refine ⟨(mb, len), ?_, (mem_rangeAddrs_iff_inRegion mb (by omega) a).mp haMb⟩
        unfold dynamicRootRegions; dsimp [st2, mkLargeGroupSt, gNew, mkLargeGroup]
        exact List.mem_append_right _ (by simp [hMapPos, hMapMul])

end VerifiedLibraries.Mallocng.Proofs
