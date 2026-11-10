/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers
public import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof
public import ProofLib.SepLogic.WP.StepsProcess
public import VerifiedLibraries.Mallocng.Proofs.MemcpySym

/-!
# Shared Realloc Helpers

Pure arithmetic, budget accounting, `memcpy` pure-code lifting, and spatial entailment helpers
shared across placed `realloc` (`PlacedReallocInPlace`, `PlacedReallocProof`) and the placed
`__rustc::__rdl_realloc` shim bridge.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType Arm64.Process ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem maxAllocSize_lt_pow64 : MallocngMaxAllocSize < 2 ^ 64 := by
  decide

theorem cond_hi_subs64_iff_lt (a b : BitVec 64) :
    ConditionHolds .HI (subsPState64 a b) = true ↔ b < a := by
  unfold subsPState64
  bv_robdd

theorem cond_cc_subs64_iff_lt (a b : BitVec 64) :
    ConditionHolds .CC (subsPState64 a b) = true ↔ a < b := by
  unfold subsPState64
  bv_robdd

theorem isPow2Align_alignedAllocOk {a : BitVec 64} (h : IsPow2Align a) :
    alignedAllocAlignOk a = true := by
  have hand : (a &&& (a - 1#64)) = 0#64 := h.2
  unfold alignedAllocAlignOk
  rw [beq_iff_eq]
  clear h
  revert hand
  bv_robdd

theorem isPow2Align_dvd_16 {a : BitVec 64} (h : IsPow2Align a) (hle : a.toNat ≤ 16) :
    a.toNat ∣ 16 := by
  obtain ⟨hne, hand⟩ := h
  have hpos : 0 < a.toNat := by
    cases Nat.eq_zero_or_pos a.toNat with
    | inl hz => exact False.elim (hne (BitVec.eq_of_toNat_eq hz))
    | inr hp => exact hp
  have ha_eq : a = BitVec.ofNat 64 a.toNat := (BitVec.ofNat_toNat 64 a).symm
  rw [ha_eq] at hand
  rcases (by omega : a.toNat = 1 ∨ a.toNat = 2 ∨ a.toNat = 3 ∨ a.toNat = 4 ∨
      a.toNat = 5 ∨ a.toNat = 6 ∨ a.toNat = 7 ∨ a.toNat = 8 ∨
      a.toNat = 9 ∨ a.toNat = 10 ∨ a.toNat = 11 ∨ a.toNat = 12 ∨
      a.toNat = 13 ∨ a.toNat = 14 ∨ a.toNat = 15 ∨ a.toNat = 16) with
    hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
    (rw [hk] at hand ⊢; first | decide | exact absurd hand (by decide))

theorem isPow2Align_dvd_max16 {a : BitVec 64} (h : IsPow2Align a) :
    a.toNat ∣ max a.toNat 16 := by
  by_cases hle : a.toNat ≤ 16
  · rw [Nat.max_eq_right hle]; exact isPow2Align_dvd_16 h hle
  · rw [Nat.max_eq_left (by omega)]; exact Nat.dvd_refl _

theorem spAligned_sub64 {s : State} (h : s.spAligned = true) :
    decide ((s.sp - 64#64) &&& 15#64 = 0#64) = true := by
  unfold State.spAligned at h
  have h0 : s.sp &&& 15#64 = 0#64 := of_decide_eq_true h
  apply decide_eq_true
  revert h0
  generalize s.sp = sp
  intro h0
  bv_robdd

theorem stackSlot56_wf {sp : BitVec 64} (h : (sp &&& 15#64) = 0#64) :
    sp - 56#64 ≠ 0#64 ∧ (sp - 56#64).toNat % 8 = 0 ∧ (sp - 56#64).toNat + 8 ≤ 2 ^ 64 := by
  have hne : sp - 56#64 ≠ 0#64 := by bv_robdd
  have hand8 : (sp - 56#64) &&& 7#64 = 0#64 := by bv_robdd
  have hmod8 : (sp - 56#64).toNat % 8 = 0 := by
    have ht : ((sp - 56#64) &&& 7#64).toNat = 0 := by rw [hand8]; rfl
    rw [BitVec.toNat_and] at ht
    have hm : (sp - 56#64).toNat &&& 7 = (sp - 56#64).toNat % 8 :=
      Nat.and_two_pow_sub_one_eq_mod (sp - 56#64).toNat 3
    exact hm.symm.trans ht
  have hlt : (sp - 56#64).toNat < 2 ^ 64 := (sp - 56#64).isLt
  exact ⟨hne, hmod8, by omega⟩

theorem mallocngMappedDelta_of_perm_eq {k b : Nat} {m0 mf : Memory}
    (h : mf.perm = m0.perm) : MallocngMappedDelta k b m0 mf := by
  refine ⟨[], Nat.zero_le k, Nat.zero_le b, fun a ha => Or.inl ?_⟩
  change (m0.perm a).mapped = true
  rwa [← h]

theorem mallocngEnv_focus_errno (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (s : State) :
    MallocngEnv mallocngIface γ A tp brkStart b ivs s ⊢
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (mallocngIface.MallocngCore γ A brkStart s.brk b ivs ∗
         ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) := by
  unfold MallocngEnv
  rw [mallocngHeap_split_runtime]
  unfold MallocngRuntime
  refine sepConj_mono_right ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun _ => Entails.of_eq (by ac_rfl)

theorem mallocngEnv_unfocus_errno (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    {s0 sf : State} (errnoVal' : BitVec 32)
    (hPerm : sf.mem.perm = s0.mem.perm) (hBrk : sf.brk = s0.brk)
    (hTp : sf.tpidrEl0 = tp) (hBrkS : sf.brkStart = brkStart) :
    ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
    (mallocngIface.MallocngCore γ A brkStart s0.brk b ivs ∗
     ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ⊢
      MallocngPostEnv mallocngIface γ A tp brkStart b ivs s0 sf := by
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun ivsf =>
        ⌜MallocngNoOrphanMappings ivs ivsf s0.mem sf.mem⌝ ∗
        MallocngEnv mallocngIface γ A tp brkStart b ivsf sf) ivs)
  have hNoOrph : MallocngNoOrphanMappings ivs ivs s0.mem sf.mem := by
    intro a hm hor
    rcases hor with hnot | hin
    · rw [hPerm, hnot] at hm; cases hm
    · exact hin
  refine Entails.pure_right hNoOrph ?_
  unfold MallocngEnv
  refine Entails.pure_right ⟨hTp, hBrkS⟩ ?_
  rw [hBrk, mallocngHeap_split_runtime]
  unfold MallocngRuntime
  refine Entails.trans (sepConj_mono_left
    (Entails.sepExists_intro (P := fun ev => (tp - 0xa4#64) ↦₃₂ ev) errnoVal')) ?_
  exact Entails.of_eq (by ac_rfl)

theorem le_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.mem_cons, List.sum_cons] at h ⊢
    rcases h with rfl | hmem
    · omega
    · have := ih hmem; omega

theorem liveCost_ge_of_env_block (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (s : State) (p : BitVec 64) (oldSz : Nat) (R : SepProp)
    (hsat : s.mem ⊨ MallocngEnv mallocngIface γ A tp brkStart b ivs s ∗
      mallocngIface.Block γ p oldSz ∗ R) :
    max oldSz MallocngMinBlockCost ≤ b.liveCost := by
  rw [← sepConj_assoc] at hsat
  have h1 : s.mem ⊨
      (mallocngIface.MallocngHeap γ A tp brkStart s.brk b ivs ∗ MallocngBlockToken γ p oldSz) ∗ R := by
    apply (fun e => Satisfies.mono e hsat)
    refine sepConj_mono_left ?_
    unfold MallocngEnv
    exact sepConj_mono_left (Entails.pure_left fun _ => Entails.refl _)
  have h2 := Satisfies.mono (sepConj_mono_left
    (mallocngHeap_read_liveUser_unpack γ A tp brkStart s.brk b ivs p oldSz)) h1
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨st, g, idx, effCost, h2⟩ := h2
  rw [sepConj_assoc, satisfies_pure_sepConj] at h2
  obtain ⟨⟨hg, ⟨hIdx, hSlot⟩, hFacts⟩, h2⟩ := h2
  have hRest : s.mem ⊨ MallocngReadRest γ A tp brkStart s.brk b ivs st ∗
      (MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngBlockToken γ p oldSz ∗ R) := by
    apply (fun e => Satisfies.mono e h2)
    exact Entails.of_eq (by
      generalize (MallocngRoTablesAt A) = P1
      generalize (MallocngReadRest γ A tp brkStart s.brk b ivs st) = P2
      ac_rfl)
  unfold MallocngReadRest at hRest
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hRest
  obtain ⟨⟨_, hWf⟩, _⟩ := hRest
  have hMaxLeEff : max oldSz MallocngMinBlockCost ≤ effCost := hFacts.effCost_bounds.1
  have hEffMem : effCost ∈ g.slots.map slotEffCost := by
    have hSlotMem : SlotState.liveUser p oldSz effCost ∈ g.slots := by
      rw [← hSlot]
      exact List.getElem_mem hIdx
    have := List.mem_map_of_mem (f := slotEffCost) hSlotMem
    simpa [slotEffCost] using this
  have hEffLeGroup : effCost ≤ (g.slots.map slotEffCost).sum := le_sum_of_mem hEffMem
  have hGroupLeTotal : (g.slots.map slotEffCost).sum ≤ totalLiveEffCost st :=
    le_sum_of_mem (List.mem_map_of_mem hg)
  have hTotalLeLive : totalLiveEffCost st ≤ b.liveCost := hWf.effCost_le_live
  omega

theorem rdlRealloc_stepBound_le {req1 req2 peak : Nat} (hle : req1 ≤ req2) :
    MallocngStepBound req1 peak ≤ MallocngStepBound req2 peak := by
  unfold MallocngStepBound Arm64.pageAlignUp PAGE_SIZE
  omega

theorem rdlRealloc_oom_congr {svc : State → State} {req1 req2 peak : Nat}
    {s0 sPre sf : State}
    (hle : req1 ≤ req2)
    (hfs : sPre.fs = s0.fs) (htr : sPre.trace = s0.trace)
    (hsig : sPre.sigActions = s0.sigActions) (hperm : sPre.mem.perm = s0.mem.perm)
    (hoom : MallocngOomCond svc req1 peak sPre sf) :
    MallocngOomCond svc req2 peak s0 sf := by
  rcases hoom with ⟨h1, h2, h3, hdelta, hgap⟩
  have hsb := rdlRealloc_stepBound_le (peak := peak) hle
  refine ⟨h1.trans hfs, h2.trans htr, h3.trans hsig, ?_, fun hsan => ?_⟩
  · obtain ⟨ivs, hlen, hsum, hcov⟩ := hdelta
    refine ⟨ivs, hlen, Nat.le_trans hsum hsb, fun a hm => ?_⟩
    rcases hcov a hm with hmPre | hin
    · exact Or.inl (by rwa [← hperm])
    · exact Or.inr hin
  · obtain ⟨sz, hmin, hmod, hszLe, hng⟩ := hgap hsan
    exact ⟨sz, hmin, hmod, Nat.le_trans hszLe hsb, hng⟩

theorem rdlRealloc_effAlign_props {align effAlign new : BitVec 64}
    (hPow2 : IsPow2Align align) (hAlMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hEff : (effAlign = align ∧ 8 < align.toNat) ∨ (effAlign = 8#64 ∧ align.toNat ≤ 8)) :
    effAlign.toNat ≤ MaxAlignedAllocAlign ∧
    max effAlign.toNat 16 = max align.toNat 16 ∧
    mallocngAlignedEffSize effAlign.toNat new.toNat =
      mallocngAlignedEffSize align.toNat new.toNat ∧
    mallocngPosixMemalignOk effAlign new = decide (MallocngLayoutFit new align) ∧
    mallocngPosixMemalignRet effAlign new =
      (if MallocngLayoutFit new align then 0#32 else 12#32) := by
  have h8Pow2 : IsPow2Align 8#64 := by decide
  have h8Max : (8#64).toNat ≤ MaxAlignedAllocAlign := by decide
  have ⟨hGe8, hLeMax, hEffPow2, hMax16, hEffSz⟩ :
      8 ≤ effAlign.toNat ∧ effAlign.toNat ≤ MaxAlignedAllocAlign ∧
      IsPow2Align effAlign ∧ max effAlign.toNat 16 = max align.toNat 16 ∧
      mallocngAlignedEffSize effAlign.toNat new.toNat =
        mallocngAlignedEffSize align.toNat new.toNat := by
    rcases hEff with ⟨rfl, _⟩ | ⟨rfl, hle⟩
    · exact ⟨by omega, hAlMax, hPow2, rfl, rfl⟩
    · refine ⟨by decide, h8Max, h8Pow2, by simp only [BitVec.toNat_ofNat]; omega, ?_⟩
      change mallocngAlignedEffSize 8 new.toNat = mallocngAlignedEffSize align.toNat new.toNat
      unfold mallocngAlignedEffSize; split <;> split <;> omega
  refine ⟨hLeMax, hMax16, hEffSz, ?_, ?_⟩
  · unfold mallocngPosixMemalignOk mallocngAlignedAllocOk
    rw [decide_eq_true hGe8, isPow2Align_alignedAllocOk hEffPow2]
    simp only [Bool.true_and]
    exact decide_eq_decide.mpr (by unfold MallocngLayoutFit; rw [hEffSz])
  · unfold mallocngPosixMemalignRet isPow2Align
    have hlt8 : ¬ (effAlign.toNat < 8) := by omega
    rw [decide_eq_true hEffPow2]
    simp only [hlt8, Bool.not_true]
    by_cases hf : MallocngLayoutFit new align
    · have hf' : mallocngAlignedEffSize effAlign.toNat new.toNat ≤ MallocngMaxAllocSize := by
        unfold MallocngLayoutFit at hf; omega
      simp [hf, hf']
    · have hf' : ¬ (mallocngAlignedEffSize effAlign.toNat new.toNat ≤ MallocngMaxAllocSize) := by
        unfold MallocngLayoutFit at hf; omega
      simp [hf, hf']

theorem memcpy_allInstrs_noSvc_noMsr (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true := by
  change (pureWordsProg 0#64 memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true
  decide +kernel

theorem memcpy_pureWords_hasWords (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).hasWords addr memcpySymWords := by
  refine pureWordsProg_hasWords (by decide) ?_
  change ((List.range memcpySymWords.length).all fun i =>
    (pureWordsProg 0#64 memcpySymWords).readWordOff (4 * i) == memcpySymWords[i]?) = true
  decide +kernel

theorem memcpy_pureWords_ok (addr dst src : BitVec 64)
    (dstBs srcBs : List (BitVec 8)) (n : BitVec 64)
    (hdstLen : dstBs.length = n.toNat) (hsrcLen : srcBs.length = n.toNat)
    (hn63 : n.toNat ≤ 2 ^ 63) :
    subroutine_ok (pureWordsProg addr memcpySymWords) addr
      { pre := fun (_ : Unit) s =>
          ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ s.readReg64 .x2 = n⌝ ∗
          (dst ↦ₛ dstBs) ∗ (src ↦ₛ srcBs)
        post := fun _ s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab ∧ sf.readReg64 .x0 = dst⌝ ∗
          (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs) } := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(dst ↦ₛ dstBs) ∗ memcpySrc false src srcBs,
    by simpa [memcpySrc, sepConj_assoc] using hmem, ?_⟩
  refine SepWP.mono (memcpy_sepwp false (pureWordsProg addr memcpySymWords) addr
    (memcpy_pureWords_hasWords addr) s0
    dst src n dstBs srcBs hpc hrun hx0 hx1 hx2 hdstLen hsrcLen hn63) ?_
  intro sf P_f _ _ ⟨⟨hx0f, hspf, hcsf, _hfs, _htr, _htp, _hbrks, horc, hsym, _hsig, _hbrk⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  simp only [memcpySrc, Bool.cond_false, sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
  exact ⟨⟨horc, hsym, hx0f⟩, hm'⟩

theorem memRegion_entails_exists_pointsToBytes (n : Nat) (p : BitVec 64) (hn : n ≤ 2 ^ 64) :
    memRegion p n ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (p ↦ₛ bs) := by
  induction n generalizing p with
  | zero =>
    rw [memRegion_zero]
    exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.of_eq (by simp)))
  | succ n ih =>
    have hsucc := memRegion_succ_off p 0 n (by omega)
    have hp0 : p + BitVec.ofNat 64 0 = p := by simp
    have hp1 : p + BitVec.ofNat 64 (0 + 1) = p + 1#64 := rfl
    rw [hp0, hp1] at hsucc
    rw [hsucc]
    refine Entails.trans (sepConj_mono_right (ih (p + 1#64) (by omega))) ?_
    simp only [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun b0 => ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun rest => ?_
    rw [← sepConj_assoc, sepConj_comm (p ↦₈ b0), sepConj_assoc]
    refine Entails.pure_left fun hlen => ?_
    refine Entails.sepExists_right (b0 :: rest) (Entails.pure_right (by simp [hlen]) ?_)
    have hcons := pointsToBytes_cons_off p 0 b0 rest
    rw [hp0, hp1] at hcons
    rw [hcons]; exact Entails.refl _

theorem pack_stack64 (sp v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
    ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
    ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7) ⊢ stackFrameAt sp 64 := by
  dsimp only [reduceStackFrameAt]
  exact Entails.sepExists_right v0 <|
    Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <|
    Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <|
    Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <|
    Entails.sepExists_right v7 <|
    Entails.refl _

theorem copyPrep_entails (p q : BitVec 64) (bs : List (BitVec 8))
    (oldLen newLen copyLen : Nat)
    (h1 : bs.length ≤ copyLen) (h2 : copyLen ≤ oldLen) (h3 : copyLen ≤ newLen)
    (h4 : oldLen ≤ 2 ^ 64) (h5 : newLen ≤ 2 ^ 64) :
    ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (oldLen - bs.length) ∗
     memRegion q newLen) ⊢
    ∃∗ dstBs : List (BitVec 8), ∃∗ midBs : List (BitVec 8),
      ⌜dstBs.length = copyLen ∧ (bs ++ midBs).length = copyLen⌝ ∗
      (q ↦ₛ dstBs) ∗ (p ↦ₛ (bs ++ midBs)) ∗
      memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
      memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen) := by
  have hpSplit : memRegion (p + BitVec.ofNat 64 bs.length) (oldLen - bs.length) =
      (memRegion (p + BitVec.ofNat 64 bs.length) (copyLen - bs.length) ∗
       memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen)) := by
    rw [memRegion_split_le (p + BitVec.ofNat 64 bs.length) (copyLen - bs.length)
      (oldLen - bs.length) (by omega) (by omega)]
    have hadd : p + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (copyLen - bs.length) =
        p + BitVec.ofNat 64 copyLen := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hsub : oldLen - bs.length - (copyLen - bs.length) = oldLen - copyLen := by omega
    rw [hadd, hsub]
  have hqSplit : memRegion q newLen =
      (memRegion q copyLen ∗ memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) :=
    memRegion_split_le q copyLen newLen h3 h5
  rw [hpSplit, hqSplit]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (memRegion_entails_exists_pointsToBytes (copyLen - bs.length) _ (by omega))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memRegion_entails_exists_pointsToBytes copyLen q (by omega))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun dstBs => Entails.sepExists_elim fun midBs => ?_
  refine Entails.sepExists_right dstBs <| Entails.sepExists_right midBs ?_
  have hcomm :
      ((p ↦ₛ bs) ∗ ((⌜midBs.length = copyLen - bs.length⌝ ∗
         ((p + BitVec.ofNat 64 bs.length) ↦ₛ midBs)) ∗
        memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen)) ∗
       (⌜dstBs.length = copyLen⌝ ∗ (q ↦ₛ dstBs)) ∗
       memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) =
      (⌜midBs.length = copyLen - bs.length⌝ ∗ ⌜dstBs.length = copyLen⌝ ∗
       ((q ↦ₛ dstBs) ∗ ((p ↦ₛ bs) ∗ ((p + BitVec.ofNat 64 bs.length) ↦ₛ midBs)) ∗
        memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
        memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen))) := by ac_rfl
  rw [hcomm, ← pointsToBytes_append p bs midBs]
  refine Entails.pure_left fun hmid => Entails.pure_left fun hdst => ?_
  exact Entails.pure_right ⟨hdst, by rw [List.length_append, hmid]; omega⟩ (Entails.refl _)

theorem copyFinish_entails (p q : BitVec 64) (bs midBs : List (BitVec 8))
    (oldLen newLen copyLen : Nat)
    (hmid : (bs ++ midBs).length = copyLen)
    (h2 : copyLen ≤ oldLen) (h3 : copyLen ≤ newLen)
    (h4 : oldLen ≤ 2 ^ 64) (h5 : newLen ≤ 2 ^ 64) :
    ((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗
     memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
     memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) ⊢
    memRegion p oldLen ∗ (q ↦ₛ bs) ∗
      memRegion (q + BitVec.ofNat 64 bs.length) (newLen - bs.length) := by
  have hmidLen : midBs.length = copyLen - bs.length := by
    rw [List.length_append] at hmid; omega
  have hpReg : ((p ↦ₛ (bs ++ midBs)) ∗ memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen)) ⊢
      memRegion p oldLen := by
    refine Entails.trans (sepConj_mono_left (IsBlock.pointsToBytes p (bs ++ midBs)).entails_memRegion) ?_
    rw [hmid, ← memRegion_split_le p copyLen oldLen h2 h4]
    exact Entails.refl _
  have hqReg : (((q + BitVec.ofNat 64 bs.length) ↦ₛ midBs) ∗
      memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) ⊢
      memRegion (q + BitVec.ofNat 64 bs.length) (newLen - bs.length) := by
    refine Entails.trans (sepConj_mono_left (IsBlock.pointsToBytes _ midBs).entails_memRegion) ?_
    rw [hmidLen]
    have hsplit := memRegion_split_le (q + BitVec.ofNat 64 bs.length)
      (copyLen - bs.length) (newLen - bs.length) (by omega) (by omega)
    have hadd : q + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (copyLen - bs.length) =
        q + BitVec.ofNat 64 copyLen := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : bs.length ≤ copyLen := by rw [List.length_append] at hmid; omega
      omega
    have hsub : newLen - bs.length - (copyLen - bs.length) = newLen - copyLen := by
      have : bs.length ≤ copyLen := by rw [List.length_append] at hmid; omega
      omega
    rw [hadd, hsub] at hsplit
    rw [← hsplit]
    exact Entails.refl _
  rw [pointsToBytes_append q bs midBs]
  have hrearr :
      (((q ↦ₛ bs) ∗ ((q + BitVec.ofNat 64 bs.length) ↦ₛ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗
       memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
       memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) =
      (((p ↦ₛ (bs ++ midBs)) ∗ memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen)) ∗
       (q ↦ₛ bs) ∗
       (((q + BitVec.ofNat 64 bs.length) ↦ₛ midBs) ∗
        memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen))) := by ac_rfl
  rw [hrearr]
  exact sepConj_mono hpReg (sepConj_mono_right hqReg)

end VerifiedLibraries.Mallocng.Proofs
