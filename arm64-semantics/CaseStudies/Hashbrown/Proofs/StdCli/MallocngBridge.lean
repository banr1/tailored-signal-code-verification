/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Proofs.StdCli.Layout
import VerifiedLibraries.Mallocng
import ProofLib.MallocngIface
import ProofLib.MallocngBridge
import ProofLib.Placed.Multi
import ProofLib.SyscallModels
import ProofLib.CType
import ProofLib.SepLogic.WP

/-!
# Placement-Generic `mallocng` Bridge

Instantiates `HbMallocngIface` for `hashbrown_std` from `VerifiedLibraries.Mallocng.mallocngTop_ok`
and `ProofLib.MallocngBridge` at an arbitrary `HbCliLayout` and `Obj.MultiPlacement`.
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.Mallocng

/-! ## Placement Bundle `HbMallocngPlaced` -/

/-- Structural placement agreement linking `VerifiedLibraries.mallocngLib` at `mpl` to the CLI RX
    program `P` and layout `C : HbCliLayout`. -/
structure HbMallocngPlaced (P : Program) (C : HbCliLayout) (mpl : Obj.MultiPlacement) : Prop where
  noHooks            : ∀ pc, P.externAt? pc = none
  svc_std            : P.svc = Syscall.standard
  placeable          : VerifiedLibraries.mallocngLib.Placeable mpl
  codeLoaded         : ∀ m, P.CodeLoaded m → VerifiedLibraries.mallocngLib.CodeLoaded mpl m
  brkBase_le         : C.mallocng.brkBase.toNat ≤ 3 * 2 ^ 20
  malloc_addr        : VerifiedLibraries.mallocngLib.fnAddr mpl "malloc" = C.mallocng.mallocAddr
  free_addr          : VerifiedLibraries.mallocngLib.fnAddr mpl "free" = C.mallocng.freeAddr
  calloc_addr        : VerifiedLibraries.mallocngLib.fnAddr mpl "calloc" = C.mallocng.callocAddr
  realloc_addr       : VerifiedLibraries.mallocngLib.fnAddr mpl "realloc" = C.mallocng.reallocAddr
  alignedAlloc_addr  : VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc" = C.mallocng.alignedAllocAddr
  posixMemalign_addr : VerifiedLibraries.mallocngLib.fnAddr mpl "posix_memalign" = C.mallocng.posixMemalignAddr
  sizeClasses_addr   : mpl.ρ "__malloc_size_classes" = C.mallocng.roTablesAddr
  debruijnFree_addr  : mpl.ρ "debruijn32.4681" = C.mallocng.roTablesAddr + 96#64
  medCntTab_addr     : mpl.ρ "med_cnt_tab" = C.mallocng.roTablesAddr + 128#64
  smallCntTab_addr   : mpl.ρ "small_cnt_tab" = C.mallocng.roTablesAddr + 136#64
  debruijnAlloc_addr : mpl.ρ "debruijn32.5048" = C.mallocng.roTablesAddr + 168#64
  ctx_addr           : mpl.ρ "__malloc_context" = C.mallocng.mallocCtxAddr
  lock_addr          : mpl.ρ "__malloc_lock" = C.mallocng.mallocLockAddr
  replaced_addr      : mpl.ρ "__malloc_replaced" = C.mallocng.mallocReplacedAddr
  aaReplaced_addr    : mpl.ρ "__aligned_alloc_replaced" = C.mallocng.alignedAllocReplacedAddr
  needLocks_addr     : C.mallocng.libcNeedLocksAddr = mpl.ρ "__libc" + 3#64
  auxv_addr          : C.mallocng.libcAuxvAddr = mpl.ρ "__libc" + 8#64
  pageSize_addr      : C.mallocng.libcPageSizeAddr = mpl.ρ "__libc" + 48#64

/-! ## Supervisor-Call Validity and Sanitized `mmap` -/

private theorem execMremap_mremapStep (s : State) : MallocngMremapStep s (execMremap s) := by
  intro hflags hal holdPos hnewPos hnewMax holdFit hrw hanon
  dsimp only [execMremap]
  have hf_flags : (s.readReg64 Reg.x3 != MREMAP_MAYMOVE) = false := by rw [hflags]; decide
  have hf_al : ((s.readReg64 Reg.x0).toNat % PAGE_SIZE != 0 || (s.readReg64 Reg.x2).toNat == 0 ||
      !decide ((s.readReg64 Reg.x2).toNat ≤ 2 ^ 64 - PAGE_SIZE)) = false := by
    have h2 : ((s.readReg64 Reg.x2).toNat == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hnewPos)
    simp [hal, h2, hnewMax]
  have hf_old0 : ((s.readReg64 Reg.x1).toNat == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt holdPos)
  have hf_lim : (!decide ((s.readReg64 Reg.x0).toNat + pageAlignUp (s.readReg64 Reg.x1).toNat ≤ USER_VA_LIMIT)) = false := by
    have hfit' : (s.readReg64 Reg.x0).toNat + pageAlignUp (s.readReg64 Reg.x1).toNat ≤ USER_VA_LIMIT := by
      simpa [USER_VA_LIMIT] using holdFit
    simp [hfit']
  have hf_nf : (!s.mem.allPerm (fun p => !p.frozen) (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by
    have hall : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 Reg.x0)
        (pageAlignUp (s.readReg64 Reg.x1).toNat) = true := by
      rw [Memory.allPerm_iff]; intro i hi
      rw [beq_iff_eq.mp ((Memory.allPerm_iff _ _ _ _).mp hrw i hi)]; decide
    simp [hall]
  have hf_can : s.mem.canMap (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat) = false := by
    apply Bool.eq_false_iff.mpr; intro hcan
    have hpos_al : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat := by unfold pageAlignUp PAGE_SIZE; omega
    have h0_unmap := (Memory.allPerm_iff _ _ _ _).mp hcan 0 hpos_al
    rw [beq_iff_eq.mp ((Memory.allPerm_iff _ _ _ _).mp hrw 0 hpos_al)] at h0_unmap
    revert h0_unmap; decide
  have hf_rw : (!s.mem.allPerm (· == some Perm.rw) (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by simp [hrw]
  have hf_anon : (!s.mem.allAnon (s.readReg64 Reg.x0)
      (pageAlignUp (s.readReg64 Reg.x1).toNat)) = false := by simp [hanon]
  simp only [hf_flags, hf_al, hf_old0, hf_lim, hf_nf, hf_can, hf_rw, hf_anon, Bool.false_eq_true, ↓reduceIte]
  split
  · exact Or.inl rfl
  · cases hsan : sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none => exact Or.inl rfl
    | some newBase =>
      simp only []; split
      · next hphys =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hphys
        exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · obtain ⟨hne, hnbAl, hnbFit, hcan⟩ := sanitizeMmapAddr_spec hsan
        exact Or.inr (Or.inr ⟨newBase, hne, hnbAl, by simpa [USER_VA_LIMIT] using hnbFit, hcan, rfl⟩)

theorem allocMallocng_svcValid : MallocngSvcValid allocMallocng := by
  intro s; refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx8; simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, SYS_BRK, SYS_MPROTECT]
  · intro hx8; simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, SYS_MUNMAP, SYS_MPROTECT, SYS_BRK]
  · intro hx8; simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, SYS_MMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP]
  · intro hx8 hx2; simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, hx2, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP]
  · intro hx8
    have heq : allocMallocng s = execMremap s := by
      simp [allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8, MALLOCNG_SYS_MREMAP, SYS_MREMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP]
    rw [heq]; exact execMremap_mremapStep s

theorem allocMallocng_sanitizedSvc : MallocngSanitizedSvc allocMallocng := by
  intro s hrun hx8 hprot hflags hoff hlen hoom
  rw [(allocMallocng_svcValid s).2.2.1 hx8] at hoom
  dsimp only [execMmap] at hoom
  have hf_prot : ((s.readReg64 Reg.x2 != MMAP_PROT_RW && s.readReg64 Reg.x2 != MMAP_PROT_NONE ||
      (s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      s.readReg64 Reg.x5 != 0#64)) = false := by
    rcases hprot with hp | hp <;> simp [hp, hflags, hoff, MMAP_PROT_NONE, MMAP_PROT_RW,
      MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED]
  have h1_pos : 0 < (s.readReg64 Reg.x1).toNat :=
    Nat.pos_of_ne_zero fun h0 => hlen (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hf_len0 : ((s.readReg64 Reg.x1).toNat == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt h1_pos)
  have hf_fix : (s.readReg64 Reg.x3 == MMAP_FLAGS_PRIVATE_ANON_FIXED) = false := by rw [hflags]; decide
  simp only [hf_prot, hf_len0, hf_fix, Bool.false_eq_true, ↓reduceIte] at hoom
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x1).toNat) with
  | none =>
    left; rintro ⟨gap, hmin, hgapAl, hfit, hcan⟩
    have hpos : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat := by unfold pageAlignUp PAGE_SIZE; omega
    have hal : pageAlignUp (s.readReg64 Reg.x1).toNat % PAGE_SIZE = 0 := by unfold pageAlignUp PAGE_SIZE; omega
    obtain ⟨base, hsome⟩ := sanitizeMmapAddr_exists_of_gap
      (s.oracle.mmap s.oracleIdx) hpos hal hmin hgapAl (by simpa [USER_VA_LIMIT] using hfit) hcan
    rw [hsan] at hsome; nomatch hsome
  | some base =>
    rw [hsan] at hoom; dsimp only at hoom; split at hoom
    · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle, State.status_setMem, hrun] at hoom
      nomatch hoom
    · split at hoom
      · next hphys =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hphys
        exact Or.inr (Nat.lt_of_not_ge hphys)
      · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle,
          State.status_setPhysMemAvail, State.status_setMem, hrun] at hoom
        nomatch hoom

/-! ## Heap Representation, Startup Initialization, and Frame Transport -/

private def hbRoPadding (C : HbCliLayout) : SepProp :=
  ((C.mallocng.roTablesAddr + 132#64) ↦ᵣ List.replicate 4 0#8) ∗
  ((C.mallocng.roTablesAddr + 163#64) ↦ᵣ List.replicate 5 0#8)

private theorem roTablesBytes_split {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    (hpl : HbMallocngPlaced P C mpl) :
    (C.mallocng.roTablesAddr ↦ᵣ ProofLib.mallocngRoTablesBytes) =
      (MallocngRoTablesAt (mallocngAddrsOfPlacement mpl) ∗ hbRoPadding C) := by
  have heq : ProofLib.mallocngRoTablesBytes =
      mallocngSizeClassBytes ++ (mallocngDebruijn32Table ++
        (mallocngMedCntTabBytes ++ (List.replicate 4 0#8 ++
          (mallocngSmallCntTabBytes ++ (List.replicate 5 0#8 ++ mallocngDebruijn32Table))))) := by
    rfl
  have hl1 : mallocngSizeClassBytes.length = 96 := rfl
  have hl2 : mallocngDebruijn32Table.length = 32 := rfl
  have hl3 : mallocngMedCntTabBytes.length = 4 := rfl
  have hl4 : (List.replicate 4 0#8).length = 4 := rfl
  have hl5 : mallocngSmallCntTabBytes.length = 27 := rfl
  have hl6 : (List.replicate 5 0#8).length = 5 := rfl
  rw [heq]
  repeat rw [pointsToBytesRO_append]
  simp only [hl1, hl2, hl3, hl4, hl5, hl6, BitVec.add_assoc, BitVec.reduceAdd]
  unfold MallocngRoTablesAt hbRoPadding mallocngAddrsOfPlacement
  dsimp only
  rw [hpl.sizeClasses_addr, hpl.debruijnFree_addr, hpl.medCntTab_addr,
      hpl.smallCntTab_addr, hpl.debruijnAlloc_addr]
  exact Entails.antisymm (by sep_entail) (by sep_entail)

private theorem pointsToWords64_eq_flatMap_bytes (ptr : BitVec 64) :
    ∀ ws : List (BitVec 64),
      (ptr ↦₆₄* ws) =
        (ptr ↦ₛ ws.flatMap fun w => List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8))
  | [] => by simp [pointsToWords64_nil, pointsToBytes_nil]
  | w :: ws => by
    rw [pointsToWords64_cons, List.flatMap_cons, pointsToBytes_append, pointsTo64_eq_pointsToBytes]
    simp only [List.length_ofFn]
    rw [← pointsToWords64_eq_flatMap_bytes (ptr + 8#64) ws]
    rfl

private def hbHeapInv (C : HbCliLayout) (L : Nat)
    (b : MallocngBudget) (lc blk : Nat)
    (staticIvs ivs : List (BitVec 64 × Nat)) (s : State) : Prop :=
  let lim := hbStdLimits L
  s.brkStart = C.mallocng.brkBase ∧
  MallocngBrkStartWf C.mallocng.brkBase ∧
  b.liveCost = lc ∧
  b.liveCount = blk ∧
  b.peakCost ≤ lim.maxPeakCost ∧
  b.peakCount ≤ lim.maxPeakBlocks ∧
  staticIvs.length ≤ 3 ∧
  ((staticIvs.map Prod.snd).sum ≤ 133 * 2 ^ 20 ∧
   (staticIvs.map Prod.snd).sum + hbDynPhysBudget L ≤ physPlusRw s) ∧
  ∀ a : BitVec 64, (s.mem.perm a).mapped = true →
    MallocngInIntervals staticIvs a ∨ MallocngInIntervals ivs a

private noncomputable def hbHeap (C : HbCliLayout) (mpl : Obj.MultiPlacement) (L : Nat)
    (γ : GhostName) (lc blk : Nat) (s : State) : SepProp :=
  let A := mallocngAddrsOfPlacement mpl
  ∃∗ b : MallocngBudget,
  ∃∗ staticIvs : List (BitVec 64 × Nat),
  ∃∗ ivs : List (BitVec 64 × Nat),
    ⌜hbHeapInv C L b lc blk staticIvs ivs s⌝ ∗
    mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk b ivs ∗
    ((A.libc + 3#64) ↦₈ 0#8) ∗
    ((A.libc + 48#64) ↦₆₄ 4096#64) ∗
    hbRoPadding C

private theorem hbBlock_noWrap (γ : GhostName) (p : BitVec 64) (n : Nat) :
    mallocngIface.Block γ p n ⊢ ⌜p ≠ 0#64 ∧ p.toNat + n < 2 ^ 64⌝ ∗ mallocngIface.Block γ p n :=
  Entails.trans (mallocngIfaceFacts_ok.block_nonnull γ p n)
    (Entails.pure_left fun ⟨hne, _, h48, _⟩ => Entails.pure_right ⟨hne, by omega⟩ (Entails.refl _))

private theorem hbBlock_aligned16 (γ : GhostName) (p : BitVec 64) (n : Nat) :
    mallocngIface.Block γ p n ⊢ ⌜16 ∣ p.toNat⌝ ∗ mallocngIface.Block γ p n :=
  Entails.trans (mallocngIfaceFacts_ok.block_nonnull γ p n)
    (Entails.pure_left fun ⟨_, hal, _, _⟩ => Entails.pure_right hal (Entails.refl _))

private theorem hbBlock_userVa (γ : GhostName) (p : BitVec 64) (n : Nat) :
    mallocngIface.Block γ p n ⊢ ⌜p.toNat + n ≤ Arm64.USER_VA_LIMIT⌝ ∗ mallocngIface.Block γ p n :=
  Entails.trans (mallocngIfaceFacts_ok.block_nonnull γ p n)
    (Entails.pure_left fun ⟨_, _, h48, _⟩ => Entails.pure_right h48 (Entails.refl _))

private theorem hbHeap_transport (C : HbCliLayout) (mpl : Obj.MultiPlacement) (L : Nat)
    {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (hbrk : s2.brk = s1.brk) (hbs : s2.brkStart = s1.brkStart)
    (hphys : s2.physMemAvail = s1.physMemAvail)
    (hperm : ∀ a : BitVec 64, s2.mem.perm a = s1.mem.perm a) :
    hbHeap C mpl L γ lc blk s1 ⊢ hbHeap C mpl L γ lc blk s2 := by
  have hpprw : physPlusRw s2 = physPlusRw s1 := by
    unfold physPlusRw; rw [hphys, rwBytes_congr hperm]
  have hinv : ∀ b staticIvs ivs,
      hbHeapInv C L b lc blk staticIvs ivs s1 = hbHeapInv C L b lc blk staticIvs ivs s2 := by
    intro b staticIvs ivs; apply propext; unfold hbHeapInv; simp only [hbs, hpprw, hperm]
  unfold hbHeap
  simp only [hbrk, hinv]
  exact Entails.refl _

private theorem hbHeap_need_locks {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    (hpl : HbMallocngPlaced P C mpl) (L : Nat)
    (γ : GhostName) (lc blk : Nat) (s : State) :
    hbHeap C mpl L γ lc blk s ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ ∃∗ R : SepProp, R := by
  unfold hbHeap
  refine Entails.sepExists_elim fun b => Entails.sepExists_elim fun staticIvs =>
    Entails.sepExists_elim fun ivs => ?_
  rw [hpl.needLocks_addr]
  let A := mallocngAddrsOfPlacement mpl
  refine Entails.trans ?_
    (sepConj_mono_right (Entails.sepExists_right
      (⌜hbHeapInv C L b lc blk staticIvs ivs s⌝ ∗
       mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk b ivs ∗
       ((A.libc + 48#64) ↦₆₄ 4096#64) ∗
       hbRoPadding C) (Entails.refl _)))
  dsimp only [A, mallocngAddrsOfPlacement]
  sep_entail

private theorem hbInitHeap {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    (hpl : HbMallocngPlaced P C mpl) (L : Nat)
    {s : State} {R : SepProp} {imgLo stackBase stackTop : Nat}
    {auxvAddr randomAddr : BitVec 64}
    {prePairs sufPairs : List (BitVec 64 × BitVec 64)}
    {randHi8 : List (BitVec 8)} {e0 : BitVec 32}
    (_hCode : P.CodeLoaded s.mem)
    (_hRoFrz : ∀ i < 200, s.mem.Frozen (C.mallocng.roTablesAddr + BitVec.ofNat 64 i))
    (hWf : MallocngInitialMemWf C.mallocng imgLo stackBase stackTop s)
    (hPhys : (hbStdLimits L).CorePhysMem ≤ s.physMemAvail)
    (hSat : s.mem ⊨ (MallocngInitialBss C.mallocng ∗
             MallocngStartupInputs C.mallocng auxvAddr randomAddr prePairs sufPairs randHi8 e0 s ∗ R)) :
    ∃ (γ : GhostName) (e1 : BitVec 32),
      s.mem ⊨ (hbHeap C mpl L γ 0 0 s ∗ (muslErrnoAddr s ↦₃₂ e1) ∗ R) := by
  let A := mallocngAddrsOfPlacement mpl
  obtain ⟨hbrk, hbrkStart, hbrkAl, hbrkLo, _himgLo, hbrkHi, _hstkLo, hstkOrd, hstkSz, hstkHi, hMapped⟩ := hWf
  have hBrkWf : MallocngBrkStartWf C.mallocng.brkBase := by
    refine ⟨by simpa [MMAP_MIN_ADDR] using hbrkLo, by simpa [PAGE_SIZE] using hbrkAl, by omega⟩
  unfold MallocngStartupInputs MallocngInitialBss at hSat
  rw [roTablesBytes_split hpl] at hSat
  have hAuxvEq : (auxvAddr ↦ₛ encodeAuxvBytes (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs)) =
      (auxvAddr ↦₆₄* ((prePairs ++ [(25#64, randomAddr)] ++ sufPairs ++ [(0#64, 0#64)]).flatMap
        fun (t, v) => [t, v])) := by rw [pointsToWords64_eq_flatMap_bytes]; rfl
  rw [hAuxvEq] at hSat
  have hEntStart :
      ((C.mallocng.mallocLockAddr ↦₃₂ 0#32) ∗ (C.mallocng.alignedAllocReplacedAddr ↦₃₂ 0#32) ∗
       (C.mallocng.mallocReplacedAddr ↦₃₂ 0#32) ∗ (C.mallocng.mallocCtxAddr ↦ₛ List.replicate 928 0#8)) ∗
      (⌜randHi8.length = 8 ∧ 0xa4 ≤ s.tpidrEl0.toNat ∧ s.tpidrEl0.toNat ≤ 2 ^ 48 ∧
        prePairs.length + sufPairs.length ≤ 64 ∧ auxvAddr.toNat % 8 = 0 ∧
        auxvAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧ randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
        (∀ e ∈ prePairs, e.1 ≠ Process.AuxvTag.null ∧ e.1 ≠ Process.AuxvTag.random) ∧
        (∀ e ∈ sufPairs, e.1 ≠ Process.AuxvTag.null ∧ e.1 ≠ Process.AuxvTag.random)⌝ ∗
       (MallocngRoTablesAt A ∗ hbRoPadding C) ∗ (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗
       (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗ (C.mallocng.libcPageSizeAddr ↦₆₄ 4096#64) ∗
       (auxvAddr ↦₆₄* ((prePairs ++ [(25#64, randomAddr)] ++ sufPairs ++ [(0#64, 0#64)]).flatMap
         fun (t, v) => [t, v])) ∗
       ((randomAddr + 8#64) ↦ₛ randHi8) ∗ (muslErrnoAddr s ↦₃₂ e0)) ⊢
      ⌜0xa4 ≤ s.tpidrEl0.toNat ∧ s.tpidrEl0.toNat ≤ 2 ^ 48⌝ ∗
        MallocngStartupResources A s.tpidrEl0 ∗ hbRoPadding C := by
    rw [sepConj_comm ((C.mallocng.mallocLockAddr ↦₃₂ 0#32) ∗ _) _]; simp only [sepConj_assoc]
    refine Entails.pure_left fun ⟨hrlen, htpLo, htpHi, hpLen, _hal, hauxvHi, hrandHi, hpreOk, hsufOk⟩ =>
      Entails.pure_right ⟨htpLo, htpHi⟩ ?_
    unfold MallocngStartupResources MallocngRuntime MallocngAuxvAt muslErrnoAddr
    rw [show A.ctx = C.mallocng.mallocCtxAddr from hpl.ctx_addr,
        show A.lock = C.mallocng.mallocLockAddr from hpl.lock_addr,
        show A.replaced = C.mallocng.mallocReplacedAddr from hpl.replaced_addr,
        show A.aaReplaced = C.mallocng.alignedAllocReplacedAddr from hpl.aaReplaced_addr,
        show C.mallocng.libcNeedLocksAddr = A.libc + 3#64 from hpl.needLocks_addr,
        show C.mallocng.libcAuxvAddr = A.libc + 8#64 from hpl.auxv_addr,
        show C.mallocng.libcPageSizeAddr = A.libc + 48#64 from hpl.pageSize_addr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right auxvAddr (Entails.sepExists_right prePairs
      (Entails.sepExists_right sufPairs (Entails.sepExists_right randomAddr
        (Entails.sepExists_right 0#64 (Entails.sepExists_right randHi8
          (Entails.sepExists_right e0 ?_))))))
    simp only [sepConj_assoc]
    have hPureAuxv : (∀ e ∈ prePairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
        (∀ e ∈ sufPairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧ prePairs.length + sufPairs.length ≤ 64 ∧
        auxvAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
        randomAddr.toNat + 16 ≤ 2 ^ 48 ∧ randHi8.length = 8 :=
      ⟨hpreOk, hsufOk, hpLen, hauxvHi, hrandHi, hrlen⟩
    rw [pure_sepConj_of_true hPureAuxv]; sep_entail
  have hSat2 : s.mem ⊨ (⌜0xa4 ≤ s.tpidrEl0.toNat ∧ s.tpidrEl0.toNat ≤ 2 ^ 48⌝ ∗
      MallocngStartupResources A s.tpidrEl0) ∗ (hbRoPadding C ∗ R) := by
    rw [← sepConj_assoc] at hSat
    exact Satisfies.of_entails (Satisfies.of_entails hSat (sepConj_mono_left hEntStart)) (by sep_entail)
  have hBupd : (⌜0xa4 ≤ s.tpidrEl0.toNat ∧ s.tpidrEl0.toNat ≤ 2 ^ 48⌝ ∗
      MallocngStartupResources A s.tpidrEl0) ⊢
      |==> (∃∗ γ : GhostName, mallocngIface.MallocngHeap γ A s.tpidrEl0 C.mallocng.brkBase C.mallocng.brkBase mallocngZeroBudget []) :=
    Entails.pure_left fun ⟨htpLo, htpHi⟩ => mallocngIfaceFacts_ok.init_resources A s.tpidrEl0 C.mallocng.brkBase htpLo htpHi hBrkWf
  have hSat3 := Satisfies.of_bupd_frame_left hBupd hSat2
  rw [sepExists_sepConj_left, satisfies_sepExists] at hSat3; obtain ⟨γ, hSat3⟩ := hSat3
  rw [mallocngIfaceFacts_ok.heap_split_runtime] at hSat3; unfold MallocngRuntime at hSat3
  have hSat4 : s.mem ⊨ (∃∗ e1 : BitVec 32,
      (mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk mallocngZeroBudget [] ∗
       ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64) ∗ hbRoPadding C) ∗
      (muslErrnoAddr s ↦₃₂ e1) ∗ R) := by
    rw [← hbrk] at hSat3; refine Satisfies.of_entails hSat3 ?_; unfold muslErrnoAddr
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.sepExists_mono fun _ => by sep_entail
  rw [satisfies_sepExists] at hSat4; obtain ⟨e1, hSat4⟩ := hSat4
  let staticIvs : List (BitVec 64 × Nat) :=
    [(0#64, C.mallocng.brkBase.toNat), (BitVec.ofNat 64 stackBase, stackTop - stackBase)]
  have hInv : hbHeapInv C L mallocngZeroBudget 0 0 staticIvs [] s := by
    refine ⟨hbrkStart, hBrkWf, rfl, rfl, Nat.zero_le _, Nat.zero_le _, by simp [staticIvs], ⟨?_, ?_⟩, ?_⟩
    · have := hpl.brkBase_le
      simp only [staticIvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · have := hpl.brkBase_le
      simp only [staticIvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      unfold hbDynPhysBudget MallocngLimits.CorePhysMem hbStdLimits physPlusRw at *
      dsimp +zetaDelta only at *; omega
    · intro a haMap; left
      rcases hMapped a haMap with ⟨_, haBrk⟩ | ⟨haLo, haHi⟩
      · exact ⟨(0#64, C.mallocng.brkBase.toNat), List.mem_cons_self, by simpa using haBrk⟩
      · refine ⟨(BitVec.ofNat 64 stackBase, stackTop - stackBase),
          List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        have hts : Process.TASK_SIZE = 2 ^ 48 := rfl; dsimp only; bv_omega
  refine ⟨γ, e1, Satisfies.of_entails hSat4 (sepConj_mono_left ?_)⟩; unfold hbHeap
  exact Entails.sepExists_right mallocngZeroBudget (Entails.sepExists_right staticIvs
    (Entails.sepExists_right [] (Entails.pure_right hInv (Entails.refl _))))

/-! ## Non-OOM Discharge and Multi-Block Call Bridge -/

private theorem hbStepBound_le {reqBytes peakCount L : Nat}
    (hReq : reqBytes ≤ (272 * L) / 77 + 139272) (hpb : peakCount ≤ 5) :
    Proofs.MallocngTightStepBound reqBytes peakCount ≤ (272 * L) / 77 + 20992000 := by
  have hPg : pageAlignUp (reqBytes + 8192) ≤ reqBytes + 12287 := by
    unfold pageAlignUp PAGE_SIZE; omega
  have hG := Proofs.Cost.mallocngRootGroupBoundAt_le peakCount
  rw [Proofs.MallocngTightStepBound_eq]
  exact Nat.max_le.mpr ⟨by omega, by omega⟩

private theorem hbMallocngOomFalse {C : HbCliLayout} {L : Nat}
    {b : MallocngBudget} {lc blk reqBytes : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {s0 sf : State}
    (hL : L ≤ HashbrownCliMaxStdin)
    (hInv : hbHeapInv C L b lc blk staticIvs ivs0 s0)
    (hIvsLen : ivs0.length ≤ 48 + 2 * b.peakCount)
    (hIvsSum : (ivs0.map Prod.snd).sum ≤
      Proofs.Cost.tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost)
    (hReq : reqBytes ≤ (hbStdLimits L).maxReq)
    (hlcReq : lc + mallocngBlockCost reqBytes ≤ (hbStdLimits L).maxPeakCost)
    (hblkReq : blk + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpprw : physPlusRw sf = physPlusRw s0)
    (hOom : MallocngTightOomCond allocMallocng reqBytes b.peakCount s0 sf) : False := by
  obtain ⟨_, _, hlcEq, hblkEq, hpcLe, hpbLe, hStLen, ⟨hStSum, hDynPhys⟩, hMap0⟩ := hInv
  obtain ⟨_, _, _, deltaIvs, hDeltaLen, hDeltaSum, hDeltaCov, hSanImp⟩ := hOom
  obtain ⟨sz, hSzPos, hSzAl, hSzBound, hTotBound, hNoGapOrPhys⟩ := hSanImp allocMallocng_sanitizedSvc
  let totIvs := staticIvs ++ ivs0 ++ deltaIvs
  have hTotCov : ∀ a : BitVec 64, (sf.mem.perm a).mapped = true →
      ∃ iv ∈ totIvs, (a - iv.1).toNat < iv.2 := by
    intro a haMap
    rcases hDeltaCov a haMap with haMap0 | ⟨iv, hiv, hin⟩
    · rcases hMap0 a haMap0 with ⟨iv, hiv, hin⟩ | ⟨iv, hiv, hin⟩
      · exact ⟨iv, List.mem_append_left _ (List.mem_append_left _ hiv), hin⟩
      · exact ⟨iv, List.mem_append_left _ (List.mem_append_right _ hiv), hin⟩
    · exact ⟨iv, List.mem_append_right _ hiv, hin⟩
  have hCostMin : 65536 ≤ mallocngBlockCost reqBytes ∧ reqBytes ≤ mallocngBlockCost reqBytes := by
    unfold mallocngBlockCost ProofLib.MallocngMinBlockCost; omega
  have hStepBoundHi : Proofs.MallocngTightStepBound reqBytes b.peakCount ≤ (272 * L) / 77 + 20992000 :=
    hbStepBound_le hReq hpbLe
  have hSzMax : sz ≤ (272 * L) / 77 + 20992000 := Nat.le_trans hSzBound hStepBoundHi
  have hDeltaMax : (deltaIvs.map Prod.snd).sum ≤ (272 * L) / 77 + 20992000 :=
    Nat.le_trans hDeltaSum hStepBoundHi
  have hEvLe : (ivs0.map Prod.snd).sum + ((deltaIvs.map Prod.snd).sum + sz) ≤
      (if reqBytes ≤ 856824 then 3074404 + lc else 2217580 + lc + reqBytes) := by
    have hblk4 : b.liveCount ≤ 4 := by
      dsimp only [hbStdLimits] at hblkReq; omega
    have hpb5 : b.peakCount ≤ 5 := by
      dsimp only [hbStdLimits] at hpbLe; omega
    have hMono := Proofs.Cost.tight2EventBudget_mono (Nat.le_refl 6) hblk4 hpb5
      (Nat.le_of_eq hlcEq) (Nat.le_refl reqBytes)
    have hHb := Proofs.Cost.tight2_hb_budget lc reqBytes
    unfold Proofs.Cost.tight2EventBudget at hMono hHb
    have hTotEq : Proofs.MallocngTightTotalBound reqBytes b.peakCount =
        Proofs.Cost.mallocngTight2StepBoundG (Proofs.Cost.tight2RootG b.peakCount) reqBytes b.peakCount := rfl
    omega
  have hSumEq : (totIvs.map Prod.snd).sum =
      (staticIvs.map Prod.snd).sum + (ivs0.map Prod.snd).sum + (deltaIvs.map Prod.snd).sum := by
    simp [totIvs, List.map_append, List.sum_append, Nat.add_assoc]
  rcases hNoGapOrPhys with hNoGap | hNoPhys
  · have hTotLen : totIvs.length ≤ 77 := by
      have : totIvs.length = staticIvs.length + ivs0.length + deltaIvs.length := by
        simp [totIvs, List.length_append, Nat.add_assoc]
      dsimp only [hbStdLimits] at hpbLe; omega
    have hMul : totIvs.length * (sz + PAGE_SIZE) + sz ≤
        77 * ((272 * L) / 77 + 20992000 + 4096) + ((272 * L) / 77 + 20992000) :=
      Nat.add_le_add (Nat.mul_le_mul hTotLen (Nat.add_le_add hSzMax (Nat.le_refl 4096))) hSzMax
    have hFitGap : MMAP_MIN_ADDR + (totIvs.map Prod.snd).sum +
        totIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48 := by
      have h272 : (272 * L) / 77 ≤ 4 * L := by omega
      have h562 : (562 * L) / 77 ≤ 8 * L := by omega
      have hlcHi : lc ≤ 8 * L + 270464 ∧ lc + reqBytes ≤ 8 * L + 336000 := by
        dsimp only [hbStdLimits] at hlcReq; omega
      have hLmax : L ≤ 10 * 2 ^ 30 := hL
      have hPage : PAGE_SIZE = 4096 := rfl
      have hMmap : MMAP_MIN_ADDR = 65536 := rfl
      split at hEvLe <;> omega
    exact hNoGap (hasGap_of_mappedIntervals hTotCov hSzPos hSzAl hFitGap)
  · have hrwLe := rwBytes_le_intervals_sum hTotCov
    have h562 : (562 * L) / 77 ≤ 8 * L := by omega
    have hlcLe : lc ≤ 8 * L + 270464 ∧ lc + reqBytes ≤ 8 * L + 336000 := by
      dsimp only [hbStdLimits] at hlcReq; omega
    have hDynLe : (ivs0.map Prod.snd).sum + ((deltaIvs.map Prod.snd).sum + sz) ≤ hbDynPhysBudget L := by
      unfold hbDynPhysBudget
      split at hEvLe <;> omega
    dsimp only [physPlusRw] at hDynPhys hpprw
    omega

private theorem hbMaxReq_le_maxAlloc {L : Nat} (hL : L ≤ HashbrownCliMaxStdin) :
    (hbStdLimits L).maxReq ≤ MallocngMaxAllocSize := by
  have hFits := hbStdLimits_fitsVaSpace hL
  unfold MallocngLimits.FitsVaSpace at hFits
  dsimp +zetaDelta only at hFits
  have ⟨h1, _⟩ := of_decide_eq_true hFits
  unfold MallocngMaxAllocSize
  omega

private theorem hbHeap_to_env (C : HbCliLayout) (mpl : Obj.MultiPlacement)
    (L : Nat) (γ : GhostName) (lc blk : Nat) (e0 : BitVec 32) (s0 : State) :
    hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ⊢
      ∃∗ b : MallocngBudget, ∃∗ staticIvs : List (BitVec 64 × Nat), ∃∗ ivs0 : List (BitVec 64 × Nat),
        ⌜hbHeapInv C L b lc blk staticIvs ivs0 s0⌝ ∗
        MallocngEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b ivs0 s0 ∗
        hbRoPadding C := by
  unfold hbHeap; simp only [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun b => Entails.sepExists_mono fun staticIvs =>
    Entails.sepExists_mono fun ivs0 => ?_
  simp only [sepConj_assoc]; refine Entails.pure_left fun hInv => Entails.pure_right hInv ?_
  unfold MallocngEnv
  rw [pure_sepConj_of_true ⟨rfl, hInv.1⟩, mallocngIfaceFacts_ok.heap_split_runtime]
  unfold MallocngRuntime muslErrnoAddr; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right e0 (by sep_entail)

private theorem hbHeap_of_postEnv {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} {γ : GhostName} {b b' : MallocngBudget} {lc blk lc' blk' : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {s0 sf : State}
    (hInv0 : hbHeapInv C L b lc blk staticIvs ivs0 s0) (hpprw : physPlusRw sf = physPlusRw s0)
    (hb'_lc : b'.liveCost = lc') (hb'_blk : b'.liveCount = blk')
    (hb'_pc : b'.peakCost ≤ (hbStdLimits L).maxPeakCost)
    (hb'_pb : b'.peakCount ≤ (hbStdLimits L).maxPeakBlocks) :
    MallocngPostEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b' ivs0 s0 sf ∗
      hbRoPadding C ⊢
      hbHeap C mpl L γ lc' blk' sf ∗ (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) := by
  unfold MallocngPostEnv MallocngEnv; simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ivsf => ?_; simp only [sepConj_assoc]
  refine Entails.pure_left fun hNoOrphan => Entails.pure_left fun ⟨_htp, hbs_f⟩ => ?_
  rw [mallocngIfaceFacts_ok.heap_split_runtime]; unfold MallocngRuntime muslErrnoAddr
  have hInvF : hbHeapInv C L b' lc' blk' staticIvs ivsf sf := by
    obtain ⟨_, hBrkWf, _, _, _, _, hStLen, hPhys0, hMap0⟩ := hInv0
    refine ⟨hbs_f, hBrkWf, hb'_lc, hb'_blk, hb'_pc, hb'_pb, hStLen, hpprw.symm ▸ hPhys0, fun a haMapF => ?_⟩
    cases hm0 : (s0.mem.perm a).mapped with
    | false => exact Or.inr (hNoOrphan a haMapF (Or.inl hm0))
    | true =>
      exact (hMap0 a hm0).elim Or.inl fun hDyn0 => Or.inr (hNoOrphan a haMapF (Or.inr hDyn0))
  unfold hbHeap; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun e1 => Entails.sepExists_right e1
    (Entails.sepExists_right b' (Entails.sepExists_right staticIvs (Entails.sepExists_right ivsf ?_)))
  simp only [sepConj_assoc]; rw [pure_sepConj_of_true hInvF]; sep_entail

private theorem hbStack_split (sp : BitVec 64) (stackSz : Nat)
    (h1 : 1024 ≤ stackSz := by decide) (h2 : stackSz ≤ 2 ^ 64 := by decide) :
    stackAt sp stackSz =
      stackFrameAt sp mallocngStackBytes ∗ memRegion (sp - BitVec.ofNat 64 stackSz) (stackSz - 1024) := by
  rw [stackAt_shrink sp stackSz 1024 h1 h2, stackAt_eq_stackFrameAt sp 1024, sepConj_comm]

private theorem hbExtractEnvBounds {γ : GhostName} {A : VerifiedLibraries.Mallocng.MallocngAddrs}
    {tp brkStart : BitVec 64} {b : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)} {s0 : State} {R : SepProp}
    (hsat : s0.mem ⊨ MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ R) :
    (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
    ivs0.length ≤ 48 + 2 * b.peakCount ∧
    (ivs0.map Prod.snd).sum ≤
      Proofs.Cost.tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost := by
  let φ := (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
    ivs0.length ≤ 48 + 2 * b.peakCount ∧
    (ivs0.map Prod.snd).sum ≤
      Proofs.Cost.tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost
  have hent : MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ R ⊢
      ⌜φ⌝ ∗ (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ R) := by
    unfold MallocngEnv
    have hh : mallocngIface.MallocngHeap γ A tp brkStart s0.brk b ivs0 ⊢
        ⌜φ⌝ ∗ mallocngIface.MallocngHeap γ A tp brkStart s0.brk b ivs0 :=
      Entails.extract_heap_fact (Proofs.Cost.mallocngHeap_ivs_tight2_bound γ A tp brkStart s0.brk b ivs0)
    exact Entails.trans (sepConj_mono_left (sepConj_mono_right hh)) (by sep_entail)
  have hsat' := Satisfies.of_entails hsat hent
  rw [satisfies_pure_sepConj] at hsat'; exact hsat'.1

private theorem hbStatePreserved_of_accounting {maxIvs maxBytes : Nat} {s0 sf : State}
    (hacc : MallocngCallAccounting maxIvs maxBytes s0 sf) (hkf : s0.mem.KeepsFrozen sf.mem) :
    MallocngStatePreserved s0 sf :=
  let ⟨⟨hfs, htr, htp, _, _, _, hsig⟩, _⟩ := hacc; ⟨hfs, htr, hsig, htp, hkf⟩

private theorem hbRunPlacedCall {S β α : Type} [ToBaseSpec S β]
    {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    (hpl : HbMallocngPlaced P C mpl)
    {fnName : String} {entryAddr : BitVec 64}
    {innerSpec : S} {callerSpec : Spec α}
    (hentry : mallocngMultiEntryOk mpl allocMallocng fnName innerSpec)
    (hAddr : VerifiedLibraries.mallocngLib.fnAddr mpl fnName = entryAddr)
    (href : ∀ (x : α) (R : SepProp) (s0 : State) (b_base : BitVec 64),
      (s0.mem ⊨ callerSpec.pre x s0 ∗ R) →
      ∃ (y : β) (R_inner : SepProp),
        (s0.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).pre y s0 ∗ R_inner) ∧
        (∀ sf : State, physPlusRw sf = physPlusRw s0 →
          ¬(sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).onOom y s0 sf ∗ R_inner)) ∧
        (∀ sf : State, physPlusRw sf = physPlusRw s0 → s0.mem.KeepsFrozen sf.mem →
          (sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b_base).post y s0 sf ∗ R_inner) →
          (sf.mem ⊨ callerSpec.post x s0 sf ∗ R)))
    (hNoPanic : ∀ (y : β) (b : BitVec 64) (R' : SepProp) (s0 sf : State),
      sf.status = .Panicked → ¬(sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onPanic y s0 sf ∗ R') := by
        intro _ _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hNoExit : ∀ (y : β) (b : BitVec 64) (code : BitVec 64) (R' : SepProp) (s0 sf : State),
      sf.status = .Exited code → ¬(sf.mem ⊨ (ToBaseSpec.toSpec innerSpec b).onExit y code s0 sf ∗ R') := by
        intro _ _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok P entryAddr callerSpec := by
  obtain ⟨_hexp, i, off, hlookup, hsub_blk⟩ := hentry
  obtain ⟨hi, _⟩ := lookupBlockSym_some hlookup
  have hsub_alloc : subroutine_ok (P.withSvc allocMallocng) entryAddr
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl (ToBaseSpec.toSpec innerSpec (mpl.base i))) := by
    rw [← hAddr]
    refine MultiPlacedLib.subroutine_ok_of_block_hooks hi hsub_blk ?_ rfl
    intro pc
    change _ = P.externAt? pc
    rw [hpl.noHooks pc]
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, Program.externAt?, Program.hookAtOff?]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp hclP => ?_
  have hclLib : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem := hpl.codeLoaded s0.mem hclP
  obtain ⟨y, R_inner, hpre_inner, hNoOom, hPostMap⟩ := href x R s0 (mpl.base i) hpre
  have hpre_wcl : s0.mem ⊨
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl (ToBaseSpec.toSpec innerSpec (mpl.base i))).pre y s0 ∗
        R_inner := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_assoc, pure_sepConj_of_true hclLib]
    exact hpre_inner
  have hreach := subroutine_ok_apply_full hsub_alloc y R_inner hpc hrun hpre_wcl hsp
    (fun sf hst hp => hNoPanic y (mpl.base i) R_inner s0 sf hst hp)
    (fun code sf hst he => hNoExit y (mpl.base i) code R_inner s0 sf hst he)
    (fun _ _ ho => ho)
  obtain ⟨sf, hsteps_alloc, hbranch⟩ := hreach (hclP.of_base_code rfl rfl)
  have hpprw : physPlusRw sf = physPlusRw s0 :=
    physPlusRw_steps_withSvc_alloc hpl.noHooks hsteps_alloc
  rcases hbranch with ⟨hpc_f, hrun_f, ⟨hpost_inner, hcc⟩⟩ | ⟨_hoom_st, hoom_sat⟩
  · have hsteps_P : Steps P s0 sf :=
      steps_of_withSvc_alloc hpl.noHooks hpl.svc_std hsteps_alloc hrun_f
    exact ⟨sf, hsteps_P, Or.inl ⟨hpc_f, hrun_f,
      ⟨hPostMap sf hpprw hsteps_P.keepsFrozen hpost_inner, hcc⟩⟩⟩
  · exact False.elim (hNoOom sf hpprw hoom_sat)

/-! ## Lowering `malloc`, `free`, and `realloc` to `HbMallocngIface` -/

private theorem hbUnpackPre (stackSz : Nat) (Rest : SepProp)
    {C : HbCliLayout} {mpl : Obj.MultiPlacement} {L : Nat} {γ : GhostName} {lc blk : Nat}
    {e0 : BitVec 32} {s0 : State}
    (hpre : s0.mem ⊨ (hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0)) ∗ (stackAt s0.sp stackSz ∗ Rest))
    (hs1 : 1024 ≤ stackSz := by decide) (hs2 : stackSz ≤ 2 ^ 64 := by decide) :
    ∃ b staticIvs ivs0, hbHeapInv C L b lc blk staticIvs ivs0 s0 ∧
      ivs0.length ≤ 48 + 2 * b.peakCount ∧
      (ivs0.map Prod.snd).sum ≤
        Proofs.Cost.tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost ∧
      (s0.mem ⊨ MallocngEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b ivs0 s0 ∗
        hbRoPadding C ∗
        (stackFrameAt s0.sp mallocngStackBytes ∗ memRegion (s0.sp - BitVec.ofNat 64 stackSz) (stackSz - 1024)) ∗
        Rest) := by
  have hpre2 := Satisfies.of_entails hpre (sepConj_mono_left (hbHeap_to_env C mpl L γ lc blk e0 s0))
  simp only [sepExists_sepConj_left] at hpre2
  rw [satisfies_sepExists] at hpre2; obtain ⟨b, hpre2⟩ := hpre2
  rw [satisfies_sepExists] at hpre2; obtain ⟨staticIvs, hpre2⟩ := hpre2
  rw [satisfies_sepExists] at hpre2; obtain ⟨ivs0, hpre2⟩ := hpre2
  simp only [sepConj_assoc] at hpre2; rw [satisfies_pure_sepConj] at hpre2; obtain ⟨hInv0, hpre2⟩ := hpre2
  obtain ⟨_hlive, hIvsLen, hIvsSum⟩ := hbExtractEnvBounds hpre2
  rw [hbStack_split s0.sp stackSz hs1 hs2] at hpre2
  exact ⟨b, staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpre2⟩

private theorem hbAllocBudget_ok {C : HbCliLayout} {L : Nat}
    {b : MallocngBudget} {lc blk req : Nat} {staticIvs ivs0 : List (BitVec 64 × Nat)} {s0 : State}
    (hInv0 : hbHeapInv C L b lc blk staticIvs ivs0 s0)
    (hlc_le : lc + mallocngBlockCost req ≤ (hbStdLimits L).maxPeakCost)
    (hblk_le : blk + 1 ≤ (hbStdLimits L).maxPeakBlocks) :
    let b' := mallocngAllocBudget true req b
    b'.liveCost = lc + mallocngBlockCost req ∧ b'.liveCount = blk + 1 ∧
    b'.peakCost ≤ (hbStdLimits L).maxPeakCost ∧ b'.peakCount ≤ (hbStdLimits L).maxPeakBlocks := by
  obtain ⟨_, _, hlc, hblk, hpc, hpb, _⟩ := hInv0
  dsimp only; simp only [mallocngAllocBudget, ↓reduceIte]
  have hmc : max req VerifiedLibraries.Mallocng.MallocngMinBlockCost = mallocngBlockCost req := rfl
  exact ⟨by rw [hlc, hmc], by rw [hblk], by omega, by omega⟩

private theorem hbExtractBlockFacts (Rest : SepProp) {γ : GhostName} {p : BitVec 64} {n : Nat}
    {m : Memory} (h : m ⊨ mallocngIface.Block γ p n ∗ Rest) :
    16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64 := by
  have h1 := Satisfies.of_entails h (sepConj_mono_left (mallocngIfaceFacts_ok.block_nonnull γ p n))
  simp only [sepConj_assoc] at h1; rw [satisfies_pure_sepConj] at h1
  exact ⟨h1.1.2.1, Nat.lt_of_le_of_lt h1.1.2.2.1 (by decide)⟩

private theorem hbRewritePostEnv (stackSz : Nat) (Rest : SepProp)
    {C : HbCliLayout} {mpl : Obj.MultiPlacement} {L : Nat} {γ : GhostName}
    {b b' : MallocngBudget} {lc blk lc' blk' : Nat} {staticIvs ivs0 : List (BitVec 64 × Nat)} {s0 sf : State}
    (hInv0 : hbHeapInv C L b lc blk staticIvs ivs0 s0) (hpprw : physPlusRw sf = physPlusRw s0)
    (hb'_lc : b'.liveCost = lc') (hb'_blk : b'.liveCount = blk')
    (hb'_pc : b'.peakCost ≤ (hbStdLimits L).maxPeakCost)
    (hb'_pb : b'.peakCount ≤ (hbStdLimits L).maxPeakBlocks)
    (h : sf.mem ⊨ (MallocngPostEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b' ivs0 s0 sf ∗
        hbRoPadding C) ∗
      (stackFrameAt s0.sp mallocngStackBytes ∗ memRegion (s0.sp - BitVec.ofNat 64 stackSz) (stackSz - 1024)) ∗ Rest)
    (hs1 : 1024 ≤ stackSz := by decide) (hs2 : stackSz ≤ 2 ^ 64 := by decide) :
    sf.mem ⊨ hbHeap C mpl L γ lc' blk' sf ∗ (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
      stackAt s0.sp stackSz ∗ Rest := by
  have h2 := Satisfies.of_entails h (sepConj_mono_left (hbHeap_of_postEnv hInv0 hpprw hb'_lc hb'_blk hb'_pc hb'_pb))
  rw [← hbStack_split s0.sp stackSz hs1 hs2] at h2
  exact Satisfies.of_entails h2 (by sep_entail)

private noncomputable def hbCoreIface {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} (hpl : HbMallocngPlaced P C mpl) (hL : L ≤ HashbrownCliMaxStdin) :
    ProofLib.MallocngCoreIface P C.mallocng (hbStdLimits L) where
  Heap := hbHeap C mpl L
  Block := mallocngIface.Block
  block_noWrap := hbBlock_noWrap
  block_aligned16 := hbBlock_aligned16
  block_userVa := hbBlock_userVa
  heap_transport := hbHeap_transport C mpl L
  heap_need_locks := hbHeap_need_locks hpl L
  init_heap := hbInitHeap hpl L
  malloc_ok γ := by
    have hMaxAlloc : (hbStdLimits L).maxReq ≤ MallocngMaxAllocSize := hbMaxReq_le_maxAlloc hL
    have hmalloc := mallocngPlacedMallocTight_ok mpl allocMallocng hpl.placeable allocMallocng_svcValid γ
    refine hbRunPlacedCall hpl hmalloc hpl.malloc_addr ?_
    intro ⟨lc, blk, req, e0⟩ R s0 _b_base hpre
    simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hreq_eq, hreq_le, hlc_le, hblk_le⟩, hpre⟩ := hpre
    obtain ⟨b, _staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpre2⟩ :=
      hbUnpackPre MallocngStackBytes R (Satisfies.of_entails hpre (by sep_entail))
    have hok : decide ((s0.readReg64 (.gpr 0#5)).toNat ≤ MallocngMaxAllocSize) = true :=
      decide_eq_true (by rw [← hreq_eq]; exact Nat.le_trans hreq_le hMaxAlloc)
    refine ⟨(s0.readReg64 (.gpr 0#5), s0.sp, s0.tpidrEl0, C.mallocng.brkBase, b, ivs0),
      hbRoPadding C ∗ memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R,
      ?_, ?_, ?_⟩
    · dsimp only [mallocngMallocTightSpec, Proofs.mallocngMallocTightSpec, ToBaseSpec.toSpec]
      simp only [ctype_simp, sepConj_assoc]; rw [pure_sepConj_of_true (by simp)]
      exact Satisfies.of_entails hpre2 (by sep_entail)
    · intro sf hpprw hoom
      dsimp only [mallocngMallocTightSpec, Proofs.mallocngMallocTightSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      have hoom' : MallocngTightOomCond allocMallocng req b.peakCount s0 sf := by
        have h := hoom.1; rw [hok] at h; simpa [← hreq_eq] using h
      exact hbMallocngOomFalse hL hInv0 hIvsLen hIvsSum hreq_le hlc_le hblk_le hpprw hoom'
    · intro sf hpprw hkf hpost
      dsimp only [mallocngMallocTightSpec, Proofs.mallocngMallocTightSpec, ToBaseSpec.toSpec] at hpost
      rw [hok] at hpost
      simp only [↓reduceIte, ctype_simp, MallocngBlock, sepConj_assoc] at hpost
      rw [satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨_, hret_ne, hret_al, hret_fit⟩, hacc⟩, hpost⟩ := hpost
      have hpres := hbStatePreserved_of_accounting hacc hkf
      change sf.readReg64 (.gpr 0#5) ≠ 0#64 at hret_ne
      change 16 ∣ (sf.readReg64 (.gpr 0#5)).toNat at hret_al
      change (sf.readReg64 (.gpr 0#5)).toNat + (s0.readReg64 (.gpr 0#5)).toNat < 2 ^ 64 at hret_fit
      rw [← hreq_eq] at hpost hret_fit
      obtain ⟨hb'_lc, hb'_blk, hb'_pc, hb'_pb⟩ := hbAllocBudget_ok hInv0 hlc_le hblk_le
      have hpost_sp2 := hbRewritePostEnv MallocngStackBytes
        (mallocngIface.Block γ (sf.readReg64 (.gpr 0#5)) req ∗ memRegion (sf.readReg64 (.gpr 0#5)) req ∗ R)
        hInv0 hpprw hb'_lc hb'_blk hb'_pc hb'_pb (Satisfies.of_entails hpost (by sep_entail))
      dsimp only; simp only [sepConj_assoc]
      rw [pure_sepConj_of_true ⟨hpres, hret_ne, hret_al, hret_fit⟩]
      exact Satisfies.of_entails hpost_sp2 (by sep_entail)
  free_ok γ := by
    have hentries := mallocngPlacedEntries_ok mpl allocMallocng hpl.placeable allocMallocng_svcValid
    refine hbRunPlacedCall hpl (hentries.free_ok γ) hpl.free_addr ?_
    intro ⟨lc, blk, optReq, e0⟩ R s0 _b_base hpre
    cases optReq with
    | none =>
      dsimp only at hpre
      have hpre0 : s0.mem ⊨ ⌜s0.readReg64 (.gpr 0#5) = 0#64⌝ ∗
          ((hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0)) ∗
            (stackAt s0.sp MallocngStackBytes ∗ R)) :=
        Satisfies.of_entails hpre (by sep_entail)
      rw [satisfies_pure_sepConj] at hpre0; obtain ⟨hp0, hpre0⟩ := hpre0
      obtain ⟨b, _staticIvs, ivs0, hInv0, _, _, hpre3⟩ := hbUnpackPre MallocngStackBytes R hpre0
      refine ⟨(s0.readReg64 (.gpr 0#5), s0.sp, 0, s0.tpidrEl0, C.mallocng.brkBase, b, ivs0),
        hbRoPadding C ∗ memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R,
        ?_, (fun _ _ ho => not_satisfies_false_sepConj ho), ?_⟩
      · dsimp only [mallocngFreeSpec, ToBaseSpec.toSpec, MallocngFreeableBlock]
        simp only [hp0, ↓reduceIte, ctype_simp, emp_sepConj, sepConj_assoc]
        rw [pure_sepConj_of_true (by simp)]; exact Satisfies.of_entails hpre3 (by sep_entail)
      · intro sf hpprw hkf hpost
        dsimp only [mallocngFreeSpec, ToBaseSpec.toSpec] at hpost
        rw [show (s0.readReg64 (.gpr 0#5) == 0#64) = true by simp [hp0]] at hpost
        simp only [mallocngFreeBudget, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost; obtain ⟨hacc, hpost⟩ := hpost
        have hpost_sp2 := hbRewritePostEnv MallocngStackBytes R
          hInv0 hpprw hInv0.2.2.1 hInv0.2.2.2.1 hInv0.2.2.2.2.1 hInv0.2.2.2.2.2.1
          (Satisfies.of_entails hpost (by sep_entail))
        dsimp only; simp only [sepConj_assoc]
        rw [pure_sepConj_of_true (hbStatePreserved_of_accounting hacc hkf)]
        exact Satisfies.of_entails hpost_sp2 (by sep_entail)
    | some req =>
      dsimp only at hpre
      have hpre0 : s0.mem ⊨ ⌜s0.readReg64 (.gpr 0#5) ≠ 0#64⌝ ∗
          ((hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0)) ∗
            (stackAt s0.sp MallocngStackBytes ∗
              (mallocngIface.Block γ (s0.readReg64 (.gpr 0#5)) req ∗ memRegion (s0.readReg64 (.gpr 0#5)) req ∗ R))) :=
        Satisfies.of_entails hpre (by sep_entail)
      rw [satisfies_pure_sepConj] at hpre0; obtain ⟨hp_ne, hpre0⟩ := hpre0
      obtain ⟨b, _staticIvs, ivs0, hInv0, _, _, hpre2⟩ :=
        hbUnpackPre MallocngStackBytes
          (mallocngIface.Block γ (s0.readReg64 (.gpr 0#5)) req ∗ memRegion (s0.readReg64 (.gpr 0#5)) req ∗ R) hpre0
      obtain ⟨hp_al, hp_fit⟩ := hbExtractBlockFacts
        (memRegion (s0.readReg64 (.gpr 0#5)) req ∗
          MallocngEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b ivs0 s0 ∗
          hbRoPadding C ∗ stackFrameAt s0.sp mallocngStackBytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R)
        (Satisfies.of_entails hpre2 (by sep_entail))
      refine ⟨(s0.readReg64 (.gpr 0#5), s0.sp, req, s0.tpidrEl0, C.mallocng.brkBase, b, ivs0),
        hbRoPadding C ∗ memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R,
        ?_, (fun _ _ ho => not_satisfies_false_sepConj ho), ?_⟩
      · dsimp only [mallocngFreeSpec, ToBaseSpec.toSpec, MallocngFreeableBlock]
        simp only [hp_ne, ↓reduceIte, ctype_simp, sepConj_assoc]
        rw [pure_sepConj_of_true (by simp [hp_al, hp_fit])]
        exact Satisfies.of_entails hpre2 (by sep_entail)
      · intro sf hpprw hkf hpost
        dsimp only [mallocngFreeSpec, ToBaseSpec.toSpec] at hpost
        rw [beq_eq_false_iff_ne.mpr hp_ne] at hpost
        simp only [ctype_simp, sepConj_assoc] at hpost
        rw [satisfies_pure_sepConj] at hpost; obtain ⟨hacc, hpost⟩ := hpost
        have hb'_lc : (mallocngFreeBudget false req b).liveCost = lc - mallocngBlockCost req := by
          dsimp [mallocngFreeBudget, mallocngBlockCost, VerifiedLibraries.Mallocng.MallocngMinBlockCost]
          rw [hInv0.2.2.1]
        have hb'_blk : (mallocngFreeBudget false req b).liveCount = blk - 1 := by
          dsimp [mallocngFreeBudget]; rw [hInv0.2.2.2.1]
        have hpost_sp2 := hbRewritePostEnv MallocngStackBytes R
          hInv0 hpprw hb'_lc hb'_blk hInv0.2.2.2.2.1 hInv0.2.2.2.2.2.1
          (Satisfies.of_entails hpost (by sep_entail))
        dsimp only; simp only [sepConj_assoc]
        rw [pure_sepConj_of_true (hbStatePreserved_of_accounting hacc hkf)]
        exact Satisfies.of_entails hpost_sp2 (by sep_entail)

private noncomputable def hbMallocngIfaceImpl {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} (hpl : HbMallocngPlaced P C mpl) (hL : L ≤ HashbrownCliMaxStdin) :
    HbMallocngIface P C.mallocng (hbStdLimits L) where
  toMallocngCoreIface := hbCoreIface hpl hL
  realloc_ok γ := by
    have hMaxAlloc : (hbStdLimits L).maxReq ≤ MallocngMaxAllocSize := hbMaxReq_le_maxAlloc hL
    have hrealloc := mallocngPlacedReallocTight_ok mpl allocMallocng hpl.placeable allocMallocng_svcValid γ
    refine hbRunPlacedCall hpl hrealloc hpl.realloc_addr ?_
    intro ⟨lc, blk, oldBlk, newReq, e0⟩ R s0 _b_base hpre
    dsimp only [hbCoreIface] at hpre; simp only [sepConj_assoc] at hpre
    rw [satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hnew_eq, hnew_le, hlc_le, hblk_le⟩, hpre⟩ := hpre
    have hok : decide ((s0.readReg64 (.gpr 1#5)).toNat ≤ MallocngMaxAllocSize) = true :=
      decide_eq_true (by rw [← hnew_eq]; exact Nat.le_trans hnew_le hMaxAlloc)
    have hpre_unpacked : ∃ b staticIvs ivs0,
        hbHeapInv C L b lc blk staticIvs ivs0 s0 ∧
        ivs0.length ≤ 48 + 2 * b.peakCount ∧
        (ivs0.map Prod.snd).sum ≤
          Proofs.Cost.tight2Footprint (b.peakCount + 6) b.peakCount b.liveCount b.liveCost ∧
        (s0.mem ⊨ (ToBaseSpec.toSpec (mallocngReallocTightSpec mallocngIface allocMallocng γ (mallocngAddrsOfPlacement mpl)) _b_base).pre
            (s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), s0.sp, oldBlk,
              s0.tpidrEl0, C.mallocng.brkBase, b, ivs0) s0 ∗
          (hbRoPadding C ∗
            memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R)) := by
      rcases oldBlk with _ | ⟨oldReq, bs⟩
      · dsimp only at hpre
        have hpre0 : s0.mem ⊨ ⌜s0.readReg64 (.gpr 0#5) = 0#64⌝ ∗
            ((hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0)) ∗
              (stackAt s0.sp MallocngStackBytes ∗ R)) :=
          Satisfies.of_entails hpre (by sep_entail)
        rw [satisfies_pure_sepConj] at hpre0; obtain ⟨hp0, hpre0⟩ := hpre0
        obtain ⟨b, staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpre2⟩ :=
          hbUnpackPre MallocngStackBytes R hpre0
        refine ⟨b, staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, ?_⟩
        dsimp only [mallocngReallocTightSpec, Proofs.mallocngReallocTightSpec, ToBaseSpec.toSpec]
        simp only [ctype_simp, sepConj_assoc]
        rw [pure_sepConj_of_true (by simp), pure_sepConj_of_true hp0]
        exact Satisfies.of_entails hpre2 (by sep_entail)
      · dsimp only at hpre
        have hpre0 : s0.mem ⊨ ⌜s0.readReg64 (.gpr 0#5) ≠ 0#64 ∧ bs.length = oldReq⌝ ∗
            ((hbHeap C mpl L γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0)) ∗
              (stackAt s0.sp MallocngStackBytes ∗
                (mallocngIface.Block γ (s0.readReg64 (.gpr 0#5)) oldReq ∗ (s0.readReg64 (.gpr 0#5) ↦ₛ bs) ∗ R))) :=
          Satisfies.of_entails hpre (by sep_entail)
        rw [satisfies_pure_sepConj] at hpre0; obtain ⟨⟨hp_ne, hbs_len⟩, hpre0⟩ := hpre0
        obtain ⟨b, staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpre2⟩ :=
          hbUnpackPre MallocngStackBytes
            (mallocngIface.Block γ (s0.readReg64 (.gpr 0#5)) oldReq ∗ (s0.readReg64 (.gpr 0#5) ↦ₛ bs) ∗ R) hpre0
        obtain ⟨hp_al, hp_fit⟩ := hbExtractBlockFacts
          ((s0.readReg64 (.gpr 0#5) ↦ₛ bs) ∗
            MallocngEnv mallocngIface γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 C.mallocng.brkBase b ivs0 s0 ∗
            hbRoPadding C ∗ stackFrameAt s0.sp mallocngStackBytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R)
          (Satisfies.of_entails hpre2 (by sep_entail))
        refine ⟨b, staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, ?_⟩
        dsimp only [mallocngReallocTightSpec, Proofs.mallocngReallocTightSpec, ToBaseSpec.toSpec]
        simp only [ctype_simp, MallocngInitBlock, hbs_len, Nat.sub_self, memRegion_zero,
          sepConj_emp, sepConj_assoc]
        rw [pure_sepConj_of_true (by simp [hp_ne, hp_al, hp_fit])]
        exact Satisfies.of_entails hpre2 (by sep_entail)
    obtain ⟨b, _staticIvs, ivs0, hInv0, hIvsLen, hIvsSum, hpre_inner⟩ := hpre_unpacked
    refine ⟨(s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), s0.sp, oldBlk,
        s0.tpidrEl0, C.mallocng.brkBase, b, ivs0),
      hbRoPadding C ∗ memRegion (s0.sp - BitVec.ofNat 64 MallocngStackBytes) (MallocngStackBytes - 1024) ∗ R,
      hpre_inner, ?_, ?_⟩
    · intro sf hpprw hoom
      dsimp only [mallocngReallocTightSpec, Proofs.mallocngReallocTightSpec, ToBaseSpec.toSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      have hoom' : MallocngTightOomCond allocMallocng newReq b.peakCount s0 sf := by
        have h := hoom.1; rw [hok] at h; simpa [← hnew_eq] using h
      exact hbMallocngOomFalse hL hInv0 hIvsLen hIvsSum hnew_le hlc_le hblk_le hpprw hoom'
    · intro sf hpprw hkf hpost
      dsimp only [mallocngReallocTightSpec, Proofs.mallocngReallocTightSpec, ToBaseSpec.toSpec] at hpost
      rw [hok] at hpost
      simp only [↓reduceIte, ctype_simp, MallocngInitBlock, emp_sepConj, sepConj_assoc] at hpost
      rw [satisfies_pure_sepConj] at hpost; obtain ⟨hpure_all, hpost⟩ := hpost
      have hret_ne : sf.readReg64 (.gpr 0#5) ≠ 0#64 := hpure_all.2.1.2.1
      have hret_al : 16 ∣ (sf.readReg64 (.gpr 0#5)).toNat := hpure_all.2.1.2.2.1
      have hret_fit : (sf.readReg64 (.gpr 0#5)).toNat + newReq < 2 ^ 64 := hnew_eq ▸ hpure_all.2.1.2.2.2.1
      have hpres := hbStatePreserved_of_accounting hpure_all.2.2 hkf
      rw [← hnew_eq] at hpost
      have hb'_pc : (mallocngReallocBudget true oldBlk newReq b).peakCost ≤ (hbStdLimits L).maxPeakCost := by
        obtain ⟨_, _, hlc, _, hpc, _⟩ := hInv0
        simp only [mallocngReallocBudget, ↓reduceIte]
        have : max newReq VerifiedLibraries.Mallocng.MallocngMinBlockCost = mallocngBlockCost newReq := rfl
        omega
      have hb'_pb : (mallocngReallocBudget true oldBlk newReq b).peakCount ≤ (hbStdLimits L).maxPeakBlocks := by
        obtain ⟨_, _, _, hblk, _, hpb, _⟩ := hInv0
        simp only [mallocngReallocBudget, ↓reduceIte]; omega
      have hpost_sp2 := hbRewritePostEnv MallocngStackBytes
        (mallocngIface.Block γ (sf.readReg64 (.gpr 0#5)) newReq ∗
          (sf.readReg64 (.gpr 0#5) ↦ₛ ((oldBlk.map Prod.snd).getD []).take newReq) ∗
          memRegion (sf.readReg64 (.gpr 0#5) + BitVec.ofNat 64 (((oldBlk.map Prod.snd).getD []).take newReq).length)
            (newReq - (((oldBlk.map Prod.snd).getD []).take newReq).length) ∗ R)
        hInv0 hpprw rfl rfl hb'_pc hb'_pb (Satisfies.of_entails hpost (by sep_entail))
      dsimp only [hbCoreIface]; simp only [sepConj_assoc]
      rw [pure_sepConj_of_true ⟨hpres, hret_ne, hret_al, hret_fit⟩]
      rcases oldBlk with _ | ⟨oldReq, bs⟩
      · dsimp only [mallocngReallocBudget] at hpost_sp2 ⊢
        simp only [↓reduceIte, Option.map_none, Option.getD_none, List.take_nil] at hpost_sp2
        have hmc : max newReq VerifiedLibraries.Mallocng.MallocngMinBlockCost = mallocngBlockCost newReq := rfl
        rw [hInv0.2.2.1, hmc, hInv0.2.2.2.1] at hpost_sp2
        exact Satisfies.of_entails hpost_sp2 (by sep_entail)
      · dsimp only [mallocngReallocBudget] at hpost_sp2 ⊢
        simp only [↓reduceIte, Option.map_some, Option.getD_some] at hpost_sp2
        have hmc1 : max oldReq VerifiedLibraries.Mallocng.MallocngMinBlockCost = mallocngBlockCost oldReq := rfl
        have hmc2 : max newReq VerifiedLibraries.Mallocng.MallocngMinBlockCost = mallocngBlockCost newReq := rfl
        rw [hInv0.2.2.1, hmc1, hmc2, hInv0.2.2.2.1] at hpost_sp2
        exact Satisfies.of_entails hpost_sp2 (by sep_entail)

/-! ## Decidable `CodeLoaded` Check and `hbMallocngIface` -/

/-- Single-pass check that every code block of `lib` at `mpl` lies in `P`'s RX code segment. -/
def checkMultiLibInProg (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (P : Program) : Bool :=
  Obj.blocksWalk lib mpl [⟨P.base, Perm.rx, P.code, 0⟩] 0 none lib.blocks

theorem codeLoaded_of_checkMultiLibInProg {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {P : Program} (hpl : lib.Placeable mpl)
    (hchk : checkMultiLibInProg lib mpl P = true) :
    ∀ m, P.CodeLoaded m → lib.CodeLoaded mpl m := by
  intro m hcl i hi
  let dummyImg : Process.ElfImage :=
    { entry := 0#64, phdrVaddr := 0#64, phnum := 0,
      segments := [⟨P.base, Perm.rx, P.code, 0⟩], brkStart := 0#64 }
  have hmaps : Obj.ElfMaps dummyImg (mpl.base i) (lib.blocks[i].patched (lib.blockPlacement mpl i)) (· == Perm.rx) := by
    simpa [Nat.zero_add] using
      Obj.blocksWalk_sound (img := dummyImg) 0 none lib.blocks (fun _ _ _ hc => nomatch hc) hchk i hi
  have ht := (lib.placeable_blockLib hi hpl).text
  have hlen : ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length =
      (lib.blockLib i).text.code.length :=
    CodeBlock.length_patched_of_aligned _ ht.len_aligned
  refine Program.CodeLoaded.intro ?_ ?_ fun k hk => ?_
  · have h1 : 4 ∣ (lib.blockLib i).text.align := Nat.dvd_of_mod_eq_zero ht.align_pos.2
    have h2 : (lib.blockLib i).text.align ∣ (mpl.base i).toNat := Nat.dvd_of_mod_eq_zero ht.base_aligned
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 h2)
  · simp only [MultiPlacedLib.blockProgram, PlacedLib.program_base, PlacedLib.program_code, hlen]
    exact ht.no_wrap
  · simp only [MultiPlacedLib.blockProgram, PlacedLib.program_base, PlacedLib.program_code,
      lib.blockLib_text hi, MultiPlacedLib.blockPlacement] at hk ⊢
    obtain ⟨q, hcell, _⟩ := hmaps k hk
    dsimp only [dummyImg, Snapshot.cellAt, List.findSome?] at hcell
    split at hcell
    · rename_i hif
      split at hif
      · rename_i hlt
        cases hif
        injection hcell with hcell'
        injection hcell' with _hq hb
        have ha : P.base + BitVec.ofNat 64 (mpl.base i + BitVec.ofNat 64 k - P.base).toNat =
            mpl.base i + BitVec.ofNat 64 k := by
          have hno := hcl.no_wrap
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
        rw [← ha]
        exact ⟨(hcl.byte_eq _ hlt).trans hb, hcl.perm_eq _ hlt, hcl.isLazyFree_eq _ hlt⟩
      · nomatch hif
    · nomatch hcell

/-- Placement-generic `HbMallocngIface` for `hashbrown_std` under `HbMallocngPlaced`. -/
noncomputable def hbMallocngIface {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} (hpl : HbMallocngPlaced P C mpl) (hL : L ≤ HashbrownCliMaxStdin) :
    HbMallocngIface P C.mallocng (hbStdLimits L) :=
  hbMallocngIfaceImpl hpl hL

/-- Caller ticket witnessing that `(hbMallocngIface hpl hL).Heap γ` owns the startup `auxv` table. -/
noncomputable def HbAuxvTicket (γ : GhostName) (auxvAddr : BitVec 64)
    (entries : List (BitVec 64 × BitVec 64)) : SepProp :=
  ∃∗ prePairs : List (BitVec 64 × BitVec 64), ∃∗ randomAddr : BitVec 64,
  ∃∗ sufPairs : List (BitVec 64 × BitVec 64), ∃∗ sec : BitVec 64,
    ⌜entries = prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs⌝ ∗
    MallocngAuxvTicket γ auxvAddr (prePairs, randomAddr, sufPairs, 0#64, sec)

/-- Tracked startup initialization for `(hbMallocngIface hpl hL).Heap` and `HbAuxvTicket`. -/
theorem hbInitHeapTracked {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} (hpl : HbMallocngPlaced P C mpl) (hL : L ≤ HashbrownCliMaxStdin)
    {s : State} {R : SepProp} {staticIvs : List (BitVec 64 × Nat)}
    {auxvAddr randomAddr : BitVec 64} {prePairs sufPairs : List (BitVec 64 × BitVec 64)}
    {randHi8 : List (BitVec 8)} {e0 : BitVec 32}
    (hbrk : s.brk = C.mallocng.brkBase) (hbrkStart : s.brkStart = C.mallocng.brkBase)
    (hBrkWf : MallocngBrkStartWf C.mallocng.brkBase) (hStLen : staticIvs.length ≤ 3)
    (hStPhys : (staticIvs.map Prod.snd).sum ≤ 133 * 2 ^ 20 ∧
      (staticIvs.map Prod.snd).sum + hbDynPhysBudget L ≤ physPlusRw s)
    (hMapped : ∀ a : BitVec 64, (s.mem.perm a).mapped = true → MallocngInIntervals staticIvs a)
    (hSat : s.mem ⊨ (MallocngInitialBss C.mallocng ∗
             MallocngStartupInputs C.mallocng auxvAddr randomAddr prePairs sufPairs randHi8 e0 s ∗ R)) :
    ∃ (γ : GhostName) (e1 : BitVec 32),
      s.mem ⊨ ((hbMallocngIface hpl hL).Heap γ 0 0 s ∗
        HbAuxvTicket γ auxvAddr (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs) ∗
        (muslErrnoAddr s ↦₃₂ e1) ∗ R) := by
  let A := mallocngAddrsOfPlacement mpl
  unfold MallocngStartupInputs MallocngInitialBss at hSat
  rw [roTablesBytes_split hpl] at hSat
  have hAuxvEq : (auxvAddr ↦ₛ encodeAuxvBytes (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs)) =
      (auxvAddr ↦₆₄* ((prePairs ++ [(25#64, randomAddr)] ++ sufPairs ++ [(0#64, 0#64)]).flatMap
        fun (t, v) => [t, v])) := by rw [pointsToWords64_eq_flatMap_bytes]; rfl
  rw [hAuxvEq] at hSat
  have hSat1 : s.mem ⊨
      ⌜randHi8.length = 8 ∧ 0xa4 ≤ s.tpidrEl0.toNat ∧ s.tpidrEl0.toNat ≤ 2 ^ 48 ∧
        prePairs.length + sufPairs.length ≤ 64 ∧ auxvAddr.toNat % 8 = 0 ∧
        auxvAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧ randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
        (∀ e ∈ prePairs, e.1 ≠ Process.AuxvTag.null ∧ e.1 ≠ Process.AuxvTag.random) ∧
        (∀ e ∈ sufPairs, e.1 ≠ Process.AuxvTag.null ∧ e.1 ≠ Process.AuxvTag.random)⌝ ∗
      ((MallocngRoTablesAt A ∗ (C.mallocng.mallocCtxAddr ↦ₛ List.replicate 928 0#8) ∗
        (C.mallocng.mallocLockAddr ↦₃₂ 0#32) ∗ (C.mallocng.mallocReplacedAddr ↦₃₂ 0#32) ∗
        (C.mallocng.alignedAllocReplacedAddr ↦₃₂ 0#32) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
        (auxvAddr ↦₆₄* ((prePairs ++ [(25#64, randomAddr)] ++ sufPairs ++ [(0#64, 0#64)]).flatMap
          fun (t, v) => [t, v])) ∗ ((randomAddr + 8#64) ↦ₛ randHi8)) ∗
       ((C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcPageSizeAddr ↦₆₄ 4096#64) ∗
        hbRoPadding C ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ R)) :=
    Satisfies.of_entails hSat (by sep_entail)
  rw [satisfies_pure_sepConj] at hSat1
  obtain ⟨⟨hrlen, _, _, hpLen, _, hauxvHi, hrandHi, hpreOk, hsufOk⟩, hSat1⟩ := hSat1
  obtain ⟨sec, rfl⟩ := exists_unpack64_of_length_8 hrlen
  rw [← pointsTo64_eq_pointsToBytes, ← hpl.ctx_addr, ← hpl.lock_addr, ← hpl.replaced_addr,
      ← hpl.aaReplaced_addr, hpl.auxv_addr, hpl.needLocks_addr, hpl.pageSize_addr] at hSat1
  have hSat2 := Satisfies.of_bupd_frame_left
    (mallocngInitCore_tracked A C.mallocng.brkBase auxvAddr prePairs randomAddr sufPairs 0#64 sec
      hBrkWf hpreOk hsufOk hpLen hauxvHi hrandHi) hSat1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hSat2; obtain ⟨γ, hSat2⟩ := hSat2
  have hCoreEq : mallocngIface.MallocngCore γ A C.mallocng.brkBase C.mallocng.brkBase mallocngZeroBudget [] =
      mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk mallocngZeroBudget [] := by rw [hbrk]
  rw [hCoreEq] at hSat2
  have hSat3 : s.mem ⊨ ((mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk mallocngZeroBudget [] ∗
      ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64) ∗ hbRoPadding C) ∗
      MallocngAuxvTicket γ auxvAddr (prePairs, randomAddr, sufPairs, 0#64, sec)) ∗
      ((muslErrnoAddr s ↦₃₂ e0) ∗ R) := Satisfies.of_entails hSat2 (by sep_entail)
  have hInv : hbHeapInv C L mallocngZeroBudget 0 0 staticIvs [] s :=
    ⟨hbrkStart, hBrkWf, rfl, rfl, Nat.zero_le _, Nat.zero_le _, hStLen, hStPhys, fun a ha => Or.inl (hMapped a ha)⟩
  have hHeap : mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk mallocngZeroBudget [] ∗
      ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64) ∗ hbRoPadding C ⊢
      (hbMallocngIface hpl hL).Heap γ 0 0 s :=
    Entails.sepExists_right mallocngZeroBudget (Entails.sepExists_right staticIvs
      (Entails.sepExists_right [] (Entails.pure_right hInv (Entails.refl _))))
  have hTick : MallocngAuxvTicket γ auxvAddr (prePairs, randomAddr, sufPairs, 0#64, sec) ⊢
      HbAuxvTicket γ auxvAddr (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs) :=
    Entails.sepExists_right prePairs (Entails.sepExists_right randomAddr
      (Entails.sepExists_right sufPairs (Entails.sepExists_right sec (Entails.pure_right rfl (Entails.refl _)))))
  exact ⟨γ, e0, Satisfies.of_entails hSat3 (by simpa only [sepConj_assoc] using sepConj_mono_left (sepConj_mono hHeap hTick))⟩

/-- Teardown `(hbMallocngIface hpl hL).Heap` and `HbAuxvTicket` into `need_locks` and `auxv`. -/
theorem hbHeap_teardown {P : Program} {C : HbCliLayout} {mpl : Obj.MultiPlacement}
    {L : Nat} (hpl : HbMallocngPlaced P C mpl) (hL : L ≤ HashbrownCliMaxStdin)
    (γ : GhostName) (lc blk : Nat) (auxvAddr : BitVec 64)
    (entries : List (BitVec 64 × BitVec 64)) (s : State) :
    (hbMallocngIface hpl hL).Heap γ lc blk s ∗ HbAuxvTicket γ auxvAddr entries ⊢
      (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ∃∗ R_dead : SepProp, R_dead := by
  let A := mallocngAddrsOfPlacement mpl
  change hbHeap C mpl L γ lc blk s ∗ HbAuxvTicket γ auxvAddr entries ⊢ _
  unfold hbHeap HbAuxvTicket; dsimp only
  conv => lhs; simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b => Entails.sepExists_elim fun staticIvs =>
    Entails.sepExists_elim fun ivs => ?_
  conv => lhs; simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prePairs => Entails.sepExists_elim fun randomAddr =>
    Entails.sepExists_elim fun sufPairs => Entails.sepExists_elim fun sec => ?_
  refine Entails.trans (Q := ⌜entries = prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs⌝ ∗
      ((mallocngIface.MallocngCore γ A C.mallocng.brkBase s.brk b ivs ∗
        MallocngAuxvTicket γ auxvAddr (prePairs, randomAddr, sufPairs, 0#64, sec)) ∗
       (((A.libc + 3#64) ↦₈ 0#8) ∗
        ⌜hbHeapInv C L b lc blk staticIvs ivs s⌝ ∗
        ((A.libc + 48#64) ↦₆₄ 4096#64) ∗ hbRoPadding C))) (by sep_entail)
    (Entails.pure_left fun hEntries => ?_)
  subst hEntries
  refine Entails.trans (sepConj_mono_left (mallocngCore_teardown_auxv γ A C.mallocng.brkBase s.brk b ivs
    auxvAddr prePairs randomAddr sufPairs 0#64 sec)) ?_
  have hAuxvEq : (auxvAddr ↦₆₄* ((prePairs ++ [(25#64, randomAddr)] ++ sufPairs ++ [(0#64, 0#64)]).flatMap
      fun (t, v) => [t, v])) =
      (auxvAddr ↦ₛ encodeAuxvBytes (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs)) := by
    rw [pointsToWords64_eq_flatMap_bytes]; rfl
  rw [hAuxvEq, ← show C.mallocng.libcAuxvAddr = A.libc + 8#64 from hpl.auxv_addr,
      ← show C.mallocng.libcNeedLocksAddr = A.libc + 3#64 from hpl.needLocks_addr]
  conv => lhs; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun R_dead => Entails.trans
    (Q := (C.mallocng.libcNeedLocksAddr ↦₈ 0#8) ∗ (C.mallocng.libcAuxvAddr ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes (prePairs ++ [(Process.AuxvTag.random, randomAddr)] ++ sufPairs)) ∗
      (((randomAddr + 8#64) ↦₆₄ sec) ∗ R_dead ∗
        ⌜hbHeapInv C L b lc blk staticIvs ivs s⌝ ∗ ((A.libc + 48#64) ↦₆₄ 4096#64) ∗ hbRoPadding C))
    (by sep_entail)
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (Entails.sepExists_right _ (Entails.refl _)))))

end CaseStudies.Hashbrown.Proofs.StdCli
