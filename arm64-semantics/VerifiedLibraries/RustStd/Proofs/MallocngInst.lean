/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.SmallProbeRead

/-!
# Musl `mallocng` Instance of `RustStdAlloc OomPreserved`

Instantiates `RustStdAlloc OomPreserved` over `mallocngIface` (`mallocngRustCliAlloc` and its
interface-parametric and `extra`-extended variants) by splitting `MallocngRuntime` into
`StdErrnoCell` and `MallocngLibcCells`, and proves `StdErrnoCell` reassembly and post-`__init_libc`
initialization lemmas.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib.SepLogic VerifiedLibraries.RustStd.Io
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- The poolable, non-`errno` portion of `MallocngRuntime mAddrs tp`:
    `__libc.need_locks = 0#8` (`mAddrs.libc + 3`) and `__libc.page_size = 4096#64`
    (`mAddrs.libc + 48`). Neither cell is touched by Rust `std` I/O (`StdErrCells`). -/
def MallocngLibcCells (mAddrs : MallocngAddrs) : SepProp :=
  ((mAddrs.libc + 3#64) ↦₈ 0#8) ∗
  ((mAddrs.libc + 48#64) ↦₆₄ 4096#64)

theorem mallocngRuntime_eq_stdErrnoCell_sep (mAddrs : MallocngAddrs) (tp : BitVec 64) :
    MallocngRuntime mAddrs tp = (StdErrnoCell tp ∗ MallocngLibcCells mAddrs) :=
  rfl

/-- Interface-parametric `mallocng` pool predicate owning `J.MallocngCore` and `MallocngLibcCells`,
    leaving `StdErrnoCell` outside the pool. -/
def mallocngRustCliPoolOf (J : MallocngIface) (γ : GhostName) (mAddrs : MallocngAddrs)
    (s : State) : SepProp :=
  ∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
    J.MallocngCore γ mAddrs s.brkStart s.brk b ivs ∗ MallocngLibcCells mAddrs

def mallocngRustCliPoolWithOf (J : MallocngIface) (extra : SepProp) (γ : GhostName)
    (mAddrs : MallocngAddrs) (s : State) : SepProp :=
  mallocngRustCliPoolOf J γ mAddrs s ∗ extra

/-- Live allocation token for `mallocngRustCliAllocOf`: pairs `⌜p.toNat % al = 0 ∧ RustLayoutOk n al⌝`
    with `J.Block γ p n` so `dealloc` and `realloc` recover `RustLayoutOk` directly from `live`. -/
def mallocngRustCliLiveOf (J : MallocngIface) (γ : GhostName)
    (p : BitVec 64) (n al : Nat) : SepProp :=
  ⌜p.toNat % al = 0 ∧ RustLayoutOk n al⌝ ∗ J.Block γ p n

def mallocngRustCliAllocOf (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mAddrs : MallocngAddrs) : RustStdAlloc OomPreserved where
  pool _ _ s := mallocngRustCliPoolOf J γ mAddrs s
  live p n al := mallocngRustCliLiveOf J γ p n al
  cost n _ := n
  CanAlloc _ _ _ _ := True
  block_valid p n al := by
    refine Entails.pure_left fun ⟨hAl, hLayout⟩ => ?_
    refine Entails.trans (hIf.block_nonnull γ p n) ?_
    refine Entails.pure_left fun ⟨hpNe, _, hBound48, _⟩ => ?_
    exact Entails.pure_right ⟨hpNe, hAl, hBound48, hLayout⟩
      (Entails.pure_right ⟨hAl, hLayout⟩ (Entails.refl _))
  pool_transport _ _ s s' hPres := by
    rcases hPres with ⟨hBs, hBrk, _⟩
    simp only [mallocngRustCliPoolOf, hBs, hBrk]

def mallocngRustCliAllocWithOf (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (extra : SepProp) (γ : GhostName) (mAddrs : MallocngAddrs) : RustStdAlloc OomPreserved where
  pool _ _ s := mallocngRustCliPoolWithOf J extra γ mAddrs s
  live p n al := mallocngRustCliLiveOf J γ p n al
  cost n _ := n
  CanAlloc _ _ _ _ := True
  block_valid := (mallocngRustCliAllocOf J hIf γ mAddrs).block_valid
  pool_transport _ _ s s' hPres := by
    rcases hPres with ⟨hBs, hBrk, _⟩
    simp only [mallocngRustCliPoolWithOf, mallocngRustCliPoolOf, hBs, hBrk]

/-- `mallocng`-backed `RustStdAlloc.pool` predicate over `mallocngIface`: owns
    `mallocngIface.MallocngCore` together with `MallocngLibcCells`, leaving `StdErrnoCell`
    outside the pool. -/
def mallocngRustCliPool (γ : GhostName) (mAddrs : MallocngAddrs) (s : State) :
    SepProp :=
  ∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
    mallocngIface.MallocngCore γ mAddrs s.brkStart s.brk b ivs ∗ MallocngLibcCells mAddrs

def mallocngRustCliAlloc (γ : GhostName) (mAddrs : MallocngAddrs) :
    RustStdAlloc OomPreserved where
  pool _ _ s := mallocngRustCliPool γ mAddrs s
  live p n al := ⌜p.toNat % al = 0 ∧ RustLayoutOk n al⌝ ∗ mallocngIface.Block γ p n
  cost n _ := n
  CanAlloc _ _ _ _ := True
  block_valid p n al := by
    refine Entails.pure_left fun ⟨hAl, hLayout⟩ => ?_
    have hBlk : mallocngIface.Block γ p n ⊢
        ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
          mallocngIface.Block γ p n :=
      mallocngBlock_nonnull γ p n
    refine Entails.trans hBlk ?_
    refine Entails.pure_left fun ⟨hpNe, _, hBound48, _⟩ => ?_
    exact Entails.pure_right ⟨hpNe, hAl, hBound48, hLayout⟩
      (Entails.pure_right ⟨hAl, hLayout⟩ (Entails.refl _))
  pool_transport _ _ s s' hPres := by
    rcases hPres with ⟨hBs, hBrk, _⟩
    simp only [mallocngRustCliPool, hBs, hBrk]

theorem mallocngRustCliIfaceFacts : MallocngIfaceFacts mallocngIface where
  init                 := mallocngPlacedInit_ok
  init_resources       := mallocngInitResources_ok
  heap_split_runtime   := mallocngHeap_split_runtime
  heap_roSplit         := mallocngHeap_roSplit
  block_noRO           := mallocngBlock_noRO
  block_nonnull        := mallocngBlock_nonnull
  block_exclusive      := mallocngBlock_exclusive
  heap_footprint_bound := mallocngHeap_footprint_bound

abbrev mallocngRustCliPoolWith (extra : SepProp) (γ : GhostName)
    (mAddrs : MallocngAddrs) (s : State) : SepProp :=
  mallocngRustCliPoolWithOf mallocngIface extra γ mAddrs s

/-- `extra`-extended `mallocngIface` allocator instance. Defined directly on `mallocngIface` so
    separation-logic theorems over `mallocngRustCliAllocWith` do not pull `MallocngIfaceFacts.init`
    into their statement closure. -/
def mallocngRustCliAllocWith (extra : SepProp) (γ : GhostName)
    (mAddrs : MallocngAddrs) : RustStdAlloc OomPreserved where
  pool _ _ s := mallocngRustCliPoolWith extra γ mAddrs s
  live p n al := mallocngRustCliLiveOf mallocngIface γ p n al
  cost n _ := n
  CanAlloc _ _ _ _ := True
  block_valid := (mallocngRustCliAlloc γ mAddrs).block_valid
  pool_transport _ _ s s' hPres := by
    rcases hPres with ⟨hBs, hBrk, _⟩
    simp only [mallocngRustCliPoolWith, mallocngRustCliPoolWithOf, mallocngRustCliPoolOf, hBs, hBrk]

def mallocngRustCliHookAllocOf (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mpl : Obj.MultiPlacement) : RustStdAlloc OomPreserved :=
  mallocngRustCliAllocWithOf J hIf (VerifiedLibraries.mallocngLib.codeRO mpl)
    γ (mallocngAddrsOfPlacement mpl)

def mallocngRustCliHookAlloc (γ : GhostName) (mpl : Obj.MultiPlacement) :
    RustStdAlloc OomPreserved :=
  mallocngRustCliAllocWith (VerifiedLibraries.mallocngLib.codeRO mpl) γ (mallocngAddrsOfPlacement mpl)

theorem mallocngRustCliPool_eq_of (γ : GhostName) (mAddrs : MallocngAddrs) (s : State) :
    mallocngRustCliPool γ mAddrs s = mallocngRustCliPoolOf mallocngIface γ mAddrs s := rfl

/-! ## `StdErrnoCell` Reassembly and Post-Call Collapse -/

theorem mallocngRustCliPoolOf_sep_stdErrnoCell_eq {J : MallocngIface}
    (hIf : MallocngIfaceFacts J) (γ : GhostName) (mAddrs : MallocngAddrs)
    (lb lk : Nat) (s : State) :
    (mallocngRustCliAllocOf J hIf γ mAddrs).pool lb lk s ∗ StdErrnoCell s.tpidrEl0 =
      (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
        J.MallocngHeap γ mAddrs s.tpidrEl0 s.brkStart s.brk b ivs) := by
  change mallocngRustCliPoolOf J γ mAddrs s ∗ StdErrnoCell s.tpidrEl0 = _
  unfold mallocngRustCliPoolOf
  let E : SepProp := StdErrnoCell s.tpidrEl0
  change (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
      J.MallocngCore γ mAddrs s.brkStart s.brk b ivs ∗ MallocngLibcCells mAddrs) ∗ E = _
  rw [sepExists_sepConj_left]
  congr 1; funext b
  rw [sepExists_sepConj_left]
  congr 1; funext ivs
  rw [sepConj_assoc, sepConj_comm (MallocngLibcCells mAddrs) E]
  dsimp only [E]
  rw [← mallocngRuntime_eq_stdErrnoCell_sep mAddrs s.tpidrEl0,
      ← hIf.heap_split_runtime γ mAddrs s.tpidrEl0 s.brkStart s.brk b ivs]

theorem mallocngRustCliPool_sep_stdErrnoCell_eq
    (γ : GhostName) (mAddrs : MallocngAddrs) (lb lk : Nat) (s : State) :
    (mallocngRustCliAlloc γ mAddrs).pool lb lk s ∗ StdErrnoCell s.tpidrEl0 =
      (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
        mallocngIface.MallocngHeap γ mAddrs s.tpidrEl0 s.brkStart s.brk b ivs) :=
  mallocngRustCliPoolOf_sep_stdErrnoCell_eq mallocngRustCliIfaceFacts γ mAddrs lb lk s

theorem mallocngRustCliPool_sep_stdErrCells_eq
    (γ : GhostName) (mAddrs : MallocngAddrs) (ioAddrs : RustStdIoAddrs)
    (lb lk : Nat) (s : State) :
    (mallocngRustCliAlloc γ mAddrs).pool lb lk s ∗ StdErrCells ioAddrs s.tpidrEl0 =
      (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
        mallocngIface.MallocngHeap γ mAddrs s.tpidrEl0 s.brkStart s.brk b ivs) ∗
      StdOsErrCells ioAddrs := by
  rw [stdErrCells_eq ioAddrs s.tpidrEl0, ← sepConj_assoc,
      mallocngRustCliPool_sep_stdErrnoCell_eq γ mAddrs lb lk s]

theorem mallocngRustCliPoolWithOf_sep_stdErrnoCell_eq {J : MallocngIface}
    (hIf : MallocngIfaceFacts J) (extra : SepProp) (γ : GhostName) (mAddrs : MallocngAddrs)
    (lb lk : Nat) (s : State) :
    (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb lk s ∗ StdErrnoCell s.tpidrEl0 =
      (∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
        J.MallocngHeap γ mAddrs s.tpidrEl0 s.brkStart s.brk b ivs) ∗ extra := by
  change (mallocngRustCliPoolOf J γ mAddrs s ∗ extra) ∗ StdErrnoCell s.tpidrEl0 = _
  rw [sepConj_assoc, sepConj_comm extra (StdErrnoCell s.tpidrEl0), ← sepConj_assoc]
  rw [← mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ mAddrs lb lk s]
  rfl

theorem postEnv_withExtra_entails_errno_pool {J : MallocngIface}
    (hIf : MallocngIfaceFacts J) (extra : SepProp) (γ : GhostName) (mAddrs : MallocngAddrs)
    (bf : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (lb' lk' : Nat) (s0 s_call sf : State) :
    MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart bf ivs0 s_call sf ∗ extra ⊢
      StdErrnoCell s0.tpidrEl0 ∗
        (mallocngRustCliAllocWithOf J hIf extra γ mAddrs).pool lb' lk' sf := by
  have hp :
      MallocngPostEnv J γ mAddrs s0.tpidrEl0 s0.brkStart bf ivs0 s_call sf ⊢
        (mallocngRustCliAllocOf J hIf γ mAddrs).pool lb' lk' sf ∗ StdErrnoCell s0.tpidrEl0 := by
    unfold MallocngPostEnv MallocngEnv
    refine Entails.sepExists_elim fun ivsf => ?_
    refine Entails.pure_left fun _ => ?_
    refine Entails.pure_left fun ⟨htp, hbs⟩ => ?_
    rw [← htp, mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ mAddrs lb' lk' sf, hbs]
    exact Entails.sepExists_right bf (Entails.sepExists_right ivsf (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hp) ?_
  change ((mallocngRustCliPoolOf J γ mAddrs sf ∗ StdErrnoCell s0.tpidrEl0) ∗ extra) ⊢
    StdErrnoCell s0.tpidrEl0 ∗ (mallocngRustCliPoolOf J γ mAddrs sf ∗ extra)
  exact Entails.of_eq (by
    rw [sepConj_comm (mallocngRustCliPoolOf J γ mAddrs sf) (StdErrnoCell s0.tpidrEl0),
        sepConj_assoc])

/-! ## Stripping `extra := emp` -/

private theorem pool_with_emp_eq (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mAddrs : MallocngAddrs) (lb lk : Nat) (s : State) :
    (mallocngRustCliAllocWithOf J hIf emp γ mAddrs).pool lb lk s =
      (mallocngRustCliAllocOf J hIf γ mAddrs).pool lb lk s := by
  change mallocngRustCliPoolOf J γ mAddrs s ∗ emp = mallocngRustCliPoolOf J γ mAddrs s
  exact sepConj_emp _

theorem rustStdAllocSpec_with_emp_eq (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mAddrs : MallocngAddrs) :
    rustStdAllocSpec (mallocngRustCliAllocWithOf J hIf emp γ mAddrs) =
      rustStdAllocSpec (mallocngRustCliAllocOf J hIf γ mAddrs) := by
  unfold rustStdAllocSpec
  congr 1
  · funext ⟨size, align, lb, lk⟩ s
    simp only [pool_with_emp_eq]; rfl
  · funext ⟨size, align, lb, lk⟩ s0 sf
    simp only [pool_with_emp_eq]; rfl

theorem rustStdDeallocSpec_with_emp_eq (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mAddrs : MallocngAddrs) :
    rustStdDeallocSpec (mallocngRustCliAllocWithOf J hIf emp γ mAddrs) =
      rustStdDeallocSpec (mallocngRustCliAllocOf J hIf γ mAddrs) := by
  unfold rustStdDeallocSpec
  congr 1
  · funext ⟨p, size, align, lb, lk⟩ s
    simp only [pool_with_emp_eq]; rfl
  · funext ⟨p, size, align, lb, lk⟩ s0 sf
    simp only [pool_with_emp_eq]; rfl

theorem rustStdReallocSpec_with_emp_eq (J : MallocngIface) (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (mAddrs : MallocngAddrs) :
    rustStdReallocSpec (mallocngRustCliAllocWithOf J hIf emp γ mAddrs) =
      rustStdReallocSpec (mallocngRustCliAllocOf J hIf γ mAddrs) := by
  unfold rustStdReallocSpec
  congr 1
  · funext ⟨p, old, align, new, bs, lb, lk⟩ s
    simp only [pool_with_emp_eq]; rfl
  · funext ⟨p, old, align, new, bs, lb, lk⟩ s0 sf
    simp only [pool_with_emp_eq]; rfl

theorem rustStdAllocEntries_of_with_emp {J : MallocngIface} {hIf : MallocngIfaceFacts J}
    {γ : GhostName} {mAddrs : MallocngAddrs} {P : Program} {addrs : RustStdAllocAddrs}
    (h : RustStdAllocEntries (mallocngRustCliAllocWithOf J hIf emp γ mAddrs) P addrs) :
    RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ mAddrs) P addrs where
  alloc := rustStdAllocSpec_with_emp_eq J hIf γ mAddrs ▸ h.alloc
  dealloc := rustStdDeallocSpec_with_emp_eq J hIf γ mAddrs ▸ h.dealloc
  realloc := rustStdReallocSpec_with_emp_eq J hIf γ mAddrs ▸ h.realloc

/-! ## Post-`__init_libc` Startup Initialization -/

theorem mallocngRustCliPoolOf_of_init_resources {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (mAddrs : MallocngAddrs) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hmem : s0.mem ⊨ MallocngStartupResources mAddrs s0.tpidrEl0 ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        ((mallocngRustCliAllocOf J hIf γ mAddrs).pool 0 0 s0 ∗ StdErrnoCell s0.tpidrEl0) ∗ R := by
  have hbupd := Satisfies.mono
    (sepConj_mono_left (hIf.init_resources mAddrs s0.tpidrEl0 s0.brkStart htpLo htpHi hbrkWf)) hmem
  have hbupd2 := Satisfies.mono (bupd_frame_r _ _) hbupd
  rw [satisfies_bupd] at hbupd2
  rw [sepExists_sepConj_left, satisfies_sepExists] at hbupd2
  obtain ⟨γ, hγ⟩ := hbupd2
  refine ⟨γ, ?_⟩
  rw [mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ mAddrs 0 0 s0]
  refine Satisfies.mono (sepConj_mono_left ?_) hγ
  rw [hbrk]
  exact Entails.sepExists_right mallocngZeroBudget (Entails.sepExists_right [] (Entails.refl _))

theorem mallocngRustCliPool_of_init_resources
    (mAddrs : MallocngAddrs) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hmem : s0.mem ⊨ MallocngStartupResources mAddrs s0.tpidrEl0 ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        ((mallocngRustCliAlloc γ mAddrs).pool 0 0 s0 ∗ StdErrnoCell s0.tpidrEl0) ∗ R :=
  mallocngRustCliPoolOf_of_init_resources mallocngRustCliIfaceFacts mAddrs R s0 htpLo htpHi hbrkWf hbrk hmem

theorem mallocngRustCliPoolOf_of_init {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (mpl : Obj.MultiPlacement) (auxvPtr : BitVec 64) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        ((mallocngRustCliAllocOf J hIf γ (mallocngAddrsOfPlacement mpl)).pool 0 0 s0 ∗
          StdErrnoCell s0.tpidrEl0) ∗ R := by
  obtain ⟨γ, hbupd⟩ :=
    hIf.init mpl s0.tpidrEl0 s0.brkStart auxvPtr R s0.mem htpLo htpHi hbrkWf hmem
  rw [satisfies_bupd] at hbupd
  refine ⟨γ, ?_⟩
  rw [mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ (mallocngAddrsOfPlacement mpl) 0 0 s0, hbrk]
  exact Satisfies.mono
    (sepConj_mono_left
      (Entails.sepExists_right mallocngZeroBudget (Entails.sepExists_right [] (Entails.refl _))))
    hbupd

theorem mallocngRustCliPool_of_init
    (mpl : Obj.MultiPlacement) (auxvPtr : BitVec 64) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      s0.mem ⊨
        ((mallocngRustCliAlloc γ (mallocngAddrsOfPlacement mpl)).pool 0 0 s0 ∗
          StdErrnoCell s0.tpidrEl0) ∗ R :=
  mallocngRustCliPoolOf_of_init mallocngRustCliIfaceFacts mpl auxvPtr R s0 htpLo htpHi hbrkWf hbrk hmem

end VerifiedLibraries.RustStd
