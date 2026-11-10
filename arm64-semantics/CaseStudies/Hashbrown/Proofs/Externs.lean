/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.PlacedCode
public import Arm64.Trusted.Spec.GlobalAlloc
public import Arm64.Trusted.Spec.RustRuntime
public import ProofLib.GlobalAlloc
public import ProofLib.MallocngIface
public import ProofLib.MallocngBridge
public import ProofLib.StdStartup.MemOps
public import ProofLib.Hoare.Hooks
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.Process.Core

/-!
# Unified Allocator and Extern Subroutine Interface

Placement-generic allocator parameter `HbAlloc` (instantiated from `Arm64.Rust.GlobalAlloc` or
`ProofLib.MallocngCoreIface`) and extern subroutine contracts across the 13 blocks of
`hashbrownLib`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown

abbrev hbAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
abbrev hbAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
abbrev hbDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
abbrev hbMemsetSym : String := "memset"
abbrev hbMemmoveSym : String := "memmove"
abbrev hbPanicFmtSym : String :=
  "_RNvNtCs2kXltWtc1W_4core9panicking9panic_fmt"
abbrev hbAllocErrSym : String :=
  "_RNvNtCshlmZ2E5RoO1_5alloc5alloc18handle_alloc_error"

/-- VM, physical-memory, and thread-pointer fields preserved across CPU instructions and pure
    memory helpers (`memset`, `memmove`, `allocShim`). -/
def HbVmPreserved (s1 s2 : State) : Prop :=
  s2.brk = s1.brk ∧
  s2.brkStart = s1.brkStart ∧
  s2.physMemAvail = s1.physMemAvail ∧
  s2.tpidrEl0 = s1.tpidrEl0 ∧
  ∀ a : BitVec 64, s2.mem.perm a = s1.mem.perm a

theorem HbVmPreserved.refl (s : State) : HbVmPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem HbVmPreserved.trans {s1 s2 s3 : State}
    (h12 : HbVmPreserved s1 s2) (h23 : HbVmPreserved s2 s3) : HbVmPreserved s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, fun a => (h23.2.2.2.2 a).trans (h12.2.2.2.2 a)⟩

theorem StdStatePreserved.toHbVmPreserved {s1 s2 : State} (h : StdStatePreserved s1 s2) :
    HbVmPreserved s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.1, h.2.2.2.2.2.2.2⟩

theorem HbVmPreserved.toVmPreserved {s1 s2 : State} (h : HbVmPreserved s1 s2) :
    VmPreserved s1 s2 := by
  refine ⟨h.2.1, h.1, h.2.2.2.1, ?_⟩
  funext a
  exact h.2.2.2.2 a

/-- Unified allocator parameterization for `hashbrown` (`allowOom = True` for `GlobalAlloc`,
    `allowOom = False` with `CodeInv` for `MallocngCoreIface`). -/
structure HbAlloc where
  Heap        : Nat → Nat → State → SepProp
  Block       : BitVec 64 → Nat → Nat → SepProp
  cost        : Nat → Nat → Nat
  CanAlloc    : Nat → Nat → Nat → Nat → Prop
  stackBytes  : Nat
  allowOom    : Prop
  CodeInv     : Memory → Prop
  codeInv_keepsFrozen :
    ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2
  block_valid :
    ∀ (p : BitVec 64) (size align : Nat),
      Block p size align ⊢
        ⌜p ≠ 0#64 ∧ p.toNat % align = 0 ∧ p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align
  heap_transport :
    ∀ {lc blk : Nat} {s1 s2 : State},
      HbVmPreserved s1 s2 → Heap lc blk s1 ⊢ Heap lc blk s2

def HbAlloc.ofGlobalAlloc {P : Program} {addrs : GlobalAllocAddrs}
    (G : GlobalAlloc P addrs) : HbAlloc where
  Heap := G.Heap
  Block := G.Block
  cost sz _ := sz
  CanAlloc := G.budgetOk
  stackBytes := G.stackBytes
  allowOom := True
  CodeInv _ := True
  codeInv_keepsFrozen _ _ := trivial
  block_valid := G.block_valid
  heap_transport h := Entails.of_eq (G.heap_transport _ _ _ _ h.toVmPreserved).symm

/-- Instantiate `HbAlloc` from `ProofLib.MallocngCoreIface`, bundling the thread-local
    `muslErrnoAddr s ↦₃₂ _` slot inside `Heap`. -/
def HbAlloc.ofMallocng {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2) : HbAlloc where
  Heap lc blk s := M.Heap γ lc blk s ∗ (∃∗ e : BitVec 32, muslErrnoAddr s ↦₃₂ e)
  Block p sz al := ⌜0 < al ∧ al ∣ 16⌝ ∗ M.Block γ p sz
  cost sz _ := mallocngBlockCost sz
  CanAlloc lc blk sz al :=
    0 < al ∧ al ∣ 16 ∧ al ≤ sz ∧
    sz ≤ lim.maxReq ∧
    lc + mallocngBlockCost sz ≤ lim.maxPeakCost ∧
    blk + 1 ≤ lim.maxPeakBlocks
  stackBytes := MallocngStackBytes
  allowOom := False
  CodeInv := CodeInv
  codeInv_keepsFrozen := hCodeInv
  block_valid p sz al := by
    apply Entails.pure_left
    rintro ⟨hal_pos, hal16⟩
    refine Entails.trans (M.block_noWrap γ p sz) ?_
    apply Entails.pure_left
    rintro ⟨hne, hlt⟩
    refine Entails.trans (M.block_aligned16 γ p sz) ?_
    apply Entails.pure_left
    intro h16
    have hdvd : al ∣ p.toNat := Nat.dvd_trans hal16 h16
    have hmod : p.toNat % al = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hle : p.toNat + sz ≤ 2 ^ 64 := Nat.le_of_lt hlt
    exact Entails.pure_right ⟨hne, hmod, hle⟩ (Entails.pure_right ⟨hal_pos, hal16⟩ (Entails.refl _))
  heap_transport {lc blk s1 s2} h := by
    have herr : muslErrnoAddr s1 = muslErrnoAddr s2 := by
      simp [muslErrnoAddr, h.2.2.2.1]
    rw [herr]
    exact sepConj_mono_left (M.heap_transport h.1 h.2.1 h.2.2.1 h.2.2.2.2)

/-! ## Extern Subroutine Contracts -/

def withCodeInv {α : Type} (A : HbAlloc) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜A.CodeInv s0.mem⌝ ∗ spec.pre x s0 }

def hbAllocShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

def hbAllocSpec (A : HbAlloc) : Spec (BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (size, align, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = size ∧
      s0.readReg64 .x1 = align ∧
      LayoutOk size align ∧
      (¬ A.allowOom → A.CanAlloc lc blk size.toNat align.toNat)⌝ ∗
    A.Heap lc blk s0 ∗
    stackAt s0.sp A.stackBytes
  post := fun (size, align, lc, blk) s0 sf =>
    let ret := sf.readReg64 .x0
    ⌜AllocStatePreserved s0 sf⌝ ∗
    stackAt s0.sp A.stackBytes ∗
    (if ret = 0#64 then
       ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk size.toNat align.toNat⌝ ∗
       A.Heap lc blk sf
     else
       ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
       A.Heap (lc + A.cost size.toNat align.toNat) (blk + 1) sf ∗
       A.Block ret size.toNat align.toNat ∗
       memRegion ret size.toNat)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜A.allowOom⌝

def hbDeallocSpec (A : HbAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align, lc, blk) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      s0.readReg64 .x1 = size ∧
      s0.readReg64 .x2 = align ∧
      LayoutOk size align⌝ ∗
    A.Heap lc blk s0 ∗
    A.Block p size.toNat align.toNat ∗
    memRegion p size.toNat ∗
    stackAt s0.sp A.stackBytes
  post := fun (_, size, align, lc, blk) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    A.Heap (lc - A.cost size.toNat align.toNat) (blk - 1) sf ∗
    stackAt s0.sp A.stackBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Per-block extern dependency bundle required by `hashbrownLib` at block placement `pl` on
    `prog`. -/
structure HbExterns (prog : Program) (pl : Obj.Placement) (A : HbAlloc) : Prop where
  allocShim_ok : subroutine_ok prog (pl.ρ hbAllocShimSym) (withCodeInv A hbAllocShimSpec)
  alloc_ok     : subroutine_ok prog (pl.ρ hbAllocSym) (withCodeInv A (hbAllocSpec A))
  dealloc_ok   : subroutine_ok prog (pl.ρ hbDeallocSym) (withCodeInv A (hbDeallocSpec A))
  memset_ok    : subroutine_ok prog (pl.ρ hbMemsetSym) (withCodeInv A stdMemsetSpec)
  memmove_ok   : subroutine_ok prog (pl.ρ hbMemmoveSym) (withCodeInv A stdMemcpySpec)
  panic_hooks  : A.allowOom →
    prog.externAt? (pl.ρ hbPanicFmtSym) = some Rust.panicked ∧
    prog.externAt? (pl.ρ hbAllocErrSym) = some Rust.panicked

/-- Multi-block extern dependency bundle across all 13 blocks of `hashbrownLib`. -/
abbrev HbMultiExterns (mpl : Obj.MultiPlacement)
    (X : String → Option (State → State)) (A : HbAlloc) : Prop :=
  ∀ (i : Nat), i < 13 →
    HbExterns (hashbrownLib.blockProgram mpl i X) (hashbrownLib.blockPlacement mpl i) A

theorem HbMultiExterns.forBlock {P : HbPlaced} {X : String → Option (State → State)} {A : HbAlloc}
    (hext : HbMultiExterns P.mpl X A) (i : Nat) (hi : i < 13 := by decide) :
    HbExterns
      (((hashbrownLib.blockLib i).program (hashbrownLib.blockPlacement P.mpl i)).rebase
        (hashbrownLib.blockPlacement P.mpl i).base X)
      (hashbrownLib.blockPlacement P.mpl i) A :=
  hbBlockProg_rebase P i X ▸ hext i hi

/-! ## Extern Transfer and `GlobalAlloc` Bridge -/

theorem subroutine_ok_hbBlockDirect {α : Type} {mpl : Obj.MultiPlacement} {i : Nat} {P : Program}
    {A : HbAlloc} {targetAddr : BitVec 64} {spec : Spec α}
    (hCode : ∀ {m : Memory}, A.CodeInv m → P.CodeLoaded m)
    (hP_ext : ∀ pc, P.externAt? pc = none)
    (hP_svc : P.svc = Syscall.standard)
    (hsub : subroutine_ok P targetAddr spec) :
    subroutine_ok (hashbrownLib.blockProgram mpl i) targetAddr (withCodeInv A spec) := by
  refine subroutine_ok_of_steps_outcome fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withCodeInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hci, hpre_spec⟩
  obtain ⟨sf, hstepsP, hout⟩ :=
    subroutine_ok_elim_steps_outcome hsub x R s0 hpc hrun hpre_spec hsp (hCode hci)
  have hsteps_hb : Steps (hashbrownLib.blockProgram mpl i) s0 sf :=
    Steps.of_sameHooks
      (fun pc => by rw [hP_ext pc, MultiPlacedLib.externAt?_blockProgram_none])
      (by simp [hP_svc, MultiPlacedLib.blockProgram, PlacedLib.program])
      hstepsP
  exact ⟨sf, hsteps_hb, hout⟩

/-- Pairwise distinctness of the 7 extern stub offsets from `mpl.base i` in each block `i < 13`,
    giving `(hashbrownLib.blockProgram mpl i X).externAt? (mpl.ρ e) = X e`. -/
def HbSep (mpl : Obj.MultiPlacement) : Prop :=
  ∀ i < 13,
    ((hashbrownLib.blockLib i).text.externs.map fun e =>
      ((hashbrownLib.blockPlacement mpl i).ρ e -
       (hashbrownLib.blockPlacement mpl i).base).toNat).Nodup

theorem hbExternAt?_of_sep {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 13) (hsep : HbSep mpl)
    (X : String → Option (State → State)) {e : String}
    (he : e ∈ (hashbrownLib.blockLib i).text.externs) {f : State → State}
    (hx : X e = some f) :
    (hashbrownLib.blockProgram mpl i X).externAt?
      ((hashbrownLib.blockPlacement mpl i).ρ e) = some f := by
  unfold MultiPlacedLib.blockProgram
  rw [PlacedLib.externAt?_program (hsep i hi) he, hx]
  rfl

theorem subroutine_ok_withCodeInv_true {α : Type} {prog : Program} {entry : BitVec 64}
    {A : HbAlloc} {spec : Spec α}
    (h : subroutine_ok prog entry spec)
    (htrue : ∀ m, A.CodeInv m = True := by intro _; rfl) :
    subroutine_ok prog entry (withCodeInv A spec) := by
  refine subroutine_ok_mono_sp h (fun x s0 => ?_) (fun _ _ _ _ => Entails.refl _)
  dsimp only [withCodeInv]
  rw [htrue]
  apply Entails.pure_left
  intro _
  exact Entails.refl _

theorem hbAlloc_ok_of_globalAlloc_on {prog prog0 : Program} {addrs : GlobalAllocAddrs}
    {pl : Obj.Placement} (G : GlobalAlloc prog0 addrs)
    (hok : subroutine_ok prog addrs.alloc G.allocSpec)
    (halloc : addrs.alloc = pl.ρ hbAllocSym) :
    subroutine_ok prog (pl.ρ hbAllocSym) (hbAllocSpec (HbAlloc.ofGlobalAlloc G)) := by
  rw [← halloc]
  refine subroutine_ok_map_oom' hok (fun (size, align, lc, blk) R s0 hpre => ?_)
  dsimp only [hbAllocSpec, HbAlloc.ofGlobalAlloc, stackAt] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, _⟩, hrest⟩
  refine ⟨(size, align, s0.sp, lc, blk), R, ?_, ?_, ?_⟩
  · dsimp only [GlobalAlloc.allocSpec, globalAllocSpec]
    rw [← sepConj_assoc] at hrest
    refine Satisfies.mono (sepConj_mono_left ?_) hrest
    exact Entails.pure_right ⟨hx0, hx1, rfl, hlay⟩ (Entails.refl _)
  · intro sf hpost
    dsimp only [GlobalAlloc.allocSpec, globalAllocSpec] at hpost
    dsimp only [hbAllocSpec, HbAlloc.ofGlobalAlloc, stackAt]
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    apply Entails.pure_left
    intro hasp
    refine Entails.pure_right hasp ?_
    apply sepConj_mono_right
    split
    · apply Entails.pure_left
      intro hnbud
      exact Entails.pure_right ⟨trivial, hnbud⟩ (Entails.refl _)
    · exact Entails.refl _
  · intro sf hoom
    exact hoom

theorem hbAlloc_ok_of_globalAlloc {prog : Program} {addrs : GlobalAllocAddrs}
    {pl : Obj.Placement} (G : GlobalAlloc prog addrs)
    (halloc : addrs.alloc = pl.ρ hbAllocSym) :
    subroutine_ok prog (pl.ρ hbAllocSym) (hbAllocSpec (HbAlloc.ofGlobalAlloc G)) :=
  hbAlloc_ok_of_globalAlloc_on G G.alloc_ok halloc

theorem hbDealloc_ok_of_globalAlloc_on {prog prog0 : Program} {addrs : GlobalAllocAddrs}
    {pl : Obj.Placement} (G : GlobalAlloc prog0 addrs)
    (hok : subroutine_ok prog addrs.dealloc G.deallocSpec)
    (hdealloc : addrs.dealloc = pl.ρ hbDeallocSym) :
    subroutine_ok prog (pl.ρ hbDeallocSym) (hbDeallocSpec (HbAlloc.ofGlobalAlloc G)) := by
  rw [← hdealloc]
  refine subroutine_ok_map hok (fun (p, size, align, lc, blk) R s0 hpre => ?_)
  dsimp only [hbDeallocSpec, HbAlloc.ofGlobalAlloc, stackAt] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlay⟩, hrest⟩
  refine ⟨(p, size, align, s0.sp, lc, blk), R, ?_, ?_⟩
  · dsimp only [GlobalAlloc.deallocSpec, globalDeallocSpec]
    rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc] at hrest
    refine Satisfies.mono (sepConj_mono_left ?_) hrest
    exact Entails.pure_right ⟨hx0, hx1, hx2, rfl, hlay⟩ (Entails.of_eq (by ac_rfl))
  · intro sf hpost
    dsimp only [GlobalAlloc.deallocSpec, globalDeallocSpec] at hpost
    dsimp only [hbDeallocSpec, HbAlloc.ofGlobalAlloc, stackAt]
    exact hpost

theorem hbDealloc_ok_of_globalAlloc {prog : Program} {addrs : GlobalAllocAddrs}
    {pl : Obj.Placement} (G : GlobalAlloc prog addrs)
    (hdealloc : addrs.dealloc = pl.ρ hbDeallocSym) :
    subroutine_ok prog (pl.ρ hbDeallocSym) (hbDeallocSpec (HbAlloc.ofGlobalAlloc G)) :=
  hbDealloc_ok_of_globalAlloc_on G G.dealloc_ok hdealloc

private theorem hbBlockExterns_eq {i : Nat} (hi : i < 13) :
    (hashbrownLib.blockLib i).text.externs = (hashbrownLib.blockLib 0).text.externs := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => rfl
  | n + 13 => omega

private theorem hbBlockProgram_externAt?_eq {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < 13)
    (X : String → Option (State → State)) (pc : BitVec 64) :
    (hashbrownLib.blockProgram mpl i X).externAt? pc =
      (hashbrownLib.blockProgram mpl 0 X).externAt? pc :=
  hashbrownLib.externAt?_blockProgram_eq_of_externs_eq (hbBlockExterns_eq hi) pc

private theorem subroutine_ok_block_of_block0 {α : Type} {mpl : Obj.MultiPlacement} {i : Nat}
    (hi : i < 13) {X : String → Option (State → State)} {entry : BitVec 64} {spec : Spec α}
    (h0 : subroutine_ok (hashbrownLib.blockProgram mpl 0 X) entry spec)
    (hcl : ∀ {m : Memory}, (hashbrownLib.blockProgram mpl i X).CodeLoaded m →
      (hashbrownLib.blockProgram mpl 0 X).CodeLoaded m) :
    subroutine_ok (hashbrownLib.blockProgram mpl i X) entry spec := by
  refine subroutine_ok_of_steps_outcome fun x R s0 hpc hrun hpre hsp hcode => ?_
  obtain ⟨sf, hsteps0, hout⟩ :=
    subroutine_ok_elim_steps_outcome h0 x R s0 hpc hrun hpre hsp (hcl hcode)
  exact ⟨sf, Steps.of_sameHooks
    (fun pc => (hbBlockProgram_externAt?_eq hi X pc).symm) rfl hsteps0, hout⟩

theorem HbMultiExterns.forProg {P : HbPlaced} {X : String → Option (State → State)} {A : HbAlloc}
    {prog : Program} {pl : Obj.Placement} {i : Nat}
    (hext : HbMultiExterns P.mpl X A) (hi : i < 13)
    (hreb : prog = hashbrownLib.blockProgram P.mpl i X)
    (hpl : pl = hashbrownLib.blockPlacement P.mpl i) :
    HbExterns prog pl A := by
  rw [hreb, hpl]; exact hext i hi

theorem hbWithCodeLoaded_of_plain {α : Type} (mpl : Obj.MultiPlacement)
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (hashbrownLib.withCodeLoaded mpl spec) := by
  refine subroutine_ok_mono_entails hok (fun _ _ => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [MultiPlacedLib.withCodeLoaded]
  rw [sepConj_comm]
  exact Entails.pure_left fun _ => Entails.refl _

theorem hbExternAt?_transfer (P : HbPlaced) {i j : Nat} {prog_i prog_j : Program}
    {X : String → Option (State → State)} (hi : i < 13) (hj : j < 13)
    (hreb_i : prog_i = hashbrownLib.blockProgram P.mpl i X)
    (hreb_j : prog_j = hashbrownLib.blockProgram P.mpl j X)
    (pc : BitVec 64) :
    prog_j.externAt? pc = prog_i.externAt? pc := by
  rw [hreb_i, hreb_j, hbBlockProgram_externAt?_eq hj X pc, hbBlockProgram_externAt?_eq hi X pc]

theorem hbSubroutineOk_crossBlock {α : Type} (P : HbPlaced) {i j : Nat}
    {prog_i prog_j : Program} {X : String → Option (State → State)}
    (hi : i < 13) (hj : j < 13)
    (hreb_i : prog_i = hashbrownLib.blockProgram P.mpl i X)
    (hreb_j : prog_j = hashbrownLib.blockProgram P.mpl j X)
    {entry : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog_j entry (hashbrownLib.withCodeLoaded P.mpl spec)) :
    subroutine_ok prog_i entry (hashbrownLib.withCodeLoaded P.mpl spec) := by
  rw [hreb_j] at hcall
  exact hashbrownLib.subroutine_ok_of_block_hooks hj hcall
    (fun pc => by
      rw [hreb_i, hbBlockProgram_externAt?_eq hj X pc, hbBlockProgram_externAt?_eq hi X pc])
    (by rw [hreb_i]; rfl)

set_option maxRecDepth 200000 in
theorem HbMultiExterns.ofGlobalAlloc {mpl : Obj.MultiPlacement}
    {X : String → Option (State → State)} {addrs : GlobalAllocAddrs}
    (hsep : HbSep mpl)
    (G0 : GlobalAlloc (hashbrownLib.blockProgram mpl 0 X) addrs)
    (halloc_ok : ∀ i < 13,
      subroutine_ok (hashbrownLib.blockProgram mpl i X) (addrs.alloc) G0.allocSpec)
    (hdealloc_ok : ∀ i < 13,
      subroutine_ok (hashbrownLib.blockProgram mpl i X) (addrs.dealloc) G0.deallocSpec)
    (halloc : addrs.alloc = mpl.ρ hbAllocSym)
    (hdealloc : addrs.dealloc = mpl.ρ hbDeallocSym)
    (hshim : HookSat X hbAllocShimSym hbAllocShimSpec)
    (hmemset : HookSat X hbMemsetSym stdMemsetSpec)
    (hmemmove : HookSat X hbMemmoveSym stdMemcpySpec)
    (hpan1 : X hbPanicFmtSym = some Rust.panicked)
    (hpan2 : X hbAllocErrSym = some Rust.panicked) :
    HbMultiExterns mpl X (HbAlloc.ofGlobalAlloc G0) := by
  intro i hi
  obtain ⟨f_sh, hx_sh, hok_sh⟩ := hshim
  obtain ⟨f_ms, hx_ms, hok_ms⟩ := hmemset
  obtain ⟨f_mm, hx_mm, hok_mm⟩ := hmemmove
  have mem_ext : ∀ {e : String}, e ∈ (hashbrownLib.blockLib 0).text.externs →
      e ∈ (hashbrownLib.blockLib i).text.externs := by
    rw [hbBlockExterns_eq hi]; exact id
  have hr_al : (hashbrownLib.blockPlacement mpl i).ρ hbAllocSym = mpl.ρ hbAllocSym := rfl
  have hr_da : (hashbrownLib.blockPlacement mpl i).ρ hbDeallocSym = mpl.ρ hbDeallocSym := rfl
  exact
    { allocShim_ok := subroutine_ok_withCodeInv_true
        (subroutine_ok_of_hookOk (hbExternAt?_of_sep hi hsep X (mem_ext (by decide)) hx_sh) hok_sh)
      alloc_ok := subroutine_ok_withCodeInv_true
        (hbAlloc_ok_of_globalAlloc_on G0 (halloc_ok i hi) (halloc.trans hr_al.symm))
      dealloc_ok := subroutine_ok_withCodeInv_true
        (hbDealloc_ok_of_globalAlloc_on G0 (hdealloc_ok i hi) (hdealloc.trans hr_da.symm))
      memset_ok := subroutine_ok_withCodeInv_true
        (subroutine_ok_of_hookOk (hbExternAt?_of_sep hi hsep X (mem_ext (by decide)) hx_ms) hok_ms)
      memmove_ok := subroutine_ok_withCodeInv_true
        (subroutine_ok_of_hookOk (hbExternAt?_of_sep hi hsep X (mem_ext (by decide)) hx_mm) hok_mm)
      panic_hooks := fun _ =>
        ⟨hbExternAt?_of_sep hi hsep X (mem_ext (by decide)) hpan1,
         hbExternAt?_of_sep hi hsep X (mem_ext (by decide)) hpan2⟩ }

end CaseStudies.Hashbrown.Proofs
