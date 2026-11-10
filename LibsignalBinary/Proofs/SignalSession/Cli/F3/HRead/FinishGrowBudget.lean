/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public meta import ProofLib.ProgramReflection

/-!
# Budget-Threaded `<alloc::raw_vec::RawVecInner>::finish_grow`

Verifies `signalSessionIoMultiLib` block 4 (`finish_grow`, `168` B / `42` insns, `0x20`-byte stack
frame, specialized to `elem_size = 1, elem_align = 1`) over any `RustCliAllocBudget M` and
`BudgetLimits`, together with `cliIoVecBuf` representation and doubling-schedule event helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8 vecU8At)
open CryptoVerification.SignalSession.Cli (ioVecAt)
open VerifiedLibraries.RustStd (
  SameCpuState vecHeader nonSyscallPreserved_toVmFields
  cells cells_zero cells_succ stackAt_split_cells
)
open VerifiedLibraries.RustStd.Io (SameCpuOracleState)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEvents
  NullAllowed OomPreserved PoolPreserved RustCliAllocBudget RustLayoutOk
  VmMemPreserved VmPreserved
  rustAllocEvents rustDeallocEvents rustReallocEvents
  rustCliAllocBudgetSpecBase rustCliReallocBudgetSpecBase
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (cliIoCap cliIoCapIdx cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoWithCodeLoaded subroutine_ok_of_cliIoWithCodeLoaded
  cliIoResolve_eq_base sepWP_seg_cliIo_block_pure
  cliIoBlocks_len cliIoFinishGrowSym cliIoFinishGrow_lookup
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustNoAllocShimSym
  cliIoLib04 cliIoPl04 cliIoPC04 cliIoBlockNoSvc0_04
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  vecHeader_to_err_sret take_append_drop_take chunk_take_self
)

/-! ## `VmPreserved`, `AllocCallPreserved`, and `OomPreserved` Helpers -/

theorem allocCallPreserved_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem oomPreserved_of_allocCallPreserved {s0 sm sf : State}
    (hacp : AllocCallPreserved s0 sm) (hoom : OomPreserved sm sf) :
    OomPreserved s0 sf :=
  ⟨hoom.1.trans hacp.1, hoom.2.1.trans hacp.2.1, hoom.2.2.trans hacp.2.2.1⟩

/-- Pure-segment state-preservation helper for `sepWP_seg_cliIo_block_pure`, producing both
    `LibsignalBinary.Heap.AllocCallPreserved` and `LibsignalBinary.Heap.VmPreserved` so
    `RustCliAllocBudget.pool` transports across every pure `signalSessionIoMultiLib` segment. -/
theorem vmPreserved_of_seg {s s' sm' sm : State}
    (h_in : SameCpuOracleState s' s) (h_out : SameCpuOracleState sm sm')
    (hnsp : ProofLib.NonSyscallPreserved s sm) (hsym : sm.symtab = s.symtab)
    (htp : sm'.tpidrEl0 = s'.tpidrEl0)
    (hsig : sm'.sigActions = s'.sigActions)
    (horc : sm'.oracle = s'.oracle) :
    AllocCallPreserved s sm ∧ VmPreserved s sm := by
  have ⟨hacp_rs, _⟩ :=
    VerifiedLibraries.RustStd.Io.allocCallPreserved_of_seg h_in h_out hnsp hsym htp hsig horc
  have hacp : AllocCallPreserved s sm :=
    ⟨hacp_rs.1, hacp_rs.2.1, hacp_rs.2.2.1, hacp_rs.2.2.2.1,
     hacp_rs.2.2.2.2.1, hacp_rs.2.2.2.2.2.1, hacp_rs.2.2.2.2.2.2⟩
  exact ⟨hacp,
    VmPreserved.of_vm_tpidr (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields hnsp)
      hacp.2.2.2.1 (FdsHiFrame.of_fs_eq hacp.1)⟩

/-- Non-VM syscall preservation (`read`, `openat`, `close`) implies `VmMemPreserved`
    (and `VmPreserved` when `FdsHiFrame s0 sf` also holds, e.g. `read` on `fd = 0`). -/
theorem vmMemPreserved_of_syscallPreserved {s0 sf : State} (h : SyscallPreserved s0 sf) :
    VmMemPreserved s0 sf :=
  VmMemPreserved.of_vm_tpidr h.2.2 h.1

theorem vmPreserved_of_syscallPreserved_fds {s0 sf : State}
    (h : SyscallPreserved s0 sf) (hfds : FdsHiFrame s0 sf) :
    VmPreserved s0 sf :=
  VmPreserved.of_vm_tpidr h.2.2 h.1 hfds

/-! ## `cliIoVecBuf` Representation and `vecU8` / `ioVecAt` Bridges -/

/-- Heap backing buffer of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs` (`align = 1`)
    over any `R_alloc : CryptoVerification.RustHeap.RustAlloc` (in particular `A.repAlloc`). -/
def cliIoVecBuf (R_alloc : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else R_alloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem cliIoVecBuf_bounds {R_alloc : RustAlloc} {m : Memory}
    {cap ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (hm : m ⊨ cliIoVecBuf R_alloc cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := by
  unfold cliIoVecBuf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

theorem vecHeader_cliIoVecBuf_eq_vecU8At (R_alloc : RustAlloc)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ cliIoVecBuf R_alloc cap ptr bs =
      vecU8At R_alloc v cap ptr bs := by
  unfold vecHeader cliIoVecBuf vecU8At CryptoVerification.RustHeap.vecHeader
  simp only [show (0 : BitVec 64) = 0#64 from rfl]

theorem vecHeader_cliIoVecBuf_entails_vecU8 (R_alloc : RustAlloc)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ cliIoVecBuf R_alloc cap ptr bs ⊢
      vecU8 R_alloc v bs := by
  rw [vecHeader_cliIoVecBuf_eq_vecU8At]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecHeader_cliIoVecBuf_entails_ioVecAt_ok (R_alloc : RustAlloc)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ cliIoVecBuf R_alloc cap ptr bs ⊢
      ioVecAt R_alloc v (.ok bs) :=
  vecHeader_cliIoVecBuf_entails_vecU8 R_alloc v cap ptr bs

theorem vecHeader_to_ioVecAt_err (R_alloc : RustAlloc) (sret p l : BitVec 64) :
    vecHeader sret 0xFFFFFFFFFFFFFFFF#64 p l ⊢ ioVecAt R_alloc sret (.error ()) :=
  vecHeader_to_err_sret sret p l

theorem cliIoVecBuf_zero_intro (R_alloc : RustAlloc) {ptr : BitVec 64} (hptr : ptr ≠ 0#64) :
    emp ⊢ cliIoVecBuf R_alloc 0#64 ptr [] := by
  unfold cliIoVecBuf
  have hlt : (0#64 : BitVec 64).toNat < 2 ^ 63 := by decide
  rw [pure_sepConj_of_true ⟨Nat.le_refl 0, hlt, hptr⟩]
  simp only [↓reduceIte]
  exact Entails.refl emp

/-- Forget `bs` inside a positive-capacity `cliIoVecBuf` into
    `R_alloc.live ptr cap 1 ∗ memRegion ptr cap` for `__rust_dealloc`. -/
theorem cliIoVecBuf_entails_dealloc_mem (R_alloc : RustAlloc)
    {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (_hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    cliIoVecBuf R_alloc (BitVec.ofNat 64 cap) ptr bs ⊢ R_alloc.live ptr cap 1 ∗ memRegion ptr cap := by
  have hlt64 : cap < 2 ^ 64 := Nat.lt_trans hlt (by decide)
  have hto : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : BitVec.ofNat 64 cap ≠ 0#64 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [hto] at this
    simp at this
    omega
  unfold cliIoVecBuf
  simp only [hto, hne, ↓reduceIte]
  refine Entails.pure_left fun ⟨hbs_le, _, _⟩ => ?_
  refine sepConj_mono_right ?_
  rw [memRegion_split_le ptr bs.length cap hbs_le (Nat.le_of_lt hlt64)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem cliIoVecBuf_unpack_pos (R_alloc : RustAlloc)
    {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)}
    (hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    cliIoVecBuf R_alloc (BitVec.ofNat 64 cap) ptr bs =
      (⌜bs.length ≤ cap ∧ cap < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (R_alloc.live ptr cap 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length))) := by
  have hlt64 : cap < 2 ^ 64 := Nat.lt_trans hlt (by decide)
  have hto : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne : BitVec.ofNat 64 cap ≠ 0#64 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [hto] at this
    simp at this
    omega
  unfold cliIoVecBuf
  simp only [hto, hne, ↓reduceIte]

/-- Repack `cliIoVecBuf` after `memcpy(ptr + len, sp, chunk)` appends `chunk = (rem.drop len).take want`. -/
theorem cliIoVecBuf_repack_chunk (R_alloc : RustAlloc)
    {cap len want : Nat} {ptr : BitVec 64} {rem chunk : List (BitVec 8)}
    (hpos : 0 < cap) (hlt : cap < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hchunk : chunk = (rem.drop len).take want) :
    R_alloc.live ptr cap 1 ∗
      (ptr ↦ₛ rem.take len) ∗
      ((ptr + BitVec.ofNat 64 len) ↦ₛ chunk) ∗
      memRegion (ptr + BitVec.ofNat 64 (len + chunk.length)) (cap - (len + chunk.length)) ⊢
    cliIoVecBuf R_alloc (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) := by
  have happ : rem.take len ++ chunk = rem.take (len + chunk.length) := by
    rw [hchunk]
    conv => lhs; arg 2; rw [chunk_take_self (rem.drop len) want]
    rw [← hchunk]
    exact take_append_drop_take rem len chunk.length
  have htake_len : (rem.take len).length = len := List.length_take_of_le (by omega)
  have htake_len' : (rem.take (len + chunk.length)).length = len + chunk.length :=
    List.length_take_of_le hlen_r
  rw [cliIoVecBuf_unpack_pos R_alloc hpos hlt,
    pure_sepConj_of_true ⟨by rw [htake_len']; exact hlen_cap, hlt, hptr⟩,
    htake_len', ← happ,
    pointsToBytes_append ptr (rem.take len) chunk, htake_len]
  sep_entail

/-! ## Doubling Schedule `cliIoCapsEvents` Telescoping Helpers -/

/-- Final capacity reached after walking `cs` starting from `prev`. -/
def lastCapOr : Nat → List Nat → Nat
  | prev, [] => prev
  | _, c :: cs => lastCapOr c cs

theorem cliIoCapsEvents_append :
    ∀ (prev : Nat) (cs₁ cs₂ : List Nat),
      cliIoCapsEvents prev (cs₁ ++ cs₂) =
        cliIoCapsEvents prev cs₁ ++ cliIoCapsEvents (lastCapOr prev cs₁) cs₂
  | 0, [], cs₂ => by simp [cliIoCapsEvents, lastCapOr]
  | _ + 1, [], cs₂ => by simp [cliIoCapsEvents, lastCapOr]
  | 0, c :: cs, cs₂ => by
    simp only [List.cons_append, cliIoCapsEvents, lastCapOr,
      cliIoCapsEvents_append c cs cs₂, List.append_assoc]
  | prev + 1, c :: cs, cs₂ => by
    simp only [List.cons_append, cliIoCapsEvents, lastCapOr,
      cliIoCapsEvents_append c cs cs₂, List.append_assoc]

theorem lastCapOr_append :
    ∀ (prev : Nat) (cs₁ cs₂ : List Nat),
      lastCapOr prev (cs₁ ++ cs₂) = lastCapOr (lastCapOr prev cs₁) cs₂
  | _, [], _ => rfl
  | _, c :: cs, cs₂ => lastCapOr_append c cs cs₂

theorem lastCapOr_range_cliIoCap :
    ∀ (j prev : Nat), lastCapOr prev ((List.range (j + 1)).map cliIoCap) = cliIoCap j
  | 0, _ => rfl
  | j + 1, prev => by
    rw [List.range_succ, List.map_append, lastCapOr_append]
    rfl

theorem cliIoCapsEvents_range_zero :
    cliIoCapsEvents 0 ((List.range 1).map cliIoCap) = rustAllocEvents (cliIoCap 0) 1 := by
  simp [cliIoCapsEvents]

theorem cliIoCapsEvents_range_succ (j : Nat) :
    cliIoCapsEvents 0 ((List.range (j + 2)).map cliIoCap) =
      cliIoCapsEvents 0 ((List.range (j + 1)).map cliIoCap) ++
        rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1 := by
  rw [show j + 2 = (j + 1) + 1 by omega, List.range_succ, List.map_append,
    cliIoCapsEvents_append, lastCapOr_range_cliIoCap]
  have hpos : 0 < cliIoCap j := by
    unfold cliIoCap
    have : 0 < 2 ^ j := Nat.two_pow_pos j
    omega
  obtain ⟨p, hp⟩ : ∃ p, cliIoCap j = p + 1 := ⟨cliIoCap j - 1, by omega⟩
  rw [hp]
  simp [cliIoCapsEvents]

theorem rustAllocEvents_one_pos {c : Nat} (hc : 0 < c) :
    rustAllocEvents c 1 = [.alloc c] := by
  unfold rustAllocEvents
  have h : 1 ≤ 16 ∧ 1 ≤ c := ⟨by decide, hc⟩
  simp [h]

theorem rustReallocEvents_one_pos {old c : Nat} (hc : 0 < c) :
    rustReallocEvents old c 1 = [.realloc 1 old c] := by
  unfold rustReallocEvents
  have h : 1 ≤ 16 ∧ 1 ≤ c := ⟨by decide, hc⟩
  simp [h]

/-! ## Budget-Threaded `<alloc::raw_vec::RawVecInner>::finish_grow` -/

/-- Deterministic `AllocEvent` list emitted by `finish_grow(oldCap, newCap)` (`elem_size = 1`,
    `elem_align = 1`) on a non-null return:
    `rustAllocEvents newCap 1` when `oldCap = 0#64`, else `rustReallocEvents oldCap.toNat newCap 1`. -/
def cliIoFinishGrowBudgetEvents (oldCap : BitVec 64) (newCap : Nat) : List AllocEvent :=
  if oldCap = 0#64 then rustAllocEvents newCap 1
  else rustReallocEvents oldCap.toNat newCap 1

/-- Budget-threaded Hoare contract for `signalSessionIoMultiLib` block `4`
    (`<alloc::raw_vec::RawVecInner>::finish_grow`, `elem_size = 1, elem_align = 1`) over any
    `(M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)`.
    Ghost: `(outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st)`. -/
def cliIoFinishGrowBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
      BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × M.σ) where
  pre := fun (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧
      s0.readReg64 .x1 = oldCap ∧
      s0.readReg64 .x2 = oldPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 newCap ∧
      0 < newCap ∧ newCap < 2 ^ 64 ∧
      bs.length ≤ newCap⌝ ∗
    (stackAt s0.sp (32 + allocHookStack) ∗
      vecHeader outPtr v0 v1 v2 ∗
      cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
      A.pool lim st s0)
  post := fun (outPtr, _, _, _, oldCap, oldPtr, bs, newCap, st) s0 sf =>
    ∃∗ isErr : Bool, ∃∗ newPtr : BitVec 64, ∃∗ errW1 : BitVec 64, ∃∗ errW2 : BitVec 64,
      ⌜AllocCallPreserved s0 sf⌝ ∗
      (stackAt s0.sp (32 + allocHookStack) ∗
        (if isErr then
          ⌜NullAllowed newCap 1⌝ ∗
          vecHeader outPtr 1#64 errW1 errW2 ∗
          cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
          A.pool lim st sf
        else
          ⌜newCap < 2 ^ 63⌝ ∗
          vecHeader outPtr 0#64 newPtr (BitVec.ofNat 64 newCap) ∗
          cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) sf))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, _, _, _, oldCap, _, _, newCap, st) s0 sf =>
    ⌜newCap < 2 ^ 63 ∧
      ¬ FitsEvents M lim st (cliIoFinishGrowBudgetEvents oldCap newCap) ∧
      OomPreserved s0 sf⌝

section
arm64_proof_prelude

private abbrev cliIoFinishGrowSavedSlots (s0 : State) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem cliIoFinishGrow_stack_split (sp : BitVec 64) :
    stackAt sp (32 + allocHookStack) =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3,
        stackAt (sp - 32#64) allocHookStack ∗
        (((sp - 32#64) ↦₆₄ st0) ∗ ((sp - 24#64) ↦₆₄ st1) ∗
          ((sp - 16#64) ↦₆₄ st2) ∗ ((sp - 8#64) ↦₆₄ st3)) := by
  rw [show 32 + allocHookStack = allocHookStack + 8 * 4 by decide,
    stackAt_split_cells sp allocHookStack 4 (by decide)]
  simp only [Nat.reduceMul, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, ProofLib.stackAt, allocHookStack]
  simp only [bv_lin_norm]

private theorem cliIoFinishGrow_stack_refold (sp : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      stackAt sp (32 + allocHookStack) := by
  rw [cliIoFinishGrow_stack_split sp]
  exact Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <| Entails.refl _

/-- Callee-saved GPRs `x21..x28` untouched by `finish_grow`. -/
private def GrowHighGprs (s0 s1 : State) : Prop :=
  s1.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s1.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)

private theorem GrowHighGprs.trans {s0 s1 s2 : State}
    (h01 : GrowHighGprs s0 s1) (h12 : GrowHighGprs s1 s2) :
    GrowHighGprs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem GrowHighGprs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    GrowHighGprs s0 s1 :=
  ⟨h.readReg64_x21, h.readReg64_x22, h.readReg64_x23, h.readReg64_x24,
   h.readReg64_x25, h.readReg64_x26, h.readReg64_x27, h.readReg64_x28⟩

private theorem cliIo4_lt : 4 < signalSessionIoMultiLib.blocks.length := by
  rw [cliIoBlocks_len]; decide

private theorem cliIoFinishGrow_realloc_pc [CliIoPlacement] :
    cliIoPl04.base + 40#64 + (cliIoPl04.ρ cliIoRustReallocSym - cliIoPl04.base - 40#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym := by
  change cliIoPl04.base + 40#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym - cliIoPl04.base - 40#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustReallocSym
  bv_lin

private theorem cliIoFinishGrow_shim_pc [CliIoPlacement] :
    cliIoPl04.base + 84#64 + (cliIoPl04.ρ cliIoRustNoAllocShimSym - cliIoPl04.base - 84#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym := by
  change cliIoPl04.base + 84#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym - cliIoPl04.base - 84#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustNoAllocShimSym
  bv_lin

private theorem cliIoFinishGrow_alloc_pc [CliIoPlacement] :
    cliIoPl04.base + 96#64 + (cliIoPl04.ρ cliIoRustAllocSym - cliIoPl04.base - 96#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym := by
  change cliIoPl04.base + 96#64 +
    (signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym - cliIoPl04.base - 96#64) =
    signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoRustAllocSym
  bv_lin

private theorem rustLayoutOk_one {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩

private theorem bit63_eq_zero_of_lt {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem bit63_eq_one_of_ge {n : Nat} (hge : 2 ^ 63 ≤ n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).getLsbD 63 = true := by
  have hd : n / 2 ^ 63 = 1 := by omega
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

/-- Shared null-return error epilogue of `finish_grow` at `cliIoPl04.base + 104#64` (`+0x68 .. +0x84`). -/
private theorem cliIoFinishGrow_epilogue_err [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 104#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnull : NullAllowed newCap 1)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 32#64) allocHookStack ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef : A.pool lim st se = A.pool lim st sf :=
    (A.pool_transport lim st se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithCodeLoaded, cliIoFinishGrowBudgetSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right true <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 1#64 <|
      Entails.sepExists_right (BitVec.ofNat 64 newCap) <| Entails.refl _)
  simp only [↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  rw [pure_sepConj_of_true hnull]
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

/-- Shared success epilogue of `finish_grow` at `cliIoPl04.base + 140#64` (`+0x8c .. +0xa4`). -/
private theorem cliIoFinishGrow_epilogue_ok [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr newPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 140#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx0 : se.readReg64 .x0 = newPtr)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnew_lt63 : newCap < 2 ^ 63)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 32#64) allocHookStack ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
        A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = newPtr := (hcpu_e.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef :
      A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se =
      A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) sf :=
    (A.pool_transport lim _ se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithCodeLoaded, cliIoFinishGrowBudgetSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right false <|
      Entails.sepExists_right newPtr <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 0#64 <| Entails.refl _)
  simp only [Bool.false_eq_true, ↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  refine Entails.trans ?_
    (sepConj_mono_right
      (by rw [pure_sepConj_of_true hnew_lt63]; exact Entails.refl _))
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

set_option maxHeartbeats 800000 in
set_option linter.style.haveILetI false in
/-- Placement-generic, cost-model-polymorphic proof of `signal_session_io`'s crate-local
    `<alloc::raw_vec::RawVecInner>::finish_grow` (`signalSessionIoMultiLib` block `4`,
    `168` B / `42` insns) given `hshim` (`rustAllocShimVmSpec`),
    `halloc` (`rustCliAllocBudgetSpecBase M A lim false`), and
    `hrealloc` (`rustCliReallocBudgetSpecBase M A lim`). -/
theorem cliIoFinishGrow_budget_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (cliIoWithCodeLoaded mpl (cliIoFinishGrowBudgetSpec M A lim)) := by
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 4 cliIoFinishGrowSym cliIo4_lt cliIoFinishGrow_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [cliIoWithCodeLoaded, MultiPlacedLib.withCodeLoaded, cliIoFinishGrowBudgetSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le_new⟩, hmem⟩
  have ⟨hbs_le_old, hold_lt, holdPtr_ne⟩ :
      bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64 :=
    cliIoVecBuf_bounds (m := s0.mem)
      (R := stackAt s0.sp (32 + allocHookStack) ∗ vecHeader outPtr v0 v1 v2 ∗
        A.pool lim st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  wp_conv_pre =>
    rw [cliIoFinishGrow_stack_split s0.sp]
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 => ?_
  by_cases hge63 : 2 ^ 63 ≤ newCap
  · -- `2 ^ 63 ≤ newCap < 2 ^ 64`: `tbnz x3, #63, 0x34` returns `CapacityOverflow`
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = true :=
      bit63_eq_one_of_ge hge63 hnew_lt64
    have hnull : NullAllowed newCap 1 := by unfold NullAllowed; omega
    apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
      (mid := s0.readReg64 .lr)
    intro s1' hcpu1_0
    have hcpu1 := hcpu1_0.1
    change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
      fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
    have hcpu_f := hcpu_f0.1
    have ⟨hacp_0f, hvm_0f⟩ :=
      vmPreserved_of_seg hcpu1_0 hcpu_f0 hnsp_f hsym_f
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0f : A.pool lim st s0 = A.pool lim st sf :=
      (A.pool_transport lim st s0 sf hvm_0f).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun1'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · exact hcpu_f.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    refine SepWP.done hpc_f hrun_f
      ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
    have hstk_back := cliIoFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right true <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right v2 <| Entails.refl _)
    simp only [↓reduceIte, hsp1_in, hpool_eq_0f, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true hacp_0f]
    rw [pure_sepConj_of_true hnull]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail
  · -- `0 < newCap < 2 ^ 63`: valid layout `RustLayoutOk newCap 1`
    have hnew_lt63 : newCap < 2 ^ 63 := Nat.lt_of_not_ge hge63
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = false :=
      bit63_eq_zero_of_lt hnew_lt63
    have hlay : RustLayoutOk newCap 1 := rustLayoutOk_one hnew_pos hnew_lt63
    have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by bv_omega
    have hnew_beq0 : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    by_cases hold0 : oldCap = 0#64
    · -- `oldCap = 0#64`: `cbz x1, 0x50` → `shim` (`+0x54`) → `__rust_alloc` (`+0x60`)
      subst hold0
      have hbs_nil : bs = [] := by simpa using hbs_le_old
      subst hbs_nil
      apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = 0#64 := (hcpu1.readReg64 .x1).trans hx1
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_shim_pc (by simpa [arm64_norm] using hrun1')
        fun sm_sh hcpu_sh0 hcl_sh hnsp_sh hsym_sh => ?_
      have hcpu_sh := hcpu_sh0.1
      have ⟨hacp_0sh, hvm_0sh⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_sh0 hnsp_sh hsym_sh
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0sh : A.pool lim st s0 = A.pool lim st sm_sh :=
        (A.pool_transport lim st s0 sm_sh hvm_0sh).symm
      have hpc_sh : sm_sh.pc = signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym :=
        hcpu_sh.pc_eq.trans cliIoFinishGrow_shim_pc
      have hrun_sh : sm_sh.status = .Running := hcpu_sh.status_eq.trans hrun1'
      have hsp_sh_eq : sm_sh.sp = s0.sp - 32#64 :=
        hcpu_sh.sp_eq.trans (by simp [arm64_norm])
      have hsp_sh : sm_sh.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_sh_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_sh : sm_sh.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) := by
        rw [hcpu_sh.readReg64 .lr]; simp [arm64_norm]
      have hx19_sh : sm_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hx20_sh : sm_sh.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hgprs_sh : GrowHighGprs s0 sm_sh := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_sh.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_sh : calleeSavedVRegs sm_sh = calleeSavedVRegs s0 :=
        hcpu_sh.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0sh]
      apply seqCodeLoaded hcl_sh
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64))
      apply (SepWP.call_subroutine_frame hshim (x := ())
        hpc_sh hrun_sh hsp_sh hlr_sh
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [rustAllocShimVmSpec]
        exact Satisfies.mono (by sep_frame) hm'
      · intro sf_sh hpc_sfsh hrun_sfsh hsp_sfsh hcs_sfsh
        refine SepWP.done hpc_sfsh hrun_sfsh fun hcl_sfsh => ?_
        dsimp only [rustAllocShimVmSpec]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hacp_sh, hvm_sh⟩
        have hpool_eq_sh : A.pool lim st sm_sh = A.pool lim st sf_sh :=
          (A.pool_transport lim st sm_sh sf_sh hvm_sh).symm
        have hsp_sfsh_eq : sf_sh.sp = s0.sp - 32#64 := hsp_sfsh.trans hsp_sh_eq
        have hx19_sfsh : sf_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfsh.readReg64_x19.trans hx19_sh
        have hx20_sfsh : sf_sh.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfsh.readReg64_x20.trans hx20_sh
        have hgprs_sfsh : GrowHighGprs s0 sf_sh :=
          hgprs_sh.trans (GrowHighGprs.of_calleeSaved hcs_sfsh)
        have hvregs_sfsh : calleeSavedVRegs sf_sh = calleeSavedVRegs s0 :=
          hcs_sfsh.vregs.trans hvregs_sh
        apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfsh
          (mid := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
        intro sa' hcpu_a0
        have hcpu_a := hcpu_a0.1
        change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
        have hpc_a' : sa'.pc = cliIoPl04.base + 88#64 := hcpu_a.pc_eq.trans hpc_sfsh
        have hrun_a' : sa'.status = .Running := hcpu_a.status_eq.trans hrun_sfsh
        have hsp_a_in : sa'.sp = s0.sp - 32#64 := hcpu_a.sp_eq.trans hsp_sfsh_eq
        have hx19_a' : sa'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          (hcpu_a.readReg64 _).trans hx19_sfsh
        have hx20_a' : sa'.readReg64 (.gpr 20#5) = outPtr :=
          (hcpu_a.readReg64 _).trans hx20_sfsh
        wp_sym_steps
        refine SepWP.done cliIoFinishGrow_alloc_pc (by simpa [arm64_norm] using hrun_a')
          fun sm_al hcpu_al0 hcl_al hnsp_al hsym_al => ?_
        have hcpu_al := hcpu_al0.1
        have ⟨hacp_shal, hvm_shal⟩ :=
          vmPreserved_of_seg hcpu_a0 hcpu_al0 hnsp_al hsym_al
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_shal : A.pool lim st sf_sh = A.pool lim st sm_al :=
          (A.pool_transport lim st sf_sh sm_al hvm_shal).symm
        have hacp_0al : AllocCallPreserved s0 sm_al :=
          allocCallPreserved_trans hacp_0sh (allocCallPreserved_trans hacp_sh hacp_shal)
        have hpc_al : sm_al.pc = signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym :=
          hcpu_al.pc_eq.trans cliIoFinishGrow_alloc_pc
        have hrun_al : sm_al.status = .Running := hcpu_al.status_eq.trans hrun_a'
        have hsp_al_eq : sm_al.sp = s0.sp - 32#64 :=
          (hcpu_al.sp_eq.trans (by simp [arm64_norm])).trans hsp_a_in
        have hsp_al : sm_al.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_al_eq]; exact s0.spAligned_sub 32#64 hsp0
        have hlr_al : sm_al.readReg64 .lr =
            cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
              "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) := by
          rw [hcpu_al.readReg64 .lr]; simp [arm64_norm]
        have hx0_al_nat : (sm_al.readReg64 .x0).toNat = newCap := by
          rw [hcpu_al.readReg64 .x0]; simpa [arm64_norm] using hnew_toNat
        have hx1_al_nat : (sm_al.readReg64 .x1).toNat = 1 := by
          rw [hcpu_al.readReg64 .x1]; simp [arm64_norm]
        have hx19_al : sm_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx19_a'
        have hx20_al : sm_al.readReg64 (.gpr 20#5) = outPtr := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx20_a'
        have hgprs_al : GrowHighGprs s0 sm_al := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.2
        have hvregs_al : calleeSavedVRegs sm_al = calleeSavedVRegs s0 :=
          hcpu_al.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs sa').trans
              (hcpu_a.calleeSavedVRegs.trans hvregs_sfsh))
        wp_conv_pre => simp only [hpool_eq_sh, hpool_eq_shal]
        apply seqCodeLoaded hcl_al
          (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64))
        apply (SepWP.call_subroutine_frame halloc (x := (newCap, 1, st))
          hpc_al hrun_al hsp_al hlr_al
          (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
          (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (h_oom := fun _ sf_oom _ hm_oom => by
            have hm' := Satisfies.drop_mid hm_oom
            dsimp only [rustCliAllocBudgetSpecBase] at hm'
            dsimp only [cliIoFinishGrowBudgetEvents]
            simp only [↓reduceIte]
            rw [satisfies_pure_sepConj] at hm' ⊢
            exact ⟨⟨hnew_lt63, hm'.1.1, oomPreserved_of_allocCallPreserved hacp_0al hm'.1.2⟩, hm'.2⟩))
        · intro R' hm'
          dsimp only [rustCliAllocBudgetSpecBase]
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
          rw [hsp_al_eq]
          exact ⟨⟨hx0_al_nat, hx1_al_nat, hlay⟩, Satisfies.mono (by sep_frame) hm'⟩
        · intro sf_al hpc_sfal hrun_sfal hsp_sfal hcs_sfal
          refine SepWP.done hpc_sfal hrun_sfal fun hcl_sfal => ?_
          dsimp only [rustCliAllocBudgetSpecBase]
          wp_conv_pre => simp only [sepConj_assoc]
          apply SepWP.pure_elim; intro hacp_al
          have hsp_sfal_eq : sf_al.sp = s0.sp - 32#64 := hsp_sfal.trans hsp_al_eq
          have hx19_sfal : sf_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            hcs_sfal.readReg64_x19.trans hx19_al
          have hx20_sfal : sf_al.readReg64 (.gpr 20#5) = outPtr :=
            hcs_sfal.readReg64_x20.trans hx20_al
          have hgprs_sfal : GrowHighGprs s0 sf_al :=
            hgprs_al.trans (GrowHighGprs.of_calleeSaved hcs_sfal)
          have hvregs_sfal : calleeSavedVRegs sf_al = calleeSavedVRegs s0 :=
            hcs_sfal.vregs.trans hvregs_al
          by_cases hx0_al0 : sf_al.readReg64 .x0 = 0#64
          · -- `__rust_alloc` returned null: `+0x64` (`cbnz x0, 0x8c`) falls through to `+0x68`
            wp_conv_pre =>
              simp only [show (0 : BitVec 64) = 0#64 from rfl,
                hx0_al0, ↓reduceIte, hsp_al_eq, sepConj_assoc]
              rw [sepConj_left_comm (stackAt _ _) ⌜NullAllowed newCap 1⌝,
                sepConj_left_comm (A.pool lim st sf_al) ⌜NullAllowed newCap 1⌝]
            apply SepWP.pure_elim; intro hnull_al
            apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 104#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_al0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hvm_be⟩ :=
              vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be : A.pool lim st sf_al = A.pool lim st se :=
              (A.pool_transport lim st sf_al se hvm_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader]
              sep_entail) <|
              cliIoFinishGrow_epilogue_err A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnull_al
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
          · -- `__rust_alloc` returned `newPtr ≠ 0`: `+0x64` (`cbnz x0, 0x8c`) jumps to `+0x8c`
            let newPtr := sf_al.readReg64 .x0
            have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_al0
            wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_al0, Bool.false_eq_true, ↓reduceIte, hsp_al_eq,
              pure_sepConj_of_true (Nat.mod_one (sf_al.readReg64 .x0).toNat), sepConj_assoc]
            apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 140#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hvm_be⟩ :=
              vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be :
                A.pool lim (M.stepEvents (rustAllocEvents newCap 1) st) sf_al =
                A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 newCap) st) se := by
              dsimp only [cliIoFinishGrowBudgetEvents]
              simp only [↓reduceIte]
              exact (A.pool_transport lim _ sf_al se hvm_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx0_e : se.readReg64 .x0 = newPtr :=
              (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
                RustCliAllocBudget.repAlloc]
              simp only [↓reduceIte, hnew_ne0, hnew_toNat, List.length_nil, Nat.sub_zero,
                BitVec.add_zero, pointsToBytes_nil]
              rw [pure_sepConj_of_true ⟨Nat.zero_le 0, by decide, holdPtr_ne⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (by rw [pure_sepConj_of_true ⟨Nat.zero_le _, hnew_lt63, hx0_al0⟩]; exact Entails.refl _)))))
              sep_entail) <|
              cliIoFinishGrow_epilogue_ok A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx0_e hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnew_lt63
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
    · -- `oldCap ≠ 0#64`: `__rust_realloc` (`+0x28`)
      have hold_beq0 : (oldCap == 0#64) = false := beq_false_of_ne hold0
      wp_conv_pre =>
        simp only [cliIoVecBuf, RustCliAllocBudget.repAlloc, hold0, ↓reduceIte,
          pure_sepConj_of_true
            (⟨hbs_le_old, hold_lt, holdPtr_ne⟩ : bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64),
          sepConj_assoc]
      apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = oldCap := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = oldPtr := (hcpu1.readReg64 .x2).trans hx2
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_realloc_pc (by simpa [arm64_norm] using hrun1')
        fun sm_re hcpu_re0 hcl_re hnsp_re hsym_re => ?_
      have hcpu_re := hcpu_re0.1
      have ⟨hacp_0re, hvm_0re⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_re0 hnsp_re hsym_re
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0re : A.pool lim st s0 = A.pool lim st sm_re :=
        (A.pool_transport lim st s0 sm_re hvm_0re).symm
      have hpc_re : sm_re.pc = signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym :=
        hcpu_re.pc_eq.trans cliIoFinishGrow_realloc_pc
      have hrun_re : sm_re.status = .Running := hcpu_re.status_eq.trans hrun1'
      have hsp_re_eq : sm_re.sp = s0.sp - 32#64 :=
        hcpu_re.sp_eq.trans (by simp [arm64_norm])
      have hsp_re : sm_re.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_re_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_re : sm_re.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64) := by
        rw [hcpu_re.readReg64 .lr]; simp [arm64_norm]
      have hx0_re : sm_re.readReg64 .x0 = oldPtr := by
        rw [hcpu_re.readReg64 .x0]; simp [arm64_norm]
      have hx1_re_nat : (sm_re.readReg64 .x1).toNat = oldCap.toNat := by
        rw [hcpu_re.readReg64 .x1]; simpa [arm64_norm] using congrArg BitVec.toNat hx1_1'
      have hx2_re_nat : (sm_re.readReg64 .x2).toNat = 1 := by
        rw [hcpu_re.readReg64 .x2]; simp [arm64_norm]
      have hx3_re_nat : (sm_re.readReg64 .x3).toNat = newCap := by
        rw [hcpu_re.readReg64 .x3]; simpa [arm64_norm] using hnew_toNat
      have hx19_re : sm_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hx20_re : sm_re.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hgprs_re : GrowHighGprs s0 sm_re := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_re.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_re : calleeSavedVRegs sm_re = calleeSavedVRegs s0 :=
        hcpu_re.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0re]
      apply seqCodeLoaded hcl_re
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64))
      apply (SepWP.call_subroutine_frame hrealloc
        (x := (oldPtr, oldCap.toNat, 1, newCap, bs, st))
        hpc_re hrun_re hsp_re hlr_re
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ sf_oom _ hm_oom => by
          have hm' := Satisfies.drop_mid hm_oom
          dsimp only [rustCliReallocBudgetSpecBase] at hm'
          dsimp only [cliIoFinishGrowBudgetEvents]
          simp only [hold0, ↓reduceIte]
          rw [satisfies_pure_sepConj] at hm' ⊢
          exact ⟨⟨hnew_lt63, hm'.1.1, oomPreserved_of_allocCallPreserved hacp_0re hm'.1.2⟩, hm'.2⟩))
      · intro R' hm'
        dsimp only [rustCliReallocBudgetSpecBase]
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
          satisfies_pure_sepConj]
        rw [hsp_re_eq]
        exact ⟨⟨hx0_re, hx1_re_nat, hx2_re_nat, hx3_re_nat, hlay, hbs_le_old, hbs_le_new⟩,
          Satisfies.mono (by sep_frame) hm'⟩
      · intro sf_re hpc_sfre hrun_sfre hsp_sfre hcs_sfre
        refine SepWP.done hpc_sfre hrun_sfre fun hcl_sfre => ?_
        dsimp only [rustCliReallocBudgetSpecBase]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; intro hacp_re
        have hsp_sfre_eq : sf_re.sp = s0.sp - 32#64 := hsp_sfre.trans hsp_re_eq
        have hx19_sfre : sf_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfre.readReg64_x19.trans hx19_re
        have hx20_sfre : sf_re.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfre.readReg64_x20.trans hx20_re
        have hgprs_sfre : GrowHighGprs s0 sf_re :=
          hgprs_re.trans (GrowHighGprs.of_calleeSaved hcs_sfre)
        have hvregs_sfre : calleeSavedVRegs sf_re = calleeSavedVRegs s0 :=
          hcs_sfre.vregs.trans hvregs_re
        by_cases hx0_re0 : sf_re.readReg64 .x0 = 0#64
        · -- `__rust_realloc` returned null: `+0x2c` (`cbnz x0, 0x8c`) + `+0x30` (`b 0x68`) → `+0x68`
          wp_conv_pre =>
            simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_re0, ↓reduceIte, hsp_re_eq, sepConj_assoc]
            rw [sepConj_left_comm (stackAt _ _) ⌜NullAllowed newCap 1⌝,
              sepConj_left_comm (A.pool lim st sf_re) ⌜NullAllowed newCap 1⌝]
          apply SepWP.pure_elim; intro hnull_re
          apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 104#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_re0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hvm_be⟩ :=
            vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be : A.pool lim st sf_re = A.pool lim st se :=
            (A.pool_transport lim st sf_re se hvm_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
              RustCliAllocBudget.repAlloc]
            simp only [hold0, ↓reduceIte]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_old, hold_lt, holdPtr_ne⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_err A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnull_re
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
        · -- `__rust_realloc` returned `newPtr ≠ 0`: `+0x2c` (`cbnz x0, 0x8c`) jumps to `+0x8c`
          let newPtr := sf_re.readReg64 .x0
          have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_re0
          wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
            hx0_re0, ↓reduceIte, hsp_re_eq,
            pure_sepConj_of_true (Nat.mod_one (sf_re.readReg64 .x0).toNat), sepConj_assoc]
          apply sepWP_seg_cliIo_block_pure 4 cliIo4_lt hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 140#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hvm_be⟩ :=
            vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be :
              A.pool lim (M.stepEvents (rustReallocEvents oldCap.toNat newCap 1) st) sf_re =
              A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se := by
            dsimp only [cliIoFinishGrowBudgetEvents]
            simp only [hold0, ↓reduceIte]
            exact (A.pool_transport lim _ sf_re se hvm_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx0_e : se.readReg64 .x0 = newPtr :=
            (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
              RustCliAllocBudget.repAlloc]
            simp only [hnew_ne0, ↓reduceIte, hnew_toNat]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_new, hnew_lt63, hx0_re0⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_ok A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx0_e hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnew_lt63
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩

theorem cliIoFinishGrow_budget_ok_withCodeLoaded {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoFinishGrowBudgetSpec M A lim)) :=
  subroutine_ok_of_cliIoWithCodeLoaded
    (cliIoFinishGrow_budget_ok A lim hpl hext4 hshim halloc hrealloc)

end

/-! ## Read-Only Block Subset `{0, 3, 4}` (`CliIoReadsCodeLoaded`) Variants -/

section
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  cliIoReadsKeep CliIoReadsCodeLoaded cliIoWithReadsCodeLoaded
  subroutine_ok_of_cliIoWithReadsCodeLoaded sepWP_seg_cliIo_block_pure_reads
)
open VerifiedLibraries.RustStd (seqCodeLoadedWhere)
arm64_proof_prelude

private theorem cliIoFinishGrow_epilogue_err_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 104#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnull : NullAllowed newCap 1)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithReadsCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 32#64) allocHookStack ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗ cliIoVecBuf A.repAlloc oldCap oldPtr bs ∗
        A.pool lim st se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef : A.pool lim st se = A.pool lim st sf :=
    (A.pool_transport lim st se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithReadsCodeLoaded, cliIoFinishGrowBudgetSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right true <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 1#64 <|
      Entails.sepExists_right (BitVec.ofNat 64 newCap) <| Entails.refl _)
  simp only [↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  rw [pure_sepConj_of_true hnull]
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

/-- Shared success epilogue of `finish_grow` at `cliIoPl04.base + 140#64` (`+0x8c .. +0xa4`). -/
private theorem cliIoFinishGrow_epilogue_ok_reads [CliIoPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} (hext4 : CliIoBlockNoExtern cliIoMpl P 4)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr newPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : M.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : CliIoReadsCodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl04.base + 140#64)
    (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : se.sp = s0.sp - 32#64)
    (hx0 : se.readReg64 .x0 = newPtr)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : GrowHighGprs s0 se)
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se)
    (hnew_lt63 : newCap < 2 ^ 63)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (cliIoWithReadsCodeLoaded cliIoMpl (cliIoFinishGrowBudgetSpec M A lim)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 32#64) allocHookStack ∗ cliIoFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗
        cliIoVecBuf A.repAlloc (BitVec.ofNat 64 newCap) newPtr bs ∗
        A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 32#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = newPtr := (hcpu_e.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr :=
    (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [cliIoFinishGrowSavedSlots, vecHeader]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨hacp_ef, hvm_ef⟩ :=
    vmPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_ef :
      A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se =
      A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) sf :=
    (A.pool_transport lim _ se sf hvm_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1
    · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f (hpost sf hpc_f hrun_f hsp_f hcs_f ?_)
  have hstk_back := cliIoFinishGrow_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  dsimp only [cliIoWithReadsCodeLoaded, cliIoFinishGrowBudgetSpec]
  rw [pure_sepConj_of_true hcl_f]
  refine Entails.trans ?_
    (Entails.sepExists_right false <|
      Entails.sepExists_right newPtr <|
      Entails.sepExists_right 0#64 <|
      Entails.sepExists_right 0#64 <| Entails.refl _)
  simp only [Bool.false_eq_true, ↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
  rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef)]
  refine Entails.trans ?_
    (sepConj_mono_right
      (by rw [pure_sepConj_of_true hnew_lt63]; exact Entails.refl _))
  refine Entails.trans ?_ (sepConj_mono_left hstk_back)
  sep_entail

set_option maxHeartbeats 800000 in
set_option linter.style.haveILetI false in
/-- Placement-generic, cost-model-polymorphic proof of `signal_session_io`'s crate-local
    `<alloc::raw_vec::RawVecInner>::finish_grow` (`signalSessionIoMultiLib` block `4`,
    `168` B / `42` insns) given `hshim` (`rustAllocShimVmSpec`),
    `halloc` (`rustCliAllocBudgetSpecBase M A lim false`), and
    `hrealloc` (`rustCliReallocBudgetSpecBase M A lim`). -/
theorem cliIoFinishGrow_budget_ok_reads {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (cliIoWithReadsCodeLoaded mpl (cliIoFinishGrowBudgetSpec M A lim)) := by
  letI : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 4 cliIoFinishGrowSym cliIo4_lt cliIoFinishGrow_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [cliIoWithReadsCodeLoaded, MultiPlacedLib.withCodeLoadedWhere, cliIoFinishGrowBudgetSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜CliIoReadsCodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le_new⟩, hmem⟩
  have ⟨hbs_le_old, hold_lt, holdPtr_ne⟩ :
      bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64 :=
    cliIoVecBuf_bounds (m := s0.mem)
      (R := stackAt s0.sp (32 + allocHookStack) ∗ vecHeader outPtr v0 v1 v2 ∗
        A.pool lim st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  wp_conv_pre =>
    rw [cliIoFinishGrow_stack_split s0.sp]
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 => ?_
  by_cases hge63 : 2 ^ 63 ≤ newCap
  · -- Branch 1 (`2 ^ 63 ≤ newCap < 2 ^ 64`): `tbnz x3, #63, 0x34` taken; returns `CapacityOverflow` (`{1, 0, v2}`).
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = true :=
      bit63_eq_one_of_ge hge63 hnew_lt64
    have hnull : NullAllowed newCap 1 := by unfold NullAllowed; omega
    apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl0
      (mid := s0.readReg64 .lr)
    intro s1' hcpu1_0
    have hcpu1 := hcpu1_0.1
    change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
      fun sf hcpu_f0 hcl_f hnsp_f hsym_f => ?_
    have hcpu_f := hcpu_f0.1
    have ⟨hacp_0f, hvm_0f⟩ :=
      vmPreserved_of_seg hcpu1_0 hcpu_f0 hnsp_f hsym_f
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0f : A.pool lim st s0 = A.pool lim st sf :=
      (A.pool_transport lim st s0 sf hvm_0f).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun1'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · exact hcpu_f.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    refine SepWP.done hpc_f hrun_f
      ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
    have hstk_back := cliIoFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right true <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right v2 <| Entails.refl _)
    simp only [↓reduceIte, hsp1_in, hpool_eq_0f, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true hacp_0f]
    rw [pure_sepConj_of_true hnull]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail
  · -- Branch 2 (`0 < newCap < 2 ^ 63`): valid layout `RustLayoutOk newCap 1`
    have hnew_lt63 : newCap < 2 ^ 63 := Nat.lt_of_not_ge hge63
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = false :=
      bit63_eq_zero_of_lt hnew_lt63
    have hlay : RustLayoutOk newCap 1 := rustLayoutOk_one hnew_pos hnew_lt63
    have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by bv_omega
    have hnew_beq0 : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    by_cases hold0 : oldCap = 0#64
    · -- Subcase 2a (`oldCap = 0#64`): `cbz x1, 0x50` taken → `shim` (`+0x54`) → `__rust_alloc` (`+0x60`)
      subst hold0
      have hbs_nil : bs = [] := by simpa using hbs_le_old
      subst hbs_nil
      apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = 0#64 := (hcpu1.readReg64 .x1).trans hx1
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_shim_pc (by simpa [arm64_norm] using hrun1')
        fun sm_sh hcpu_sh0 hcl_sh hnsp_sh hsym_sh => ?_
      have hcpu_sh := hcpu_sh0.1
      have ⟨hacp_0sh, hvm_0sh⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_sh0 hnsp_sh hsym_sh
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0sh : A.pool lim st s0 = A.pool lim st sm_sh :=
        (A.pool_transport lim st s0 sm_sh hvm_0sh).symm
      have hpc_sh : sm_sh.pc = signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym :=
        hcpu_sh.pc_eq.trans cliIoFinishGrow_shim_pc
      have hrun_sh : sm_sh.status = .Running := hcpu_sh.status_eq.trans hrun1'
      have hsp_sh_eq : sm_sh.sp = s0.sp - 32#64 :=
        hcpu_sh.sp_eq.trans (by simp [arm64_norm])
      have hsp_sh : sm_sh.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_sh_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_sh : sm_sh.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) := by
        rw [hcpu_sh.readReg64 .lr]; simp [arm64_norm]
      have hx19_sh : sm_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hx20_sh : sm_sh.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hgprs_sh : GrowHighGprs s0 sm_sh := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_sh.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_sh : calleeSavedVRegs sm_sh = calleeSavedVRegs s0 :=
        hcpu_sh.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0sh]
      apply seqCodeLoadedWhere hcl_sh
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64))
      apply (SepWP.call_subroutine_frame hshim (x := ())
        hpc_sh hrun_sh hsp_sh hlr_sh
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [rustAllocShimVmSpec]
        exact Satisfies.mono (by sep_frame) hm'
      · intro sf_sh hpc_sfsh hrun_sfsh hsp_sfsh hcs_sfsh
        refine SepWP.done hpc_sfsh hrun_sfsh fun hcl_sfsh => ?_
        dsimp only [rustAllocShimVmSpec]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hacp_sh, hvm_sh⟩
        have hpool_eq_sh : A.pool lim st sm_sh = A.pool lim st sf_sh :=
          (A.pool_transport lim st sm_sh sf_sh hvm_sh).symm
        have hsp_sfsh_eq : sf_sh.sp = s0.sp - 32#64 := hsp_sfsh.trans hsp_sh_eq
        have hx19_sfsh : sf_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfsh.readReg64_x19.trans hx19_sh
        have hx20_sfsh : sf_sh.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfsh.readReg64_x20.trans hx20_sh
        have hgprs_sfsh : GrowHighGprs s0 sf_sh :=
          hgprs_sh.trans (GrowHighGprs.of_calleeSaved hcs_sfsh)
        have hvregs_sfsh : calleeSavedVRegs sf_sh = calleeSavedVRegs s0 :=
          hcs_sfsh.vregs.trans hvregs_sh
        -- Step `+0x58 .. +0x60` (`mov x0, x19; mov w1, #1; bl __rust_alloc`)
        apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl_sfsh
          (mid := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
        intro sa' hcpu_a0
        have hcpu_a := hcpu_a0.1
        change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
        have hpc_a' : sa'.pc = cliIoPl04.base + 88#64 := hcpu_a.pc_eq.trans hpc_sfsh
        have hrun_a' : sa'.status = .Running := hcpu_a.status_eq.trans hrun_sfsh
        have hsp_a_in : sa'.sp = s0.sp - 32#64 := hcpu_a.sp_eq.trans hsp_sfsh_eq
        have hx19_a' : sa'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          (hcpu_a.readReg64 _).trans hx19_sfsh
        have hx20_a' : sa'.readReg64 (.gpr 20#5) = outPtr :=
          (hcpu_a.readReg64 _).trans hx20_sfsh
        wp_sym_steps
        refine SepWP.done cliIoFinishGrow_alloc_pc (by simpa [arm64_norm] using hrun_a')
          fun sm_al hcpu_al0 hcl_al hnsp_al hsym_al => ?_
        have hcpu_al := hcpu_al0.1
        have ⟨hacp_shal, hvm_shal⟩ :=
          vmPreserved_of_seg hcpu_a0 hcpu_al0 hnsp_al hsym_al
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_shal : A.pool lim st sf_sh = A.pool lim st sm_al :=
          (A.pool_transport lim st sf_sh sm_al hvm_shal).symm
        have hacp_0al : AllocCallPreserved s0 sm_al :=
          allocCallPreserved_trans hacp_0sh (allocCallPreserved_trans hacp_sh hacp_shal)
        have hpc_al : sm_al.pc = signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym :=
          hcpu_al.pc_eq.trans cliIoFinishGrow_alloc_pc
        have hrun_al : sm_al.status = .Running := hcpu_al.status_eq.trans hrun_a'
        have hsp_al_eq : sm_al.sp = s0.sp - 32#64 :=
          (hcpu_al.sp_eq.trans (by simp [arm64_norm])).trans hsp_a_in
        have hsp_al : sm_al.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_al_eq]; exact s0.spAligned_sub 32#64 hsp0
        have hlr_al : sm_al.readReg64 .lr =
            cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
              "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) := by
          rw [hcpu_al.readReg64 .lr]; simp [arm64_norm]
        have hx0_al_nat : (sm_al.readReg64 .x0).toNat = newCap := by
          rw [hcpu_al.readReg64 .x0]; simpa [arm64_norm] using hnew_toNat
        have hx1_al_nat : (sm_al.readReg64 .x1).toNat = 1 := by
          rw [hcpu_al.readReg64 .x1]; simp [arm64_norm]
        have hx19_al : sm_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx19_a'
        have hx20_al : sm_al.readReg64 (.gpr 20#5) = outPtr := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx20_a'
        have hgprs_al : GrowHighGprs s0 sm_al := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.1
          · rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.2
        have hvregs_al : calleeSavedVRegs sm_al = calleeSavedVRegs s0 :=
          hcpu_al.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs sa').trans
              (hcpu_a.calleeSavedVRegs.trans hvregs_sfsh))
        wp_conv_pre => simp only [hpool_eq_sh, hpool_eq_shal]
        apply seqCodeLoadedWhere hcl_al
          (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64))
        apply (SepWP.call_subroutine_frame halloc (x := (newCap, 1, st))
          hpc_al hrun_al hsp_al hlr_al
          (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
          (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (h_oom := fun _ sf_oom _ hm_oom => by
            have hm' := Satisfies.drop_mid hm_oom
            dsimp only [rustCliAllocBudgetSpecBase] at hm'
            dsimp only [cliIoFinishGrowBudgetEvents]
            simp only [↓reduceIte]
            rw [satisfies_pure_sepConj] at hm' ⊢
            exact ⟨⟨hnew_lt63, hm'.1.1, oomPreserved_of_allocCallPreserved hacp_0al hm'.1.2⟩, hm'.2⟩))
        · intro R' hm'
          dsimp only [rustCliAllocBudgetSpecBase]
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
          rw [hsp_al_eq]
          exact ⟨⟨hx0_al_nat, hx1_al_nat, hlay⟩, Satisfies.mono (by sep_frame) hm'⟩
        · intro sf_al hpc_sfal hrun_sfal hsp_sfal hcs_sfal
          refine SepWP.done hpc_sfal hrun_sfal fun hcl_sfal => ?_
          dsimp only [rustCliAllocBudgetSpecBase]
          wp_conv_pre => simp only [sepConj_assoc]
          apply SepWP.pure_elim; intro hacp_al
          have hsp_sfal_eq : sf_al.sp = s0.sp - 32#64 := hsp_sfal.trans hsp_al_eq
          have hx19_sfal : sf_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            hcs_sfal.readReg64_x19.trans hx19_al
          have hx20_sfal : sf_al.readReg64 (.gpr 20#5) = outPtr :=
            hcs_sfal.readReg64_x20.trans hx20_al
          have hgprs_sfal : GrowHighGprs s0 sf_al :=
            hgprs_al.trans (GrowHighGprs.of_calleeSaved hcs_sfal)
          have hvregs_sfal : calleeSavedVRegs sf_al = calleeSavedVRegs s0 :=
            hcs_sfal.vregs.trans hvregs_al
          by_cases hx0_al0 : sf_al.readReg64 .x0 = 0#64
          · -- `__rust_alloc` returned null: `+0x64` (`cbnz x0, 0x8c`) falls through to `+0x68`
            wp_conv_pre =>
              simp only [show (0 : BitVec 64) = 0#64 from rfl,
                hx0_al0, ↓reduceIte, hsp_al_eq, sepConj_assoc]
              rw [sepConj_left_comm (stackAt _ _) ⌜NullAllowed newCap 1⌝,
                sepConj_left_comm (A.pool lim st sf_al) ⌜NullAllowed newCap 1⌝]
            apply SepWP.pure_elim; intro hnull_al
            apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 104#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_al0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hvm_be⟩ :=
              vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be : A.pool lim st sf_al = A.pool lim st se :=
              (A.pool_transport lim st sf_al se hvm_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader]
              sep_entail) <|
              cliIoFinishGrow_epilogue_err_reads A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnull_al
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
          · -- `__rust_alloc` returned `newPtr ≠ 0`: `+0x64` (`cbnz x0, 0x8c`) jumps to `+0x8c`
            let newPtr := sf_al.readReg64 .x0
            have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_al0
            wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_al0, Bool.false_eq_true, ↓reduceIte, hsp_al_eq,
              pure_sepConj_of_true (Nat.mod_one (sf_al.readReg64 .x0).toNat), sepConj_assoc]
            apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl_sfal
              (mid := cliIoPl04.base + 140#64)
            intro sb' hcpu_b0
            have hcpu_b := hcpu_b0.1
            change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
            have hpc_b' : sb'.pc = cliIoPl04.base + 100#64 := hcpu_b.pc_eq.trans hpc_sfal
            have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfal
            have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
            wp_sym_steps
            refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
              fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
            have hcpu_e := hcpu_e0.1
            have ⟨hacp_be, hvm_be⟩ :=
              vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
                (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            have hpool_eq_be :
                A.pool lim (M.stepEvents (rustAllocEvents newCap 1) st) sf_al =
                A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents 0#64 newCap) st) se := by
              dsimp only [cliIoFinishGrowBudgetEvents]
              simp only [↓reduceIte]
              exact (A.pool_transport lim _ sf_al se hvm_be).symm
            have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
            have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
            have hsp_e_eq : se.sp = s0.sp - 32#64 :=
              (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfal_eq)
            have hx0_e : se.readReg64 .x0 = newPtr :=
              (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
            have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx19_sfal))
            have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
              (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
                ((hcpu_b.readReg64 _).trans hx20_sfal))
            have hgprs_e : GrowHighGprs s0 se := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.1
              · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfal.2.2.2.2.2.2.2
            have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
              hcpu_e.calleeSavedVRegs.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                  (hcpu_b.calleeSavedVRegs.trans hvregs_sfal))
            refine SepWP.weaken_pre (by
              rw [hpool_eq_be]
              dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
                RustCliAllocBudget.repAlloc]
              simp only [↓reduceIte, hnew_ne0, hnew_toNat, List.length_nil, Nat.sub_zero,
                BitVec.add_zero, pointsToBytes_nil]
              rw [pure_sepConj_of_true ⟨Nat.zero_le 0, by decide, holdPtr_ne⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (by rw [pure_sepConj_of_true ⟨Nat.zero_le _, hnew_lt63, hx0_al0⟩]; exact Entails.refl _)))))
              sep_entail) <|
              cliIoFinishGrow_epilogue_ok_reads A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
                hx0_e hx19_e hx20_e hgprs_e hvregs_e
                (allocCallPreserved_trans hacp_0al (allocCallPreserved_trans hacp_al hacp_be))
                hnew_lt63
                fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
    · -- Subcase 2b (`oldCap ≠ 0#64`): `cbz x1, 0x50` not taken → `__rust_realloc` (`+0x28`)
      have hold_beq0 : (oldCap == 0#64) = false := beq_false_of_ne hold0
      wp_conv_pre =>
        simp only [cliIoVecBuf, RustCliAllocBudget.repAlloc, hold0, ↓reduceIte,
          pure_sepConj_of_true
            (⟨hbs_le_old, hold_lt, holdPtr_ne⟩ : bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64),
          sepConj_assoc]
      apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl0
        (mid := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl04.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = oldCap := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = oldPtr := (hcpu1.readReg64 .x2).trans hx2
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done cliIoFinishGrow_realloc_pc (by simpa [arm64_norm] using hrun1')
        fun sm_re hcpu_re0 hcl_re hnsp_re hsym_re => ?_
      have hcpu_re := hcpu_re0.1
      have ⟨hacp_0re, hvm_0re⟩ :=
        vmPreserved_of_seg hcpu1_0 hcpu_re0 hnsp_re hsym_re
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0re : A.pool lim st s0 = A.pool lim st sm_re :=
        (A.pool_transport lim st s0 sm_re hvm_0re).symm
      have hpc_re : sm_re.pc = signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym :=
        hcpu_re.pc_eq.trans cliIoFinishGrow_realloc_pc
      have hrun_re : sm_re.status = .Running := hcpu_re.status_eq.trans hrun1'
      have hsp_re_eq : sm_re.sp = s0.sp - 32#64 :=
        hcpu_re.sp_eq.trans (by simp [arm64_norm])
      have hsp_re : sm_re.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_re_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_re : sm_re.readReg64 .lr =
          cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64) := by
        rw [hcpu_re.readReg64 .lr]; simp [arm64_norm]
      have hx0_re : sm_re.readReg64 .x0 = oldPtr := by
        rw [hcpu_re.readReg64 .x0]; simp [arm64_norm]
      have hx1_re_nat : (sm_re.readReg64 .x1).toNat = oldCap.toNat := by
        rw [hcpu_re.readReg64 .x1]; simpa [arm64_norm] using congrArg BitVec.toNat hx1_1'
      have hx2_re_nat : (sm_re.readReg64 .x2).toNat = 1 := by
        rw [hcpu_re.readReg64 .x2]; simp [arm64_norm]
      have hx3_re_nat : (sm_re.readReg64 .x3).toNat = newCap := by
        rw [hcpu_re.readReg64 .x3]; simpa [arm64_norm] using hnew_toNat
      have hx19_re : sm_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hx20_re : sm_re.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hgprs_re : GrowHighGprs s0 sm_re := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_re.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_re : calleeSavedVRegs sm_re = calleeSavedVRegs s0 :=
        hcpu_re.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0re]
      apply seqCodeLoadedWhere hcl_re
        (mid := cliIoPl04.base + (reloc_call_off% cliIoLib04.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64))
      apply (SepWP.call_subroutine_frame hrealloc
        (x := (oldPtr, oldCap.toNat, 1, newCap, bs, st))
        hpc_re hrun_re hsp_re hlr_re
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ sf_oom _ hm_oom => by
          have hm' := Satisfies.drop_mid hm_oom
          dsimp only [rustCliReallocBudgetSpecBase] at hm'
          dsimp only [cliIoFinishGrowBudgetEvents]
          simp only [hold0, ↓reduceIte]
          rw [satisfies_pure_sepConj] at hm' ⊢
          exact ⟨⟨hnew_lt63, hm'.1.1, oomPreserved_of_allocCallPreserved hacp_0re hm'.1.2⟩, hm'.2⟩))
      · intro R' hm'
        dsimp only [rustCliReallocBudgetSpecBase]
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
          satisfies_pure_sepConj]
        rw [hsp_re_eq]
        exact ⟨⟨hx0_re, hx1_re_nat, hx2_re_nat, hx3_re_nat, hlay, hbs_le_old, hbs_le_new⟩,
          Satisfies.mono (by sep_frame) hm'⟩
      · intro sf_re hpc_sfre hrun_sfre hsp_sfre hcs_sfre
        refine SepWP.done hpc_sfre hrun_sfre fun hcl_sfre => ?_
        dsimp only [rustCliReallocBudgetSpecBase]
        wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; intro hacp_re
        have hsp_sfre_eq : sf_re.sp = s0.sp - 32#64 := hsp_sfre.trans hsp_re_eq
        have hx19_sfre : sf_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfre.readReg64_x19.trans hx19_re
        have hx20_sfre : sf_re.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfre.readReg64_x20.trans hx20_re
        have hgprs_sfre : GrowHighGprs s0 sf_re :=
          hgprs_re.trans (GrowHighGprs.of_calleeSaved hcs_sfre)
        have hvregs_sfre : calleeSavedVRegs sf_re = calleeSavedVRegs s0 :=
          hcs_sfre.vregs.trans hvregs_re
        by_cases hx0_re0 : sf_re.readReg64 .x0 = 0#64
        · -- `__rust_realloc` returned null: `+0x2c` (`cbnz x0, 0x8c`) + `+0x30` (`b 0x68`) → `+0x68`
          wp_conv_pre =>
            simp only [show (0 : BitVec 64) = 0#64 from rfl,
              hx0_re0, ↓reduceIte, hsp_re_eq, sepConj_assoc]
            rw [sepConj_left_comm (stackAt _ _) ⌜NullAllowed newCap 1⌝,
              sepConj_left_comm (A.pool lim st sf_re) ⌜NullAllowed newCap 1⌝]
          apply SepWP.pure_elim; intro hnull_re
          apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 104#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_b.readReg64 .x0).trans hx0_re0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hvm_be⟩ :=
            vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be : A.pool lim st sf_re = A.pool lim st se :=
            (A.pool_transport lim st sf_re se hvm_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 104#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
              RustCliAllocBudget.repAlloc]
            simp only [hold0, ↓reduceIte]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_old, hold_lt, holdPtr_ne⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_err_reads A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnull_re
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
        · -- `__rust_realloc` returned `newPtr ≠ 0`: `+0x2c` (`cbnz x0, 0x8c`) jumps to `+0x8c`
          let newPtr := sf_re.readReg64 .x0
          have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hx0_re0
          wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl,
            hx0_re0, ↓reduceIte, hsp_re_eq,
            pure_sepConj_of_true (Nat.mod_one (sf_re.readReg64 .x0).toNat), sepConj_assoc]
          apply sepWP_seg_cliIo_block_pure_reads 4 cliIo4_lt rfl hext4 cliIoBlockNoSvc0_04 hcl_sfre
            (mid := cliIoPl04.base + 140#64)
          intro sb' hcpu_b0
          have hcpu_b := hcpu_b0.1
          change SepWP (cliIoPC04.rebase cliIoPl04.base (fun _ => none)) _ _ _ _
          have hpc_b' : sb'.pc = cliIoPl04.base + 44#64 := hcpu_b.pc_eq.trans hpc_sfre
          have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfre
          have hx0_b' : sb'.readReg64 (.gpr 0#5) = newPtr := hcpu_b.readReg64 .x0
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
            fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
          have hcpu_e := hcpu_e0.1
          have ⟨hacp_be, hvm_be⟩ :=
            vmPreserved_of_seg hcpu_b0 hcpu_e0 hnsp_e hsym_e
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          have hpool_eq_be :
              A.pool lim (M.stepEvents (rustReallocEvents oldCap.toNat newCap 1) st) sf_re =
              A.pool lim (M.stepEvents (cliIoFinishGrowBudgetEvents oldCap newCap) st) se := by
            dsimp only [cliIoFinishGrowBudgetEvents]
            simp only [hold0, ↓reduceIte]
            exact (A.pool_transport lim _ sf_re se hvm_be).symm
          have hpc_e : se.pc = cliIoPl04.base + 140#64 := hcpu_e.pc_eq.trans (by simp [arm64_norm])
          have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_b'
          have hsp_e_eq : se.sp = s0.sp - 32#64 :=
            (hcpu_e.sp_eq.trans (by simp [arm64_norm])).trans (hcpu_b.sp_eq.trans hsp_sfre_eq)
          have hx0_e : se.readReg64 .x0 = newPtr :=
            (hcpu_e.readReg64 .x0).trans ((by simp [arm64_norm] : _ = sb'.readReg64 .x0).trans hx0_b')
          have hx19_e : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx19_sfre))
          have hx20_e : se.readReg64 (.gpr 20#5) = outPtr :=
            (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sb'.readReg64 _).trans
              ((hcpu_b.readReg64 _).trans hx20_sfre))
          have hgprs_e : GrowHighGprs s0 se := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.1
            · rw [hcpu_e.readReg64]; simpa [arm64_norm] using (hcpu_b.readReg64 _).trans hgprs_sfre.2.2.2.2.2.2.2
          have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
            hcpu_e.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
                (hcpu_b.calleeSavedVRegs.trans hvregs_sfre))
          refine SepWP.weaken_pre (by
            rw [hpool_eq_be]
            dsimp only [cliIoFinishGrowSavedSlots, vecHeader, cliIoVecBuf,
              RustCliAllocBudget.repAlloc]
            simp only [hnew_ne0, ↓reduceIte, hnew_toNat]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_new, hnew_lt63, hx0_re0⟩]; exact Entails.refl _)))))
            sep_entail) <|
            cliIoFinishGrow_epilogue_ok_reads A lim hext4 hcl_e hpc_e hrun_e hsp0 hsp_e_eq
              hx0_e hx19_e hx20_e hgprs_e hvregs_e
              (allocCallPreserved_trans hacp_0re (allocCallPreserved_trans hacp_re hacp_be))
              hnew_lt63
              fun sf _ _ hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩

/-- `withCodeLoaded` projection of `cliIoFinishGrow_budget_ok_reads`. -/
theorem cliIoFinishGrow_budget_ok_withReadsCodeLoaded {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      rustAllocShimVmSpec)
    (halloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym)
      (rustCliAllocBudgetSpecBase M A lim false))
    (hrealloc : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym)
      (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere cliIoReadsKeep mpl (cliIoFinishGrowBudgetSpec M A lim)) :=
  subroutine_ok_of_cliIoWithReadsCodeLoaded
    (cliIoFinishGrow_budget_ok_reads A lim hpl hext4 hshim halloc hrealloc)


end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget
