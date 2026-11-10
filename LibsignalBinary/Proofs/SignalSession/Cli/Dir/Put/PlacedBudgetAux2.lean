/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Hit Exit and Search Loop Body for `Dir::put::<String>` (Block 542)

Verifies the cache-hit exit (`+112 .. +192`), loop latch (`+68 .. +76`), and single-iteration search
loop body (`+80 .. +108`) for `Dir::put::<String>` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (
  arrayAt arrayAt_append arrayAt_concat arrayAt_cons arrayAt_nil vecAt vecBuf_of_ne_zero vecHeader
  vecHeader_entails_memRegion vecU8 vecU8At
)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (SepWPp.of_sepWP_cs_placed StepInvPlaced)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (
  DirGhost DirPutGhost cliBcmpName cliBcmpSpec dirAt dirEntryAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_542 lsProg_542)
open CryptoVerification.SignalSession.Cli.Put.Helpers (
  PutCalleeOkPlaced PutCalleeSavedPlaced dirAt_of_vecAt putCalleeOkPlaced_get putCalleeOkPlaced_mk
  putSavedCells setOrPush_hit sp_sub_96_aligned vecU8At_eq_header_rest' vecU8Rest
  vecU8Rest_expose_bytes vecU8_intro_header_rest withPutCSPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (growOneDirRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (
  DirPutTailEnv dirPutTailEnv_hit_freeOnly putPanicQPlaced putRetQPlaced step_bcmp_call_p
  step_dealloc_call_p step_epilogue_ret_p step_epilogue_tail_dealloc_p step_miss_p
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private structure Hide (P : Prop) : Prop where
  out : P

theorem not_miss_of_hit {changed pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {name oldBs : List (BitVec 8)}
    (hx_eq : changed = pre ++ (name, oldBs) :: rest) :
    ¬ ∀ e ∈ changed, e.1 ≠ name := by
  intro hall
  refine hall (name, oldBs) ?_ rfl
  rw [hx_eq]
  exact List.mem_append_right _ (List.Mem.head _)

/-- Shared hit-branch continuation (`+136 .. +152`): writes `{bytes}` over `[curPtr + 24 .. +48)`,
reassembles `dirAt A.repAlloc x.self (x.dir.put x.name x.bytes)`, and branches on `nameCap = 0`
between `step_epilogue_ret_p` (`+248`) and `step_epilogue_tail_dealloc_p` (`+156`). -/
theorem step_hit_store_and_exit_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ} {evsAcc : List AllocEvent}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr oldCap oldPtr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hfAcc : FreeOnlyEvs evsAcc)
    (hPutEnv : ∀ evs, DirPutTailEnv x.dir x.name evs → PutEnv x.dir x.name x.bytes evs)
    (hpc : s.pc = (blkPl_542).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc (ptr + BitVec.ofNat 64 (pre.length * 48)) x.name ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64) ↦₆₄ oldCap) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64) ↦₆₄ oldPtr) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗
        A.pool lim (M.stepEvents evsAcc st0) s)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  clear hdealloc
  subst hP
  have hhit : ¬ ∀ e ∈ x.dir.changed, e.1 ≠ x.name := not_miss_of_hit hx_eq
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq_h.out, List.length_append, List.length_cons] at hlen_le
    omega
  have h32 : curPtr + 32#64 = (curPtr + 24#64) + 8#64 := by bv_arith
  have h40 : curPtr + 40#64 = (curPtr + 24#64) + 16#64 := by bv_arith
  rw [h32, h40,
      show vecU8 A.repAlloc x.bytesV x.bytes =
        (∃∗ bytesCap : BitVec 64, ∃∗ bytesPtr : BitVec 64,
          vecU8At A.repAlloc x.bytesV bytesCap bytesPtr x.bytes) from rfl]
  clear h32 h40
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A.repAlloc x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes ∗
        A.pool lim (M.stepEvents evsAcc st0) s) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
  have hbytesV_mem :
      ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ⊢ memRegion x.bytesV 24 := by
    have hhdrV :
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) =
        vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) := by
      unfold vecHeader; sep_ac_rfl
    rw [hhdrV]
    exact vecHeader_entails_memRegion x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length)
  have hdir_pack :
      vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curPtr x.name ∗
        (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) := by
    have hnew_entry :
        vecU8 A.repAlloc curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes) ⊢
        dirEntryAt A.repAlloc (x.name, x.bytes) curPtr := by
      have hhdr2 :
          ((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes =
          vecHeader (curPtr + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes := by
        unfold vecHeader; sep_ac_rfl
      rw [hhdr2]
      exact sepConj_mono_right (vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr)
    have hput_eq : (x.dir.put x.name x.bytes) =
        { changed := pre ++ (x.name, x.bytes) :: rest, path := x.dir.path } := by
      simp only [DirGhost.put, hx_eq_h.out, setOrPush_hit hpre]
    have hlen_same : (pre ++ (x.name, x.bytes) :: rest).length = x.dir.changed.length := by
      rw [hx_eq_h.out, List.length_append, List.length_append, List.length_cons, List.length_cons]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (Entails.trans (by rw [← sepConj_assoc]; exact Entails.refl _)
          (sepConj_mono_left hnew_entry))))) ?_
    have harr_join :
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          (dirEntryAt A.repAlloc (x.name, x.bytes) curPtr ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest) =
        arrayAt (dirEntryAt A.repAlloc) 48 ptr (pre ++ (x.name, x.bytes) :: rest) := by
      rw [arrayAt_append (dirEntryAt A.repAlloc) 48 ptr pre ((x.name, x.bytes) :: rest), arrayAt_cons]
    rw [hput_eq]
    refine Entails.trans ?_
      (dirAt_of_vecAt A.repAlloc x.self cap ptr (pre ++ (x.name, x.bytes) :: rest) x.dir.path)
    unfold vecAt
    rw [vecBuf_of_ne_zero A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr _ hcap0, hlen_same,
        pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩, ← harr_join]
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hncap0 : nameCap = 0
  · subst hncap0
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 248#64)
    wp_steps_sync_pool ((blkPl_542).base + 248#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_ret_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := evsAcc) (v3 := v3) (R := R)
        h96 hle_stk
        (hPutEnv evsAcc (dirPutTailEnv_hit_freeOnly hhit hfAcc))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    rw [show vecU8Rest A.repAlloc 0 namePtr x.name = emp from rfl]
    simp only [emp_sepConj]
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          vecU8 A.repAlloc curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗
        A.pool lim (M.stepEvents evsAcc st0) _ by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 156#64)
    wp_steps_sync_pool ((blkPl_542).base + 156#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_tail_dealloc_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := evsAcc)
        (v3 := v3) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 hhook hle_stk hncap0 hna_le hna_lt
        (hPutEnv _ (dirPutTailEnv_hit_freeOnly hhit (hfAcc.append (FreeOnlyEvs.singleton 1 nameCap.toNat))))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          vecU8 A.repAlloc curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A.repAlloc bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗
        A.pool lim (M.stepEvents evsAcc st0) _ by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem))))))

/-- Full hit exit (`+112 .. +192`): drops `entry.bytes` if `oldCap ≠ 0` (`+112 .. +132`),
then calls `step_hit_store_and_exit_p` (`+136 .. +152`). -/
theorem step_hit_exit_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hPutEnv : ∀ evs, DirPutTailEnv x.dir x.name evs → PutEnv x.dir x.name x.bytes evs)
    (hpc : s.pc = (blkPl_542).base + 112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        dirEntryAt A.repAlloc (x.name, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A.repAlloc (x.name, oldBs) curPtr =
        vecU8 A.repAlloc curPtr x.name ∗
          (∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
            vecU8At A.repAlloc (curPtr + 0x18#64) oldCap oldPtr oldBs) from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun oldCap => ?_
  refine SepWPp.exists_elim fun oldPtr => ?_
  rw [vecU8At_eq_header_rest' A.repAlloc (curPtr + 0x18#64) oldCap oldPtr oldBs,
      show vecHeader (curPtr + 0x18#64) oldCap oldPtr (BitVec.ofNat 64 oldBs.length) =
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ (((curPtr + 0x18#64) + 8#64) ↦₆₄ oldPtr) ∗
          (((curPtr + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) from rfl]
  have hcur24 : curPtr + 32#64 - 8#64 = curPtr + 24#64 := by bv_arith
  have hcur32 : (curPtr + 0x18#64) + 8#64 = curPtr + 32#64 := by bv_arith
  have hcur40 : (curPtr + 0x18#64) + 16#64 = curPtr + 40#64 := by bv_arith
  rw [hcur32, hcur40]
  clear hcur32 hcur40
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜oldBs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Rest A.repAlloc oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hold_le, hold_lt, _⟩ => ?_
  by_cases hold0 : oldCap = 0
  · subst hold0
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 136#64)
    wp_steps_sync_pool ((blkPl_542).base + 136#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    rw [show vecU8Rest A.repAlloc 0 oldPtr oldBs = emp from rfl]
    simp only [emp_sepConj]
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := [])
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := 0) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        FreeOnlyEvs.nil hPutEnv
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm]; rfl)
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    rw [M.stepEvents_nil]
    dsimp only [curPtr]
    exact Entails.of_eq (by sep_ac_rfl)
  · apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsRustDeallocSymCli)
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retDealloc := (blkPl_542).base + 136#64
    refine step_dealloc_call_p (A := A) (lim := lim) (H := H) (stk := stk)
      (curSt := st0)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes)
      hdealloc hhook96 hle_stk oldCap oldPtr retDealloc oldBs
      hold0 hold_le hold_lt
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm hput_csm => ?_)
      (by dsimp only [retDealloc]; simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm])
    dsimp only [retDealloc] at hpcm
    clear retDealloc
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64 :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm]; rfl)
    clear hcsm hinv1
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
        (st0 := st0) (evsAcc := rustDeallocEvents oldCap.toNat 1)
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := oldCap) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        (FreeOnlyEvs.singleton 1 oldCap.toNat) hPutEnv
        hpcm hrunm hspm halign htrm
        sm_x19 sm_x20 sm_x21 sm_x22
        hput_csm
        rfl)
    exact Entails.of_eq (by dsimp only [curPtr]; sep_ac_rfl)

/-- Loop latch (`+68 .. +76`): advances `X27 -= 48, X26 += 48`, exiting to `step_miss_p` (`+196`)
when `rest = []` or invoking `hcont` at `+80` when `rest = hd' :: rest'`. -/
theorem step_latch_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ}
    {pre : List (List (BitVec 8) × List (BitVec 8))}
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A lim growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ hd :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hd.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hFit0 : FitsEnv M lim st0 (PutEnv x.dir x.name x.bytes))
    (hPutEnv : ∀ evs, DirPutTailEnv x.dir x.name evs → PutEnv x.dir x.name x.bytes evs)
    (hpc : s.pc = (blkPl_542).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd :: rest).length))
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        dirEntryAt A.repAlloc hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s)
    (hcont : ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (blkPl_542).base + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSavedPlaced s0 sn →
      SepWPp (lsProg_542 H) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr (pre ++ [hd]) ∗
          dirEntryAt A.repAlloc hd' (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48)) ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A.repAlloc nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 sn)
        (putRetQPlaced A lim PutEnv stk x st0 s0 R)
        (putPanicQPlaced A lim PutEnv stk x st0 s0 R)) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  have hgrow0 := putCalleeOkPlaced_mk H (lsmpl.base 586) hgrow
  clear hgrow
  subst hP
  have hpre' : ∀ e ∈ pre ++ [hd], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact hpre e h1
    · rcases List.mem_singleton.mp h2 with rfl
      exact hhd_ne
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq, List.length_append, List.length_cons] at hlen_le
    omega
  cases rest with
  | nil =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ [hd]) := ⟨hx_eq⟩
    clear hx_eq
    have _ : Hide _ := ⟨hcont⟩
    clear hcont
    have hx27_48 : s.readReg64 .x27 = 48#64 := hx27
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 196#64)
    wp_steps_sync_pool ((blkPl_542).base + 196#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_l
    have hvec_join :
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          dirEntryAt A.repAlloc hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) [] ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) =
        vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self cap ptr x.dir.changed := by
      have harr_cat :
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            dirEntryAt A.repAlloc hd (ptr + BitVec.ofNat 64 (pre.length * 48)) =
          arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed := by
        rw [hx_eq_h.out, show hd :: ([] : List _) = [hd] from rfl,
            arrayAt_concat (dirEntryAt A.repAlloc) 48 ptr pre hd]
      unfold vecAt
      rw [vecBuf_of_ne_zero A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed hcap0,
          pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩,
          arrayAt_nil, emp_sepConj, ← harr_cat]
      sep_ac_rfl
    refine SepWPp.weaken_pre ?_
      (step_miss_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H)
        (growStk := growStk) (stk := stk) (st0 := st0)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
        (by rwa [hx_eq_h.out])
        hlen_lt32 hna_le hna_lt hna_ptr hFit0 hPutEnv
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (hcs.step (by simp only [arm64_norm]) hinv_l)
        rfl)
    refine Entails.of_eq ?_
    rw [← hvec_join]
    sep_ac_rfl
  | cons hd' rest' =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ hd :: hd' :: rest') := ⟨hx_eq⟩
    clear hx_eq
    have hcont_h : Hide _ := ⟨hcont⟩
    clear hcont
    have hrem_bound : 48 * (hd :: hd' :: rest').length < 2 ^ 64 := by
      rw [hx_eq_h.out, List.length_append] at hlen_lt32
      simp only [List.length_cons] at hlen_lt32 ⊢
      omega
    have hx27' : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) + 48#64 := by
      rw [hx27, List.length_cons (a := hd), Nat.mul_succ, BitVec.ofNat_add]
    clear hx27
    have hx27_ne0 : BitVec.ofNat 64 (48 * (hd' :: rest').length) ≠ 0#64 := by
      intro h0
      have h := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by simp only [List.length_cons] at hrem_bound ⊢; omega),
          BitVec.toNat_zero] at h
      simp only [List.length_cons] at h
      omega
    generalize hrem_eq : BitVec.ofNat 64 (48 * (hd' :: rest').length) = rem at hx27' hx27_ne0
    have hrem_h : Hide _ := ⟨hrem_eq⟩
    clear hrem_eq hrem_bound
    have hcur_next :
        ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64 =
          ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) := by
      have hl : (pre ++ [hd]).length = pre.length + 1 := by simp
      rw [hl, BitVec.add_assoc,
          show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
          ← BitVec.ofNat_add, Nat.succ_mul]
    have hcur_next_h : Hide _ := ⟨hcur_next⟩
    clear hcur_next
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 80#64)
    wp_steps_sync_pool ((blkPl_542).base + 80#64)
    apply SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv_l
    refine SepWPp.weaken_pre ?_
      (hcont_h.out hd' rest' _ rfl
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm]; rw [← hcur_next_h.out]; bv_arith)
        (by simp only [arm64_norm, ← hrem_h.out])
        (hcs.step (by simp only [arm64_norm]) hinv_l))
    rw [hcur_next_h.out, arrayAt_cons, arrayAt_concat (dirEntryAt A.repAlloc) 48 ptr pre hd]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Single iteration of the search loop body (`+80 .. +108`) at entry `(eName, oldBs)` followed by
`rest`: compares lengths (`+80 .. +88`), optionally calls `bcmp` (`+92 .. +108`), exits via
`step_hit_exit_p` on a match (`eName = x.name`), or advances via `step_latch_p` on a mismatch
(`eName ≠ x.name`). -/
theorem step_loop_body_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost} {st0 : M.σ}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {eName oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hbcmp : subroutine_ok (lsProg_542 H) (lsρ cliBcmpName)
      (withPutCSPlaced s0 (withVmPreserved cliBcmpSpec)))
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack M A lim extHookStack)))
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A lim growStk)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (eName, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hFit0 : FitsEnv M lim st0 (PutEnv x.dir x.name x.bytes))
    (hPutEnv : ∀ evs, DirPutTailEnv x.dir x.name evs → PutEnv x.dir x.name x.bytes evs)
    (hpc : s.pc = (blkPl_542).base + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length))
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        dirEntryAt A.repAlloc (eName, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s)
    (hcont : eName ≠ x.name →
      ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (blkPl_542).base + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSavedPlaced s0 sn →
      SepWPp (lsProg_542 H) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr (pre ++ [(eName, oldBs)]) ∗
          dirEntryAt A.repAlloc hd' (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48)) ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A.repAlloc nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 sn)
        (putRetQPlaced A lim PutEnv stk x st0 s0 R)
        (putPanicQPlaced A lim PutEnv stk x st0 s0 R))
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A lim PutEnv stk x st0 s0 R)
      (putPanicQPlaced A lim PutEnv stk x st0 s0 R) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  have hgrow0 := putCalleeOkPlaced_mk H (lsmpl.base 586) hgrow
  have hcont_h : Hide _ := ⟨hcont⟩
  clear hdealloc hgrow hcont
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (eName, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A.repAlloc (eName, oldBs) curPtr =
        (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64, vecU8At A.repAlloc curPtr eCap ePtr eName) ∗
          vecU8 A.repAlloc (curPtr + 0x18#64) oldBs from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun eCap => ?_
  refine SepWPp.exists_elim fun ePtr => ?_
  rw [vecU8At_eq_header_rest' A.repAlloc curPtr eCap ePtr eName,
      show vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) =
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜eName.length ≤ eCap.toNat ∧ eCap.toNat < 2 ^ 63 ∧ ePtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A.repAlloc eCap ePtr eName ∗
        vecU8 A.repAlloc (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 s) by sep_ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨he_le, he_lt, he_ptr⟩ => ?_
  have he_repack :
      ((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A.repAlloc eCap ePtr eName) ∗
        vecU8 A.repAlloc (curPtr + 0x18#64) oldBs ⊢
      dirEntryAt A.repAlloc (eName, oldBs) curPtr := by
    refine sepConj_mono_left ?_
    have hhdr :
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A.repAlloc eCap ePtr eName =
        vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A.repAlloc eCap ePtr eName := by
      unfold vecHeader; sep_ac_rfl
    rw [hhdr]
    exact vecU8_intro_header_rest he_le he_lt he_ptr
  have hcur16 : curPtr + 32#64 - 16#64 = curPtr + 16#64 := by bv_arith
  have hcur8 : curPtr + 32#64 - 24#64 = curPtr + 8#64 := by bv_arith
  by_cases hlen_eq : BitVec.ofNat 64 eName.length = BitVec.ofNat 64 x.name.length
  · have hlen_nat : eName.length = x.name.length := by
      have h := congrArg BitVec.toNat hlen_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    apply SepWPp.of_sepWP_cs_placed (mid := lsρ cliBcmpName)
    wp_steps_sync_pool (lsρ cliBcmpName)
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    rw [vecU8Rest_expose_bytes (A := A.repAlloc) (cap := eCap) (ptr := ePtr) he_le,
        vecU8Rest_expose_bytes (A := A.repAlloc) (cap := nameCap) (ptr := namePtr) hna_le]
    have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = eName.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen_nat]
    let retBcmp := (blkPl_542).base + 108#64
    refine step_bcmp_call_p (A := A) (lim := lim) (H := H) (stk := stk)
      (curSt := st0)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        (if eCap = 0 then emp
         else A.repAlloc.live ePtr eCap.toNat 1 ∗
           memRegion (ePtr + BitVec.ofNat 64 eName.length) (eCap.toNat - eName.length)) ∗
        vecU8 A.repAlloc (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        (if nameCap = 0 then emp
         else A.repAlloc.live namePtr nameCap.toNat 1 ∗
           memRegion (namePtr + BitVec.ofNat 64 x.name.length) (nameCap.toNat - x.name.length)) ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes)
      hbcmp hhook96 hle_stk ePtr namePtr retBcmp eName x.name
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hx2_nat])
      hlen_nat.symm
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl)
      fun sm hpcm hrunm hspm htrm heq_iff hcsm hput_csm => ?_
    dsimp only [retBcmp] at hpcm
    clear retBcmp
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = x.self := hcsm.2.2.2.1.trans (by simp only [arm64_norm, hx22])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, hx23])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx24])
    have sm_x25 : sm.readReg64 .x25 = ptr := hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
    have sm_x26 : sm.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 :=
      hcsm.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx26]; rfl)
    have sm_x27 : sm.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length) :=
      hcsm.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx27])
    clear hcsm hinv1
    refine SepWPp.weaken_pre
      (show _ ⊢
        putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          dirEntryAt A.repAlloc (eName, oldBs) curPtr ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A.repAlloc nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 sm by
        refine Entails.trans (Entails.of_eq (show _ =
          putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
            vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
            A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
              ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
              vecU8Rest A.repAlloc eCap ePtr eName) ∗
              vecU8 A.repAlloc (curPtr + 0x18#64) oldBs) ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            vecU8Rest A.repAlloc nameCap namePtr x.name ∗
            memRegion x.nameV 24 ∗
            vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 sm by
            rw [vecU8Rest_expose_bytes (A := A.repAlloc) (cap := eCap) (ptr := ePtr) he_le,
                vecU8Rest_expose_bytes (A := A.repAlloc) (cap := nameCap) (ptr := namePtr) hna_le]
            sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))) ?_
    by_cases hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32
    · have heq_name : eName = x.name := heq_iff.mp hw0
      subst heq_name
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 112#64)
      wp_steps_sync_pool ((blkPl_542).base + 112#64)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_hit_exit_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H) (stk := stk)
          (st0 := st0)
          (pre := pre) (rest := rest) (oldBs := oldBs)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOkPlaced_get hdealloc0) h96 hhook96 hle_stk
          hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt hPutEnv
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x26])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl)
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hne_name : eName ≠ x.name := mt heq_iff.mpr hw0
      have hw0_64 :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        exact hw0 (by simpa using congrArg (BitVec.truncate 32) h0)
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 68#64)
      wp_steps_sync_pool ((blkPl_542).base + 68#64)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_latch_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H)
          (growStk := growStk) (stk := stk) (st0 := st0)
          (pre := pre) (hd := (eName, oldBs)) (rest := rest)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
          hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
          hna_le hna_lt hna_ptr hFit0 hPutEnv
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x22])
          (by simp only [arm64_norm, sm_x23])
          (by simp only [arm64_norm, sm_x24])
          (by simp only [arm64_norm, sm_x25])
          (by simp only [arm64_norm, sm_x26])
          (by simp only [arm64_norm, sm_x27])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl
          (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
            hcont_h.out hne_name hd' rest' sn hrest hpcsn
              h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hne_name : eName ≠ x.name := fun h => hlen_eq (h ▸ rfl)
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 68#64)
    wp_steps_sync_pool ((blkPl_542).base + 68#64)
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_latch_p (A := A) (lim := lim) (PutEnv := PutEnv) (H := H)
        (growStk := growStk) (stk := stk) (st0 := st0)
        (pre := pre) (hd := (eName, oldBs)) (rest := rest)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
        hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
        hna_le hna_lt hna_ptr hFit0 hPutEnv
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm, hx26]; rfl)
        (by simp only [arm64_norm, hx27])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl
        (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
          hcont_h.out hne_name hd' rest' sn hrest hpcsn
            h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A.repAlloc eCap ePtr eName) ∗
          vecU8 A.repAlloc (curPtr + 0x18#64) oldBs) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A.repAlloc nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A.repAlloc x.bytesV x.bytes ∗ A.pool lim st0 _ by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux2
