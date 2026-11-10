/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Search Loop for `Dir::put::<&str>` (Block 543)

Verifies the loop latch (`+120..+128`), post-`bcmp` dispatch (`+160`), loop body, and inductive
`Dir.changed` search loop (`step_loop_543`) on Block 543 under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (arrayAt arrayAt_append vecBuf vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false)
open CryptoVerification.SignalSession.Cli (
  DirGhost DirPutStrGhost cliBcmpName cliBcmpSpec dirEntryAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_543 lsProg_543)
open CryptoVerification.SignalSession.Cli.PutStr.Helpers (
  PresHigh nameBuf nameBufRest nameBuf_expose_bytes ofNat_toNat_of_lt
  savedSlots sepWPp_exists_left sepWPp_pure_left sepWPp_weaken_pre setOrPush_append_of_forall_ne
  stackAt_split_sub vecU8At_eq_header_heap vecU8Heap vecU8Heap_expose_bytes vecU8Rest
  vecU8_of_header_heap
)
open CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers (
  CurEq atOff543 sepWPp_cut_rebase_543 sepWPp_eq_pre stackAt_split_sp
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced growOneDirSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (
  DirPutStrPanicPlaced DirPutStrPostPlaced bcmp_lscro_ok_at_dirPutStr_543 call_lscro_wpp
  panic_false_wpp_543 step_hit_543 step_miss_543
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem entails_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem ite_false_eq {α : Sort _} (t e : α) : (if false = true then t else e) = e :=
  rfl

private theorem bv_sub_eq_add_neg64 (a b : BitVec 64) : a - b = a + (-b) :=
  BitVec.sub_eq_add_neg a b

private theorem sub48_latch (n : Nat) (hlt : (n + 1) * 48 < 2 ^ 64) :
    BitVec.ofNat 64 ((n + 1) * 48) - 48#64 = BitVec.ofNat 64 (n * 48) := by
  have h1 := ofNat_toNat_of_lt hlt
  have h2 := ofNat_toNat_of_lt (show n * 48 < 2 ^ 64 by omega)
  have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
  have hle : (48#64 : BitVec 64) ≤ BitVec.ofNat 64 ((n + 1) * 48) := by
    rw [BitVec.le_def, h48, h1]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle, h1, h2, h48]
  omega

private theorem setOrPush_hit_middle (name bs ev : List (BitVec 8))
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (hpre : ∀ p ∈ pre, p.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ (name, ev) :: rest) =
      pre ++ (name, bs) :: rest := by
  rw [setOrPush_append_of_forall_ne name bs pre ((name, ev) :: rest) hpre]
  simp [DirGhost.setOrPush]

private theorem w0_cbnz_zero {w : BitVec 64} (h : w.setWidth 32 = 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 w) == 0#64) = true := by
  have h1 : BitVec.truncate 32 w = 0#32 := h
  rw [h1]
  rfl

private theorem w0_cbnz_nonzero {w : BitVec 64} (h : w.setWidth 32 ≠ 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 w) == 0#64) = false := by
  apply beq_false_of_ne
  intro hz
  apply h
  have h2 := congrArg (BitVec.setWidth 32) hz
  have h3 : (BitVec.zeroExtend 64 (BitVec.truncate 32 w)).setWidth 32 = w.setWidth 32 := by
    bv_omega
  rw [h3] at h2
  exact h2

/-- Loop latch `+120..+128` on Block `543`: exits to `step_miss_543` when `rest = []` or
advances to `hnext` at `+132` when `rest = e' :: rest'`. -/
private theorem step_latch_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 : State)
    (cap ptr namePtr bCap bPtr curBase : BitVec 64)
    (pre : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hsplit : x.dir.changed = pre ++ e :: rest)
    (hpre_ne : ∀ p ∈ pre, p.1 ≠ x.name)
    (hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)))
    (hnext :
      let cal := max growStk extHookStack
      ∀ (s2 : State),
        rest ≠ [] →
        x.dir.changed = (pre ++ [e]) ++ rest →
        (∀ p ∈ pre ++ [e], p.1 ≠ x.name) →
        LibsignalCodeRoLoaded lsmpl s2.mem →
        s2.pc = atOff543 132 →
        s2.status = .Running →
        s2.spAligned = true →
        s2.sp = s0.sp - 80#64 →
        s2.trace = s0.trace →
        PresHigh s0 s2 →
        s2.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
        s2.readReg64 .x20 = x.bytesV →
        s2.readReg64 .x21 = namePtr →
        s2.readReg64 .x22 = x.self →
        s2.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
        s2.readReg64 .x24 = ptr →
        s2.readReg64 .x25 = ptr + BitVec.ofNat 64 ((pre ++ [e]).length * 48) + 32#64 →
        s2.readReg64 .x26 = BitVec.ofNat 64 (rest.length * 48) →
        SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s2
          ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2)
          (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
          (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R))
    (sl : State)
    (he_ne : e.1 ≠ x.name)
    (hcrl_l : LibsignalCodeRoLoaded lsmpl sl.mem)
    (hpcl : sl.pc = atOff543 120)
    (hrunl : sl.status = .Running)
    (hspal : sl.spAligned = true)
    (hspl : sl.sp = s0.sp - 80#64)
    (htrl : sl.trace = s0.trace)
    (hhighl : PresHigh s0 sl)
    (hr19 : sl.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hr20 : sl.readReg64 .x20 = x.bytesV)
    (hr21 : sl.readReg64 .x21 = namePtr)
    (hr22 : sl.readReg64 .x22 = x.self)
    (hr23 : sl.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length)
    (hr24 : sl.readReg64 .x24 = ptr)
    (hr25 : sl.readReg64 .x25 = curBase + 32#64)
    (hr26 : sl.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48)) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) sl
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool lim (M.stepEvents evsPre st0) sl)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal
  have hpre_next : ∀ p ∈ pre ++ [e], p.1 ≠ x.name := by
    intro p hp
    rcases List.mem_append.mp hp with hp0 | hp1
    · exact hpre_ne p hp0
    · rw [List.mem_singleton.mp hp1]; exact he_ne
  cases rest with
  | nil =>
    have hr26_48 : sl.readReg64 .x26 = 48#64 := hr26
    have hmiss_all : ∀ p ∈ x.dir.changed, p.1 ≠ x.name := by
      rw [hsplit]
      exact hpre_next
    apply sepWPp_cut_rebase_543 (mid := atOff543 244) hcrl_l
    dsimp +zetaDelta only [atOff543] at hpcl ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 244)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
    · subst hP2
      conv => arg 4; rw [← hs2]
      let _ := hr25
      let _ := hr26_48
      apply sepWPp_eq_pre
      · exact step_miss_543 hgrow x st0 evsPre R s0 s2 cap ptr namePtr bCap bPtr
          hstk hstk_max hlen32 hmiss_all hFitTail hWrap hcrl_s2
          (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunl)
          (by
            have hsp_eq : s2.sp = sl.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hspal)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspl)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htrl)
          ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.2⟩
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr19)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr20)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr21)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr22)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr23)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr24)
      · try dsimp +zetaDelta only [savedSlots, bytesAt]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        sep_ac_rfl
  | cons e' rest' =>
    have hsub_len : rest'.length + 2 ≤ x.dir.changed.length := by
      rw [hsplit, List.length_append, List.length_cons, List.length_cons]
      omega
    have hmul_lt : ((e' :: rest').length + 1) * 48 < 2 ^ 64 := by
      let _ := hsub_len
      rw [List.length_cons]
      omega
    have hne_48 : (BitVec.ofNat 64 (((e' :: rest').length + 1) * 48) == 48#64) = false := by
      apply beq_false_of_ne
      intro heq
      have h1 := congrArg BitVec.toNat heq
      rw [ofNat_toNat_of_lt hmul_lt, List.length_cons] at h1
      have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
      rw [h48] at h1
      omega
    have hx26_sub :
        BitVec.ofNat 64 (((e' :: rest').length + 1) * 48) - 48#64 =
          BitVec.ofNat 64 ((e' :: rest').length * 48) :=
      sub48_latch (e' :: rest').length hmul_lt
    have hx25_add :
        curBase + 80#64 =
          ptr + BitVec.ofNat 64 ((pre ++ [e]).length * 48) + 32#64 := by
      have hm : (pre ++ [e]).length * 48 = pre.length * 48 + 48 := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [hcur'.out, hm, BitVec.ofNat_add]
      bv_omega
    apply sepWPp_cut_rebase_543 (mid := atOff543 132) hcrl_l
    dsimp +zetaDelta only [atOff543] at hpcl ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 132)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
    · subst hP2
      conv => arg 4; rw [← hs2]
      let _ := hne_48
      let _ := hx25_add
      let _ := hx26_sub
      let _ := hr25
      let _ := hr26
      apply sepWPp_eq_pre
      · exact hnext s2 (List.cons_ne_nil _ _)
          (by rw [hsplit, List.append_assoc, List.singleton_append])
          hpre_next hcrl_s2
          (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunl)
          (by
            have hsp_eq : s2.sp = sl.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hspal)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspl)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htrl)
          ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.2⟩
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr19)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr20)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr21)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr22)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr23)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr24)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_add)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx26_sub)
      · try dsimp +zetaDelta only [savedSlots, bytesAt]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        sep_ac_rfl

/-- Post-`bcmp` branch `+160` on Block `543`: dispatches to `step_hit_543` on `e.1 = x.name`
or to `step_latch_543` on `e.1 ≠ x.name`. -/
private theorem step_after_bcmp_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 s1 sm : State)
    (cap ptr namePtr bCap bPtr curBase eCap ePtr : BitVec 64)
    (pre : List (List (BitVec 8) × List (BitVec 8)))
    (e : List (BitVec 8) × List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8)))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hsp_align0 : s0.spAligned = true)
    (hsplit : x.dir.changed = pre ++ e :: rest)
    (hpre_ne : ∀ p ∈ pre, p.1 ≠ x.name)
    (hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)))
    (hle_c : x.dir.changed.length ≤ cap.toNat)
    (hbnd_c : cap.toNat * 48 < 2 ^ 63)
    (hptr_c : ptr ≠ 0)
    (hcap_c : cap ≠ 0)
    (hvbuf_close :
      (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
        ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
        vecU8Heap A.repAlloc eCap ePtr e.1 ∗
        vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ⊢
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed)
    (hnext :
      let cal := max growStk extHookStack
      ∀ (s2 : State),
        rest ≠ [] →
        x.dir.changed = (pre ++ [e]) ++ rest →
        (∀ p ∈ pre ++ [e], p.1 ≠ x.name) →
        LibsignalCodeRoLoaded lsmpl s2.mem →
        s2.pc = atOff543 132 →
        s2.status = .Running →
        s2.spAligned = true →
        s2.sp = s0.sp - 80#64 →
        s2.trace = s0.trace →
        PresHigh s0 s2 →
        s2.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
        s2.readReg64 .x20 = x.bytesV →
        s2.readReg64 .x21 = namePtr →
        s2.readReg64 .x22 = x.self →
        s2.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
        s2.readReg64 .x24 = ptr →
        s2.readReg64 .x25 = ptr + BitVec.ofNat 64 ((pre ++ [e]).length * 48) + 32#64 →
        s2.readReg64 .x26 = BitVec.ofNat 64 (rest.length * 48) →
        SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s2
          ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2)
          (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
          (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R))
    (hsp_s1 : s1.sp = s0.sp - 80#64)
    (htr_s1 : s1.trace = s0.trace)
    (hcrlm : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpcm : sm.pc = atOff543 160)
    (hrunm : sm.status = .Running)
    (hspam : sm.spAligned = true)
    (hspm : sm.sp = s1.sp)
    (htr_sm0 : sm.trace = s1.trace)
    (hbcmp_iff : (sm.readReg64 .x0).setWidth 32 = 0#32 ↔ e.1 = x.name)
    (hhigh_sm : PresHigh s0 sm)
    (hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20_sm : sm.readReg64 .x20 = x.bytesV)
    (hx21_sm : sm.readReg64 .x21 = namePtr)
    (hx22_sm : sm.readReg64 .x22 = x.self)
    (hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length)
    (hx24_sm : sm.readReg64 .x24 = ptr)
    (hx25_sm : sm.readReg64 .x25 = curBase + 32#64)
    (hx26_sm : sm.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48))
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) sm
      ((ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
        (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
        ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
        vecU8Rest A.repAlloc eCap ePtr e.1 ∗
        vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBufRest A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
        savedSlots s0 ∗
        A.pool lim (M.stepEvents evsPre st0) sm)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal
  have hstk_back :
      memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
        stackAt s1.sp extHookStack =
        stackAt (s0.sp - 80#64) cal := by
    rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
  by_cases heq_name : e.1 = x.name
  · have hw0_z :
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = true :=
      w0_cbnz_zero (hbcmp_iff.mpr heq_name)
    have hhit : ¬ ∀ p ∈ x.dir.changed, p.1 ≠ x.name := by
      intro hall
      exact hall e (by rw [hsplit]; simp) heq_name
    have hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest := by
      unfold DirGhost.put
      dsimp only
      rw [hsplit]
      rcases e with ⟨ek, ev⟩
      dsimp only at heq_name
      subst heq_name
      exact setOrPush_hit_middle x.name x.bytes ev pre rest hpre_ne
    have hlen_hit : x.dir.changed.length = (pre ++ (x.name, x.bytes) :: rest).length := by
      simp only [hsplit, List.length_append, List.length_cons]
    apply sepWPp_cut_rebase_543 (mid := atOff543 164) hcrlm
    dsimp +zetaDelta only [atOff543] at hpcm ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 164)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
    · subst hP2
      conv => arg 4; rw [← hs2]
      let _ := hw0_z
      let _ := hx22_sm
      let _ := hx23_sm
      let _ := hx24_sm
      let _ := hx26_sm
      let _ := hvbuf_close
      have hprep_hit :
          (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Rest A.repAlloc eCap ePtr e.1 ∗
            vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
            A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBufRest A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2 ⊢
          ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
              A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
              vecU8 A.repAlloc curBase x.name ∗
              ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
              ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
              vecU8Heap A.repAlloc oldCap oldPtr e.2 ∗
              arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
                ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A.repAlloc namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool lim (M.stepEvents evsPre st0) s2 := by
        have ha32 : curBase + 24#64 + 8#64 = curBase + 32#64 := by bv_omega
        have ha40 : curBase + 24#64 + 16#64 = curBase + 40#64 := by bv_omega
        have hv2 : vecU8 A.repAlloc (curBase + 24#64) e.2 =
            ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
              ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
              ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
              vecU8Heap A.repAlloc oldCap oldPtr e.2 := by
          unfold vecU8
          simp only [vecU8At_eq_header_heap, ha32, ha40]
        rw [hv2]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine Entails.sepExists_elim fun oldCap =>
          Entails.trans ?_ (Entails.sepExists_intro oldCap)
        refine Entails.sepExists_elim fun oldPtr =>
          Entails.trans ?_ (Entails.sepExists_intro oldPtr)
        have he_assemble :
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              ((ePtr ↦ₛ e.1) ∗ vecU8Rest A.repAlloc eCap ePtr e.1) ⊢
              vecU8 A.repAlloc curBase x.name := by
          rw [← vecU8Heap_expose_bytes, heq_name]
          exact vecU8_of_header_heap A.repAlloc curBase eCap ePtr x.name
        rw [← hstk_back, ← hlen_hit, nameBuf_expose_bytes A.repAlloc namePtr x.name]
        rw [show ∀ (B1 B2 StkE C0 C1 C2 ER O0 O1 O2 OH L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
              B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ (O0 ∗ O1 ∗ O2 ∗ OH) ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
              (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER)) ∗
              (S0 ∗ S1 ∗ S2 ∗ L0 ∗ P0 ∗ O0 ∗ O1 ∗ O2 ∗ OH ∗ R0 ∗ M0 ∗
                Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
              intros; sep_ac_rfl]
        exact Entails.trans (sepConj_mono_left he_assemble) (entails_eq (by sep_ac_rfl))
      apply sepWPp_eq_pre
      · apply sepWPp_weaken_pre hprep_hit
        have hpull_ex1 : ∀ (Φ : BitVec 64 → SepProp), (∃∗ a, Φ a) = (∃∗ a, Φ a) ∗ emp :=
          fun _ => (sepConj_emp _).symm
        rw [hpull_ex1]
        refine sepWPp_exists_left fun oldCap => ?_
        rw [sepConj_emp, hpull_ex1]
        refine sepWPp_exists_left fun oldPtr => ?_
        rw [sepConj_emp]
        exact step_hit_543 hC x st0 evsPre R s0 s2 pre rest e.2
          cap ptr curBase namePtr bCap bPtr oldCap oldPtr
          hstk hstk_max hname32 hhit hWrap hput_eq hcur'.out
          (by rw [← hlen_hit]; exact hle_c) hbnd_c hptr_c hcap_c
          hsp_align0 hcrl_s2
          (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
          (by
            have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hspam)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspm.trans hsp_s1)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htr_sm0.trans htr_s1)
          ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.2⟩
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx19_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx20_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx21_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_sm)
      · try dsimp +zetaDelta only [savedSlots, bytesAt]
        try rw [hsp_s1]
        repeat rw [ite_false_eq]
        repeat rw [bv_sub_eq_add_neg64]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        sep_ac_rfl
  · have hw0_nz :
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
      w0_cbnz_nonzero (fun hz => heq_name (hbcmp_iff.mp hz))
    apply sepWPp_cut_rebase_543 (mid := atOff543 120) hcrlm
    dsimp +zetaDelta only [atOff543] at hpcm ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 120)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
    · subst hP2
      conv => arg 4; rw [← hs2]
      let _ := hw0_nz
      have hclose_miss :
          (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Rest A.repAlloc eCap ePtr e.1 ∗
            vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
            A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBufRest A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2 ⊢
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2 := by
        rw [← hstk_back, nameBuf_expose_bytes A.repAlloc namePtr x.name]
        rw [show ∀ (B1 B2 StkE C0 C1 C2 ER VO L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
              B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
              (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER) ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗
              (S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
              intros; sep_ac_rfl]
        rw [← vecU8Heap_expose_bytes]
        exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by sep_ac_rfl))
      apply sepWPp_eq_pre
      · apply sepWPp_weaken_pre hclose_miss
        exact step_latch_543 hgrow x st0 evsPre R s0 cap ptr namePtr bCap bPtr curBase
          pre e rest hstk hstk_max hlen32 hFitTail hWrap hsplit hpre_ne hcur' hnext
          s2 heq_name hcrl_s2
          (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
          (by
            have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hspam)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspm.trans hsp_s1)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htr_sm0.trans htr_s1)
          ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.1,
           by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.2⟩
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx19_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx20_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx21_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx22_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx23_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx24_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_sm)
          (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx26_sm)
      · try dsimp +zetaDelta only [savedSlots, bytesAt]
        try rw [hsp_s1]
        repeat rw [ite_false_eq]
        repeat rw [bv_sub_eq_add_neg64]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        sep_ac_rfl

/-- Single iteration of the search loop body starting at `+132` on Block `543` for `e :: rest`. -/
private theorem step_loop_body_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hsp_align0 : s0.spAligned = true)
    (e : List (BitVec 8) × List (BitVec 8))
    (rest pre : List (List (BitVec 8) × List (BitVec 8)))
    (hnext :
      let cal := max growStk extHookStack
      ∀ (s2 : State),
        rest ≠ [] →
        x.dir.changed = (pre ++ [e]) ++ rest →
        (∀ p ∈ pre ++ [e], p.1 ≠ x.name) →
        LibsignalCodeRoLoaded lsmpl s2.mem →
        s2.pc = atOff543 132 →
        s2.status = .Running →
        s2.spAligned = true →
        s2.sp = s0.sp - 80#64 →
        s2.trace = s0.trace →
        PresHigh s0 s2 →
        s2.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
        s2.readReg64 .x20 = x.bytesV →
        s2.readReg64 .x21 = namePtr →
        s2.readReg64 .x22 = x.self →
        s2.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
        s2.readReg64 .x24 = ptr →
        s2.readReg64 .x25 = ptr + BitVec.ofNat 64 ((pre ++ [e]).length * 48) + 32#64 →
        s2.readReg64 .x26 = BitVec.ofNat 64 (rest.length * 48) →
        SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s2
          ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s2)
          (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
          (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R))
    (s : State)
    (hsplit : x.dir.changed = pre ++ e :: rest)
    (hpre_ne : ∀ p ∈ pre, p.1 ≠ x.name)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 132)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length)
    (hx24 : s.readReg64 .x24 = ptr)
    (hx25 : s.readReg64 .x25 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 ((e :: rest).length * 48))
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool lim (M.stepEvents evsPre st0) s)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
    intro cal
    have hbcmp := bcmp_lscro_ok_at_dirPutStr_543 H hBcmp
    generalize hcur_raw : ptr + BitVec.ofNat 64 (pre.length * 48) = curBase at hx25
    have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur_raw.symm⟩
    clear hcur_raw
    have hlen_split : x.dir.changed.length = pre.length + (rest.length + 1) := by
      rw [hsplit, List.length_append, List.length_cons]
    let _ := hlen_split
    have hcap_ne : ∀ (h : x.dir.changed.length ≤ cap.toNat), cap ≠ 0 := by
      intro h h0
      subst h0
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      omega
    have hvbuf_open :
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ⊢
          ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
            (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
              (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A.repAlloc eCap ePtr e.1 ∗
              vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
              A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
              arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48)) := by
      unfold vecBuf
      refine Entails.pure_left fun ⟨hle_c, hbnd_c, hptr_c⟩ => ?_
      have hcn := hcap_ne hle_c
      simp only [hcn, ↓reduceIte]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c, hcn⟩ ?_
      have happ : arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            dirEntryAt A.repAlloc e curBase ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
      rw [happ]
      unfold dirEntryAt
      have hv1 : vecU8 A.repAlloc curBase e.1 =
          ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A.repAlloc eCap ePtr e.1 := by
        unfold vecU8
        simp only [vecU8At_eq_header_heap]
      rw [hv1]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun eCap => Entails.trans ?_ (Entails.sepExists_intro eCap)
      refine Entails.sepExists_elim fun ePtr => Entails.trans ?_ (Entails.sepExists_intro ePtr)
      exact entails_eq (by sep_ac_rfl)
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvbuf_open))))
    rw [show ∀ (A1 A2 A3 P0 E1 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ E1) ∗ Z =
            P0 ∗ E1 ∗ A1 ∗ A2 ∗ A3 ∗ Z from
          fun _ _ _ _ _ _ => by sep_ac_rfl]
    refine sepWPp_pure_left fun ⟨hle_c, hbnd_c, hptr_c, hcap_c⟩ => ?_
    refine sepWPp_exists_left fun eCap => ?_
    try simp only [sepConj_assoc]
    refine sepWPp_exists_left fun ePtr => ?_
    try simp only [sepConj_assoc]
    have he_len_pull :
        vecU8Heap A.repAlloc eCap ePtr e.1 =
          ⌜e.1.length < 2 ^ 63⌝ ∗ vecU8Heap A.repAlloc eCap ePtr e.1 := by
      apply Entails.antisymm
      · unfold vecU8Heap
        refine Entails.pure_left fun ⟨h1, h2, h3⟩ => ?_
        exact Entails.pure_right (by omega) (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
      · exact Entails.pure_left fun _ => Entails.refl _
    rw [he_len_pull]
    rw [show ∀ (C0 C1 C2 P0 H1 Z : SepProp),
          C0 ∗ C1 ∗ C2 ∗ (P0 ∗ H1) ∗ Z = P0 ∗ C0 ∗ C1 ∗ C2 ∗ H1 ∗ Z from
          fun _ _ _ _ _ _ => by sep_ac_rfl]
    refine sepWPp_pure_left fun he_len63 => ?_
    let _ := he_len63
    have hvbuf_close :
        (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
          ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
          vecU8Heap A.repAlloc eCap ePtr e.1 ∗
          vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ⊢
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed := by
      have he1 := vecU8_of_header_heap A.repAlloc curBase eCap ePtr e.1
      unfold vecBuf
      simp only [hcap_c, ↓reduceIte]
      have happ : arrayAt (dirEntryAt A.repAlloc) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            (vecU8 A.repAlloc curBase e.1 ∗ vecU8 A.repAlloc (curBase + 24#64) e.2) ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
        unfold dirEntryAt
        sep_ac_rfl
      rw [happ]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c⟩ ?_
      rw [show (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A.repAlloc eCap ePtr e.1 ∗
            vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
            A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) =
          ((curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A.repAlloc eCap ePtr e.1) ∗
          (A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48)) by sep_ac_rfl]
      exact Entails.trans (sepConj_mono_left he1) (entails_eq (by sep_ac_rfl))
    by_cases hlen_eq : e.1.length = x.name.length
    · have hlen_beq :
          (BitVec.ofNat 64 e.1.length == BitVec.ofNat 64 x.name.length) = true := by
        rw [hlen_eq]; exact beq_self_eq_true _
      apply sepWPp_cut_rebase_543 (mid := lsρ cliBcmpName) hcrl
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps_sync_pool (lsρ cliBcmpName)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        conv => arg 4; rw [← hs1]
        let _ := hlen_beq
        have hsp_s1 : s1.sp = s0.sp - 80#64 := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp
        have htr_s1 : s1.trace = s0.trace := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr
        have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
          ofNat_toNat_of_lt (by omega)
        rw [vecU8Heap_expose_bytes A.repAlloc eCap ePtr e.1,
          nameBuf_expose_bytes A.repAlloc namePtr x.name,
          stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
        apply call_lscro_wpp hbcmp ⟨ePtr, false, e.1, namePtr, false, x.name⟩
          (ret_pc := atOff543 160)
          (F := (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Rest A.repAlloc eCap ePtr e.1 ∗
            vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
            A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
            arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            nameBufRest A.repAlloc namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0 ∗
            A.pool lim (M.stepEvents evsPre st0) s1)
          (hcrl := hcrl_s1)
          (hpc := by rw [hs1]; rfl)
          (hrun := by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
          (hsp_align := by
            have hsp_eq : s1.sp = s.sp := by rw [hs1]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hsp_align)
          (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (hspec := rfl)
          (hφ := ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21,
                  by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21,
                  by rw [hs1]; simp only [wp_norm, arm64_norm]; omega,
                  hlen_eq.symm⟩)
          (hP := by
            try dsimp +zetaDelta only [savedSlots, bytesAt]
            repeat rw [ite_false_eq]
            repeat rw [bv_sub_eq_add_neg64]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            sep_ac_rfl)
          (hpan := fun _ => panic_false_wpp_543)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro sm hpcm hrunm hspm hcsm hcrlm
        dsimp only [withVmPreserved, cliBcmpSpec]
        conv => arg 4; rw [bytesAt_false, bytesAt_false]
        try simp only [sepConj_assoc]
        refine sepWPp_pure_left fun hvm_sm => ?_
        refine sepWPp_pure_left fun ⟨hbcmp_iff, htr_sm0⟩ => ?_
        conv => arg 4; rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evsPre st0) hvm_sm]
        have hhigh_s1 : PresHigh s0 s1 :=
          ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
        have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
        have hspam : sm.spAligned = true := by
          have hsp_eq' : sm.sp = s.sp := hspm.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm])
          simpa only [State.spAligned, hsp_eq'] using hsp_align
        have hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
          hcsm.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx19)
        have hx20_sm : sm.readReg64 .x20 = x.bytesV :=
          hcsm.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx20)
        have hx21_sm : sm.readReg64 .x21 = namePtr :=
          hcsm.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21)
        have hx22_sm : sm.readReg64 .x22 = x.self :=
          hcsm.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx22)
        have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length :=
          hcsm.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx23)
        have hx24_sm : sm.readReg64 .x24 = ptr :=
          hcsm.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx24)
        have hx25_sm : sm.readReg64 .x25 = curBase + 32#64 :=
          hcsm.2.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25)
        have hx26_sm : sm.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48) :=
          hcsm.2.2.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26)
        apply sepWPp_eq_pre
        · exact step_after_bcmp_543 hC hgrow x st0 evsPre R s0 s1 sm
            cap ptr namePtr bCap bPtr curBase eCap ePtr pre e rest
            hstk hstk_max hname32 hlen32 hFitTail hWrap hsp_align0
            hsplit hpre_ne hcur' hle_c hbnd_c hptr_c hcap_c hvbuf_close hnext
            hsp_s1 htr_s1 hcrlm hpcm hrunm hspam hspm htr_sm0 hbcmp_iff
            hhigh_sm hx19_sm hx20_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm
        · dsimp +zetaDelta only [savedSlots]
          sep_ac_rfl
    · have he_ne_name : e.1 ≠ x.name := fun h => hlen_eq (congrArg List.length h)
      have hlen_beq :
          (BitVec.ofNat 64 e.1.length == BitVec.ofNat 64 x.name.length) = false := by
        apply beq_false_of_ne
        intro heq_bv
        have h1 := congrArg BitVec.toNat heq_bv
        rw [ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)] at h1
        exact hlen_eq h1
      apply sepWPp_cut_rebase_543 (mid := atOff543 120) hcrl
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 120)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        conv => arg 4; rw [← hs1]
        let _ := hlen_beq
        let _ := hbcmp
        have hclose_len :
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A.repAlloc eCap ePtr e.1 ∗
              vecU8 A.repAlloc (curBase + 24#64) e.2 ∗
              A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
              arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48) ∗
              (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A.repAlloc namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool lim (M.stepEvents evsPre st0) s1 ⊢
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A.repAlloc namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool lim (M.stepEvents evsPre st0) s1 := by
          rw [show ∀ (C0 C1 C2 EH VO L0 P0 R0 M0 Z : SepProp),
                C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗ Z =
                  (C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗ Z from
                fun _ _ _ _ _ _ _ _ _ _ => by sep_ac_rfl]
          exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by sep_ac_rfl))
        apply sepWPp_eq_pre
        · apply sepWPp_weaken_pre hclose_len
          exact step_latch_543 hgrow x st0 evsPre R s0 cap ptr namePtr bCap bPtr curBase
            pre e rest hstk hstk_max hlen32 hFitTail hWrap hsplit hpre_ne hcur' hnext
            s1 he_ne_name hcrl_s1
            (by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (by
              have hsp_eq : s1.sp = s.sp := by rw [hs1]; try simp only [wp_norm, arm64_norm]
              simpa only [State.spAligned, hsp_eq] using hsp_align)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr)
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
             by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
             by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx19)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx20)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx22)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx23)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx24)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26)
        · try dsimp +zetaDelta only [savedSlots, bytesAt]
          repeat rw [bv_sub_eq_add_neg64]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          sep_ac_rfl

/-- Loop invariant and induction over `suf` starting at `+132` on Block `543`. -/
theorem step_loop_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hsp_align0 : s0.spAligned = true)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    let cal := max growStk extHookStack
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ p ∈ pre, p.1 ≠ x.name) →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = atOff543 132 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 80#64 →
      s.trace = s0.trace →
      PresHigh s0 s →
      s.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x20 = x.bytesV →
      s.readReg64 .x21 = namePtr →
      s.readReg64 .x22 = x.self →
      s.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
      s.readReg64 .x24 = ptr →
      s.readReg64 .x25 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 →
      s.readReg64 .x26 = BitVec.ofNat 64 (suf.length * 48) →
      SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
        ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A.repAlloc namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool lim (M.stepEvents evsPre st0) s)
        (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
        (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact (hsuf rfl).elim
  | cons e rest ih =>
    intro pre s _hsuf hsplit hpre_ne hcrl hpc hrun hsp_align hsp htr hhigh
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
    exact step_loop_body_543 hC hBcmp hgrow x st0 evsPre R s0 cap ptr namePtr bCap bPtr
      hstk hstk_max hname32 hlen32 hFitTail hWrap hsp_align0 e rest pre (ih (pre ++ [e])) s
      hsplit hpre_ne hcrl hpc hrun hsp_align hsp htr hhigh
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hlr_ls

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux2
