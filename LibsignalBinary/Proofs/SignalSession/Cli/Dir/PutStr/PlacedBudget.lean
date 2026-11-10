/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux2
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `[LibsignalPlacement]` `<signal_session::stores::Dir>::put::<&str>` (Block 543)

Verifies the loop preheader and top-level block-543 and caller-transferable `dirPutStrSpecPlaced`
contracts for `Dir::put::<&str>` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ
)
open CryptoVerification.RustHeap (LayoutOk vecAt vecBuf vecHeader vecOf vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyBytesAtSpec sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (
  DirGhost DirPutStrGhost cliBcmpName cliBcmpSpec dirAt dirEntryAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_543 lsProg_543)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  CliPanicHooksPlaced ls_transfer_lscro
)
open CryptoVerification.SignalSession.Cli.PutStr.Helpers (
  PresHigh beq_ofNat_zero_eq_false layoutOk_u8_of_lt memRegion_le_two_pow_64_of_pointsTo64
  nameBuf nameBuf_of_nil nameBuf_of_nonempty ofNat_eq_of_toNat_eq ofNat_toNat_of_lt preheader_mul48
  savedSlots sepWPp_pure_left sepWPp_weaken_pre spAligned_of_sub80 stackAt_dirPutStr_split
  stackAt_split_sub vecU8At_eq_header_heap vecU8Heap
)
open CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers (
  atOff543 sepWPp_cut_rebase_543 sepWPp_eq_pre stackAt_split_sp
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv
  rustAllocEvents rustCliAllocNoOomExternSpecWithStack
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced dirPutStrSpecPlaced growOneDirSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (
  DirPutStrEnv DirPutStrPanicPlaced DirPutStrPostPlaced allocNoOom_ok_at_dirPutStr_543
  call_lscro_wpp dirPutStrEnv_of_nil dirPutStrEnv_of_nonempty memcpy_bytesAt_lscro_ok_at_543
  panic_false_wpp_543 session2ShimBudgetSpecX shim_ok_at_dirPutStr_543 step_miss_543
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux2 (step_loop_543)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem entails_eq' {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem satisfies_eq' {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

private theorem bv_sub_eq_add_neg64' (a b : BitVec 64) : a - b = a + (-b) :=
  BitVec.sub_eq_add_neg a b

private theorem sp_slot_norm (sp : BitVec 64) :
    sp + (-80#64 + 8#64) = sp + (-72#64) ∧
    sp + (-80#64 + 16#64) = sp + (-64#64) ∧
    sp + (-80#64 + 24#64) = sp + (-56#64) ∧
    sp + (-80#64 + 32#64) = sp + (-48#64) ∧
    sp + (-80#64 + 40#64) = sp + (-40#64) ∧
    sp + (-80#64 + 48#64) = sp + (-32#64) ∧
    sp + (-80#64 + 56#64) = sp + (-24#64) ∧
    sp + (-80#64 + 64#64) = sp + (-16#64) ∧
    sp + (-80#64 + 72#64) = sp + (-8#64) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Shared loop preheader `+104..+116` on Block `543` when `x.dir.changed = e0 :: rest0`. -/
private theorem step_preheader_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 s : State)
    (e0 : List (BitVec 8) × List (BitVec 8))
    (rest0 : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hchanged : x.dir.changed = e0 :: rest0)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hsp_align0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 104)
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
  apply sepWPp_cut_rebase_543 (mid := atOff543 132) hcrl
  dsimp +zetaDelta only [atOff543] at hpc ⊢
  wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 132)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
  · subst hP1
    conv => arg 4; rw [← hs1]
    have hx25_init :
        ptr + 32#64 =
          ptr + BitVec.ofNat 64 (([] : List (List (BitVec 8) × List (BitVec 8))).length * 48) + 32#64 := by
      change ptr + 32#64 = ptr + 0#64 + 32#64
      bv_omega
    have hlen_lt : (e0 :: rest0).length < 2 ^ 32 := hchanged ▸ hlen32
    have hx26_init :
        ((BitVec.ofNat 64 (e0 :: rest0).length +
            BitVec.ofNat 64 (2 * (e0 :: rest0).length)) <<< 4) =
          BitVec.ofNat 64 ((e0 :: rest0).length * 48) := by
      have h2mul :
          BitVec.ofNat 64 (2 * (e0 :: rest0).length) =
            BitVec.ofNat 64 (e0 :: rest0).length <<< 1 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
      rw [h2mul]
      exact preheader_mul48 _
    let _ := hx23
    let _ := hx24
    let _ := hx25_init
    let _ := hx26_init
    apply sepWPp_eq_pre
    · exact step_loop_543 hC hBcmp hgrow x st0 evsPre R s0 cap ptr namePtr bCap bPtr
        hstk hstk_max hname32 hlen32 hFitTail hWrap hsp_align0 hlr_ls (e0 :: rest0) [] s1
        (List.cons_ne_nil _ _)
        (by simpa only [List.nil_append] using hchanged)
        (fun _ hm => (List.not_mem_nil hm).elim)
        hcrl_s1
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
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25_init)
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; exact hx26_init)
    · try dsimp +zetaDelta only [savedSlots, bytesAt, cal]
      try simp only [sp_slot_norm]
      try rw [emp_sepConj]
      try rw [sepConj_emp]
      try simp only [wp_norm, arm64_norm]
      try rw [Nat.mul_comm 48]
      try sep_ac_rfl

/-- Envelope-polymorphic `Dir::put::<&str>` contract on Block 543 for any `PutStrEnv`
containing `DirPutStrEnv`. -/
theorem dirPutStr_placed_ok_of_deps_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hPutStrEnv : ∀ dir name bytes evs, DirPutStrEnv dir name bytes evs →
      PutStrEnv dir name bytes evs)
    (hC : AllocContractsXCliPlaced A lim H)
    (_hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543) (dirPutStrSpecPlaced A lim PutStrEnv stk) := by
  have hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk) :=
    ls_transfer_lscro (callerProg := lsProg_543 H) hGrow (by decide) hjGrow hjGrow_unmut
  clear hGrow
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align0
  rw [show lsmpl.base 543 = atOff543 0 by dsimp [atOff543]; rw [BitVec.add_zero]; rfl] at hpc
  obtain ⟨hcrl0, hpre_inner⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [dirPutStrSpecPlaced] at hpre_inner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_inner
  rcases hpre_inner with ⟨⟨hx0, hx1, hx2_nat, hx3, hname32, hlen32, hFit0, hlr_ls⟩, hmem_spatial⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.name.length :=
    ofNat_eq_of_toNat_eq hx2_nat
  have hstk_max : stk ≤ 2 ^ 64 := by
    have hm1 : s0.mem ⊨ vecU8 A.repAlloc x.bytesV x.bytes ∗ stackAt s0.sp stk ∗
        (dirAt A.repAlloc x.self x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
          A.pool lim st0 s0 ∗ R) :=
      satisfies_eq' (by sep_ac_rfl) hmem_spatial
    unfold vecU8 at hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
    rcases hm1 with ⟨bc, bp, hmb⟩
    rw [vecU8At_eq_header_heap] at hmb
    unfold stackAt at hmb
    have hmb' : s0.mem ⊨ (x.bytesV ↦₆₄ bc) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
        (((x.bytesV + 8#64) ↦₆₄ bp) ∗ ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bc bp x.bytes ∗
          (dirAt A.repAlloc x.self x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
            A.pool lim st0 s0 ∗ R)) :=
      satisfies_eq' (by sep_ac_rfl) hmb
    exact memRegion_le_two_pow_64_of_pointsTo64 hmb'
  let cal := max growStk extHookStack
  unfold dirAt vecOf vecAt vecHeader at hmem_spatial
  unfold vecU8 at hmem_spatial
  rw [stackAt_dirPutStr_split s0.sp (cal := cal) hstk hstk_max] at hmem_spatial
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_spatial
  rcases hmem_spatial with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, bCap, bPtr, cap, ptr, hm_init⟩
  rw [vecU8At_eq_header_heap] at hm_init
  have hm_ord : s0.mem ⊨
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        A.pool lim st0 s0) ∗ R :=
    satisfies_eq' (by sep_ac_rfl) hm_init
  refine ⟨_, R, hm_ord, ?_⟩
  clear hpre hm_init hm_ord
  have hshim := shim_ok_at_dirPutStr_543 hC
  have halloc := allocNoOom_ok_at_dirPutStr_543 hC
  have hmemcpy := memcpy_bytesAt_lscro_ok_at_543 A lim H hC hRO x.nameRo
  by_cases hnil : x.name = []
  · have hx2_zero : s0.readReg64 .x2 = 0#64 := by
      rw [hx2, hnil]; rfl
    have hWrapNil : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
        PutStrEnv x.dir x.name x.bytes ([] ++ evsTail) :=
      fun evsTail ht => hPutStrEnv x.dir x.name x.bytes ([] ++ evsTail) (dirPutStrEnv_of_nil hnil ht)
    have hFitTailNil : FitsEnv M lim (M.stepEvents [] st0) (DirPutTailEnv x.dir x.name) := by
      rw [M.stepEvents_nil]
      unfold FitsEnv at hFit0 ⊢
      intro evsTail ht
      simpa only [List.nil_append] using hFit0 ([] ++ evsTail) (hWrapNil evsTail ht)
    have hname_fold :
        bytesAt x.nameRo x.nameA x.name ⊢
          bytesAt x.nameRo x.nameA x.name ∗ nameBuf A.repAlloc 1#64 x.name := by
      rw [hnil]
      exact Entails.trans (entails_eq' (sepConj_emp _).symm)
        (sepConj_mono_right (nameBuf_of_nil A.repAlloc))
    cases hdir_cases : x.dir.changed with
    | nil =>
      apply sepWPp_cut_rebase_543 (mid := atOff543 244) hcrl0
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 244)
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        conv => arg 4; rw [← hs1]
        let _ := hC
        let _ := hBcmp
        let _ := hshim
        let _ := halloc
        let _ := hmemcpy
        let _ := hx1
        let _ := hx2
        let _ := hx2_zero
        let _ := hname32
        rw [← hdir_cases]
        apply sepWPp_eq_pre
        · exact step_miss_543 hgrow x st0 [] R s0 s1 cap ptr 1#64 bCap bPtr
            hstk hstk_max hlen32
            (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
            hFitTailNil hWrapNil
            hcrl_s1
            (by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (spAligned_of_sub80 hsp_align0 (by rw [hs1]; try simp only [wp_norm, arm64_norm]))
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
            (by rw [hs1]; simp only [wp_norm, arm64_norm]; rw [hnil]; rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
        · rw [M.stepEvents_nil]
          try dsimp +zetaDelta only [savedSlots, bytesAt, cal]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          sep_ac_rfl
    | cons e0 rest0 =>
      have hlen_pos : 0 < (e0 :: rest0).length := by simp
      have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
        beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
      apply sepWPp_cut_rebase_543 (mid := atOff543 104) hcrl0
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 104)
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        conv => arg 4; rw [← hs1]
        let _ := hshim
        let _ := halloc
        let _ := hmemcpy
        let _ := hx1
        let _ := hx2
        let _ := hx2_zero
        let _ := hlen_nz
        rw [← hdir_cases]
        apply sepWPp_eq_pre
        · exact step_preheader_543 hC hBcmp hgrow x st0 [] R s0 s1 e0 rest0 cap ptr 1#64 bCap bPtr
            hstk hstk_max hname32 hlen32 hdir_cases hFitTailNil hWrapNil hsp_align0 hcrl_s1
            (by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (spAligned_of_sub80 hsp_align0 (by rw [hs1]; try simp only [wp_norm, arm64_norm]))
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by rw [hs1]; try simp only [wp_norm, arm64_norm],
             by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
            (by rw [hs1]; simp only [wp_norm, arm64_norm]; rw [hnil]; rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm])
        · rw [M.stepEvents_nil]
          try dsimp +zetaDelta only [savedSlots, bytesAt, cal]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          sep_ac_rfl
  · have hname_pos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx2_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hname_pos (by omega)
    have hname_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    have hlay_name : LayoutOk x.name.length 1 :=
      layoutOk_u8_of_lt hname_pos (by omega)
    let evsAlloc := rustAllocEvents x.name.length 1
    have hWrapNe : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
        PutStrEnv x.dir x.name x.bytes (evsAlloc ++ evsTail) :=
      fun evsTail ht =>
        hPutStrEnv x.dir x.name x.bytes (evsAlloc ++ evsTail) (dirPutStrEnv_of_nonempty hnil ht)
    have hFitSeq : FitsEnv M lim st0 (SeqEnv (· = evsAlloc) (DirPutTailEnv x.dir x.name)) := by
      unfold FitsEnv at hFit0 ⊢
      intro evs hs
      refine hFit0 evs (hPutStrEnv x.dir x.name x.bytes evs ?_)
      unfold DirPutStrEnv
      split
      · rename_i hc; exact (hnil hc).elim
      · exact hs
    have hFitAlloc : FitsEvents M lim st0 evsAlloc :=
      FitsEnv.eq_iff.mp (FitsEnv.seq_left hFitSeq)
    have hFitTailNe : FitsEnv M lim (M.stepEvents evsAlloc st0) (DirPutTailEnv x.dir x.name) :=
      FitsEnv.seq_right hFitSeq rfl
    apply sepWPp_cut_rebase_543 (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
    dsimp +zetaDelta only [atOff543] at hpc ⊢
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
      conv => arg 4; rw [← hs1]
      let _ := hx2_nz
      have hsp_s1 : s1.sp = s0.sp - 80#64 := by
        rw [hs1]; try simp only [wp_norm, arm64_norm]
      have hspa_s1 : s1.spAligned = true :=
        spAligned_of_sub80 hsp_align0 hsp_s1
      have htr_s1 : s1.trace = s0.trace := by
        rw [hs1]; try simp only [wp_norm, arm64_norm]
      rw [stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
      apply call_lscro_wpp hshim ()
        (ret_pc := atOff543 48)
        (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          bytesAt x.nameRo x.nameA x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0 ∗
          A.pool lim st0 s1)
        (hcrl := hcrl_s1)
        (hpc := by rw [hs1]; rfl)
        (hrun := by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := hspa_s1)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
        (hspec := rfl)
        (hφ := trivial)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, bytesAt, cal]
          try rw [hsp_s1]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          sep_ac_rfl)
        (hpan := fun _ => panic_false_wpp_543)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro s2 hpcs2 hruns2 hsps2 hcss2 hcrls2
      dsimp only [session2ShimBudgetSpecX]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun ⟨htr_s20, hvm_s20⟩ => ?_
      conv => arg 4; rw [← A.pool_of_vmPreserved (lim := lim) (st := st0) hvm_s20]
      have hsp_s2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp_s1
      have hspa_s2 : s2.spAligned = true := by
        simpa only [State.spAligned, hsps2] using hspa_s1
      have htr_s2 : s2.trace = s0.trace := htr_s20.trans htr_s1
      have hhigh_s2 : PresHigh s0 s2 :=
        (PresHigh.of_callee
          ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm],
           by rw [hs1]; try simp only [wp_norm, arm64_norm],
           by dsimp only [calleeSavedVRegs]; rw [hs1]; try simp only [wp_norm, arm64_norm]⟩
          hcss2)
      have hx19_s2 : s2.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
        hcss2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx2)
      have hx20_s2 : s2.readReg64 .x20 = x.bytesV :=
        hcss2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx3)
      have hx22_s2 : s2.readReg64 .x22 = x.self :=
        hcss2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx0)
      have hx23_s2 : s2.readReg64 .x23 = x.nameA :=
        hcss2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx1)
      let _ := hsp_s2
      let _ := hspa_s2
      apply sepWPp_cut_rebase_543 (mid := lsρ lsRustAllocSymCli) hcrls2
      dsimp +zetaDelta only [atOff543] at hpcs2 ⊢
      wp_steps_sync_pool (lsρ lsRustAllocSymCli)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s3 P3 hcrl_s3 ⟨hs3, hP3⟩
      · subst hP3
        conv => arg 4; rw [← hs3]
        have hsp_s3 : s3.sp = s1.sp := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hsps2
        have hspa_s3 : s3.spAligned = true := by
          simpa only [State.spAligned, hsp_s3] using hspa_s1
        have htr_s3 : s3.trace = s0.trace := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact htr_s2
        rw [← hsp_s3]
        apply call_lscro_wpp halloc (x.name.length, 1, st0)
          (ret_pc := atOff543 60)
          (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            bytesAt x.nameRo x.nameA x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s3.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0)
          (hcrl := hcrl_s3)
          (hpc := by rw [hs3]; rfl)
          (hrun := by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hruns2)
          (hsp_align := hspa_s3)
          (hlr := by rw [hs3]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
          (hspec := rfl)
          (hφ := ⟨by rw [hs3]; simp only [wp_norm, arm64_norm]; exact hname_toNat,
                  by rw [hs3]; try simp only [wp_norm, arm64_norm],
                  ⟨hlay_name, by decide⟩,
                  hFitAlloc,
                  by
                    have hlr3 : s3.readReg64 .lr = atOff543 60 := by
                      rw [hs3]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm]
                    rw [hlr3]
                    exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
                      543 60#64 (by decide) (by decide)⟩)
          (hP := by
            try dsimp +zetaDelta only [savedSlots, bytesAt, cal]
            try rw [hsp_s3]
            try rw [hsp_s1]
            repeat rw [bv_sub_eq_add_neg64']
            try simp only [sp_slot_norm]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try sep_ac_rfl)
          (hpan := fun _ => panic_false_wpp_543)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro s4 hpcs4 hruns4 hsps4 hcss4 hcrls4
        dsimp only [rustAllocNoOomExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
          rustCliAllocNoOomExternSpecWithStack]
        simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        refine sepWPp_pure_left fun ⟨htr_s43, hoom, _halign_ptr⟩ => ?_
        have hsp_s4 : s4.sp = s1.sp := hsps4.trans hsp_s3
        have hspa_s4 : s4.spAligned = true := by
          simpa only [State.spAligned, hsp_s4] using hspa_s1
        have hhigh_s4 : PresHigh s0 s4 :=
          (PresHigh.of_callee
            ⟨by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.1,
             by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.2.1,
             by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s2.2.2⟩
            hcss4)
        have hx19_s4 : s4.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
          hcss4.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx19_s2)
        have hx20_s4 : s4.readReg64 .x20 = x.bytesV :=
          hcss4.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx20_s2)
        have hx22_s4 : s4.readReg64 .x22 = x.self :=
          hcss4.2.2.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx22_s2)
        have hx23_s4 : s4.readReg64 .x23 = x.nameA :=
          hcss4.2.2.2.2.1.trans (by rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hx23_s2)
        have hoom_raw : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom
        let allocPtr := s4.readReg64 .x0
        have htr_s4 : s4.trace = s0.trace := htr_s43.trans htr_s3
        apply sepWPp_cut_rebase_543 (mid := lsρ memcpyName) hcrls4
        dsimp +zetaDelta only [atOff543] at hpcs4 ⊢
        wp_steps_sync_pool (lsρ memcpyName)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro s5 P5 hcrl_s5 ⟨hs5, hP5⟩
        · subst hP5
          conv => arg 4; rw [← hs5]
          let _ := hoom_raw
          let _ := hsp_s4
          let _ := hspa_s4
          have hsp_s5 : s5.sp = s3.sp := by
            rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hsps4
          have hspa_s5 : s5.spAligned = true := by
            simpa only [State.spAligned, hsp_s5] using hspa_s3
          have htr_s5 : s5.trace = s0.trace := by
            rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact htr_s4
          rw [← hsp_s5]
          apply call_lscro_wpp hmemcpy (allocPtr, x.nameA, x.name)
            (ret_pc := atOff543 80)
            (F := A.pool lim (M.stepEvents evsAlloc st0) s5 ∗
              A.live allocPtr x.name.length 1 ∗
              (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
              savedSlots s0)
            (hcrl := hcrl_s5)
            (hpc := by rw [hs5]; rfl)
            (hrun := by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hruns4)
            (hsp_align := hspa_s5)
            (hlr := by rw [hs5]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
            (hspec := sepConj_assoc _ _ _)
            (hφ := ⟨by rw [hs5]; try simp +zetaDelta only [wp_norm, arm64_norm],
                    by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx23_s4,
                    by rw [hs5]; simp only [wp_norm, arm64_norm]; exact hname_toNat,
                    by omega⟩)
            (hP := by
              try dsimp +zetaDelta only [savedSlots, bytesAt, cal, evsAlloc, allocPtr]
              try rw [hsp_s5]
              try rw [hsp_s3]
              try rw [hsp_s1]
              repeat rw [bv_sub_eq_add_neg64']
              try simp only [sp_slot_norm]
              try rw [emp_sepConj]
              try rw [sepConj_emp]
              try simp only [wp_norm, arm64_norm]
              try rw [Nat.mul_comm 48]
              sep_ac_rfl)
            (hpan := fun _ => panic_false_wpp_543)
            (hexit := fun _ _ => rfl)
            (hoom := fun _ => rfl)
          intro s6 hpcs6 hruns6 hsps6 hcss6 hcrls6
          dsimp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec]
          try simp only [sepConj_assoc]
          refine sepWPp_pure_left fun hvm_s65 => ?_
          refine sepWPp_pure_left fun ⟨_hx0_mc, htr_s65⟩ => ?_
          conv => arg 4; rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evsAlloc st0) hvm_s65]
          have hsp_s6 : s6.sp = s0.sp - 80#64 :=
            hsps6.trans (hsp_s5.trans (hsp_s3.trans hsp_s1))
          have hspa_s6 : s6.spAligned = true := by
            simpa only [State.spAligned, hsps6] using hspa_s5
          have htr_s6 : s6.trace = s0.trace := htr_s65.trans htr_s5
          have hhigh_s6 : PresHigh s0 s6 :=
            (PresHigh.of_callee
              ⟨by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.1,
               by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.2.1,
               by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s4.2.2⟩
              hcss6)
          have hx19_s6 : s6.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
            hcss6.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx19_s4)
          have hx20_s6 : s6.readReg64 .x20 = x.bytesV :=
            hcss6.2.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx20_s4)
          have hx21_s6 : s6.readReg64 .x21 = allocPtr :=
            hcss6.2.2.1.trans (by rw [hs5]; try simp +zetaDelta only [wp_norm, arm64_norm])
          have hx22_s6 : s6.readReg64 .x22 = x.self :=
            hcss6.2.2.2.1.trans (by rw [hs5]; try simp only [wp_norm, arm64_norm]; try exact hx22_s4)
          have hstk_merge6 :
              memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                stackAt s5.sp extHookStack =
                stackAt (s0.sp - 80#64) cal := by
            rw [← stackAt_split_sub s5.sp
              (Nat.le_max_right growStk extHookStack) (by omega), hsp_s5, hsp_s3, hsp_s1]
          have hlive_eq : A.live allocPtr x.name.length 1 = A.repAlloc.live allocPtr x.name.length 1 := by
            rw [A.repAlloc_live_norm]
          have hpost_mc_ent :
              (allocPtr ↦ₛ x.name) ∗
                bytesAt x.nameRo x.nameA x.name ∗
                stackAt s5.sp extHookStack ∗
                A.pool lim (M.stepEvents evsAlloc st0) s6 ∗
                A.live allocPtr x.name.length 1 ∗
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
                strRefAt (x.self + 0x18#64) x.dir.path ∗
                (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                savedSlots s0 ⊢
              (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
                strRefAt (x.self + 0x18#64) x.dir.path ∗
                bytesAt x.nameRo x.nameA x.name ∗
                nameBuf A.repAlloc allocPtr x.name ∗
                (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                stackAt (s0.sp - 80#64) cal ∗
                savedSlots s0 ∗
                A.pool lim (M.stepEvents evsAlloc st0) s6 := by
            rw [hlive_eq]
            rw [show ∀ (BS NB Stk5 Pool Live S0 S1 S2 VB Path B0 B1 B2 BH M0 MC Sav : SepProp),
                  BS ∗ NB ∗ Stk5 ∗ Pool ∗ Live ∗ S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗
                    B0 ∗ B1 ∗ B2 ∗ BH ∗ M0 ∗ MC ∗ Sav =
                  (Live ∗ BS) ∗
                    (S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗ NB ∗ B0 ∗ B1 ∗ B2 ∗ BH ∗
                      M0 ∗ (MC ∗ Stk5) ∗ Sav ∗ Pool) by intros; sep_ac_rfl]
            rw [hstk_merge6]
            exact Entails.trans
              (sepConj_mono_left (nameBuf_of_nonempty A.repAlloc allocPtr x.name hnil hoom (by omega)))
              (entails_eq' (by sep_ac_rfl))
          apply sepWPp_weaken_pre hpost_mc_ent
          cases hdir_cases : x.dir.changed with
          | nil =>
            apply sepWPp_cut_rebase_543 (mid := atOff543 244) hcrls6
            dsimp +zetaDelta only [atOff543] at hpcs6 ⊢
            wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 244)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            intro s7 P7 hcrl_s7 ⟨hs7, hP7⟩
            · subst hP7
              conv => arg 4; rw [← hs7]
              let _ := hBcmp
              let _ := hC
              rw [← hdir_cases]
              apply sepWPp_eq_pre
              · exact step_miss_543 hgrow x st0 evsAlloc R s0 s7 cap ptr allocPtr bCap bPtr
                  hstk hstk_max hlen32
                  (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
                  hFitTailNe hWrapNe
                  hcrl_s7
                  (by rw [hs7]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hruns6)
                  (by
                    have hsp_eq : s7.sp = s6.sp := by rw [hs7]; try simp only [wp_norm, arm64_norm]
                    simpa only [State.spAligned, hsp_eq] using hspa_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hsp_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact htr_s6)
                  ⟨by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.1,
                   by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.1,
                   by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.2⟩
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx19_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx20_s6)
                  (by rw [hs7]; try simp +zetaDelta only [wp_norm, arm64_norm]; try exact hx21_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx22_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm])
              · try dsimp +zetaDelta only [savedSlots, bytesAt, cal, evsAlloc, allocPtr]
                try simp only [sp_slot_norm]
                try rw [emp_sepConj]
                try rw [sepConj_emp]
                try simp only [wp_norm, arm64_norm]
                try rw [Nat.mul_comm 48]
                sep_ac_rfl
          | cons e0 rest0 =>
            have hlen_pos : 0 < (e0 :: rest0).length := by simp
            have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
              beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
            apply sepWPp_cut_rebase_543 (mid := atOff543 104) hcrls6
            dsimp +zetaDelta only [atOff543] at hpcs6 ⊢
            wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 104)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            intro s7 P7 hcrl_s7 ⟨hs7, hP7⟩
            · subst hP7
              conv => arg 4; rw [← hs7]
              let _ := hlen_nz
              rw [← hdir_cases]
              apply sepWPp_eq_pre
              · exact step_preheader_543 hC hBcmp hgrow x st0 evsAlloc R s0 s7 e0 rest0 cap ptr allocPtr bCap bPtr
                  hstk hstk_max hname32 hlen32 hdir_cases hFitTailNe hWrapNe hsp_align0 hcrl_s7
                  (by rw [hs7]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hruns6)
                  (by
                    have hsp_eq : s7.sp = s6.sp := by rw [hs7]; try simp only [wp_norm, arm64_norm]
                    simpa only [State.spAligned, hsp_eq] using hspa_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hsp_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact htr_s6)
                  ⟨by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.1,
                   by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.1,
                   by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hhigh_s6.2.2⟩
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx19_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx20_s6)
                  (by rw [hs7]; try simp +zetaDelta only [wp_norm, arm64_norm]; try exact hx21_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try exact hx22_s6)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm]; try rw [hdir_cases]; try rfl)
                  (by rw [hs7]; try simp only [wp_norm, arm64_norm])
              · try dsimp +zetaDelta only [savedSlots, bytesAt, cal, evsAlloc, allocPtr]
                try simp only [sp_slot_norm]
                try rw [emp_sepConj]
                try rw [sepConj_emp]
                try simp only [wp_norm, arm64_norm]
                try rw [Nat.mul_comm 48]
                sep_ac_rfl

/-- `Dir::put::<&str>` satisfies `dirPutStrSpecPlaced A lim DirPutStrEnv stk` on Block 543 under `[LibsignalPlacement]`. -/
theorem dirPutStr_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim DirPutStrEnv stk) :=
  dirPutStr_placed_ok_of_deps_gen (fun _ _ _ _ h => h) hC hpan hRO hBcmp hjGrow hjGrow_unmut hGrow hstk

/-- Envelope-polymorphic caller-transferable `[LibsignalPlacement]` `Dir::put::<&str>` contract
for any block `< 619`. -/
theorem dirPutStr_placed_caller_ok_of_deps_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {callerProg growProg : Program} {i jGrow : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg growProg jGrow H]
    {growStk stk : Nat}
    (hPutStrEnv : ∀ dir name bytes evs, DirPutStrEnv dir name bytes evs →
      PutStrEnv dir name bytes evs)
    (hC : AllocContractsXCliPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hi : i < 619 := by decide)
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 543) (dirPutStrSpecPlaced A lim PutStrEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 543)
    (dirPutStr_placed_ok_of_deps_gen hPutStrEnv hC hpan hRO hBcmp hjGrow hjGrow_unmut hGrow hstk) hi

/-- Caller-transferable `[LibsignalPlacement]` `Dir::put::<&str>` contract for any block `< 619`. -/
theorem dirPutStr_placed_caller_ok_of_deps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg growProg : Program} {i jGrow : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg growProg jGrow H]
    {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hi : i < 619 := by decide)
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim DirPutStrEnv stk) :=
  dirPutStr_placed_caller_ok_of_deps_gen (fun _ _ _ _ h => h)
    hC hpan hRO hBcmp hGrow hstk hi hjGrow hjGrow_unmut

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget
