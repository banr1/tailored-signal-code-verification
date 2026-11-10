/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Path.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

gen_decodes CryptoVerification.libsignalSessionCode_tree pathDec
  [(ls_off% "libsignal_cli::stores::path") → (ls_off% "libsignal_cli::stores::path" + 288)]

/-! ## 1. Stack, Memory, and Capacity Helpers -/

theorem stk_lt_two_pow_64 {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hm : m ⊨ memRegion ret 24 ∗ stackAt sp stk ∗ R) :
    stk < 2 ^ 64 := by
  by_contra hge
  have hdisj :=
    (IsBlock.memRegion ret 24).disjoint (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk)
      (by decide) (by omega) hm
  have hlt := (ret - (sp - BitVec.ofNat 64 stk)).isLt
  exact absurd hdisj.2 (by omega)

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem cells_14_eq (fsp : BitVec 64) :
    cells fsp 14 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗
        ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
        ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13)) := by
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem stackAt_path_frame (sp0 : BitVec 64) {subStk : Nat} (hsub : subStk + 112 ≤ 2 ^ 64) :
    stackAt sp0 (112 + subStk) =
      stackAt (sp0 - 112#64) subStk ∗ cells (sp0 - 112#64) 14 := by
  have h := ProofLib.stackAt_split_cells sp0 subStk 14 (by omega)
  have heq : subStk + 8 * 14 = 112 + subStk := by omega
  simpa only [heq] using h

theorem sp_sub_112_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 112#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem fsp_add_112_eq (sp0 : BitVec 64) : (sp0 - 112#64) + 112#64 = sp0 := by
  bv_omega

theorem pointsTo64_pair_eq_pointsTo128 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  rw [pointsTo128_split64]
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  rw [h0, h1]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_1_eq_pointsTo8 (a : BitVec 64) :
    memRegion a 1 = ∃∗ b : BitVec 8, a ↦₈ b :=
  ProofLib.memRegion_one a

theorem pointsTo8_eq_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem bv_eq_ofNat_of_toNat {v : BitVec 64} {n : Nat} (h : v.toNat = n) :
    v = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ BitVec.isLt v)]

theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem ofNat_ne_zero {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## 2. Call Target Address Lemmas and Unified `memcpy` (`ro : Bool`) Contract -/

theorem cliDoReserve_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pathName -
      BitVec.ofNat 64
        (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "libsignal_cli::stores::path") =
      (tripleRatchetProgAtExt b ext).fnAddr cliDoReserveName := by
  have h1 := path_fnOff
  have h2 := cliDoReserve_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h1, h2]
  bv_omega


/-- Stack-equipped `memcpy` contract parameterized by `ro : Bool` (`ChainProofs.bytesAt`). -/
def session2MemcpyBytesAtSpecX (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

theorem memcpy_bytesAt_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      ((session2MemcpyBytesAtSpecX ro).inImage img) := by
  cases ro
  · have hmc := memcpy_ok_at2_ext_x hC (name := pathName)
      (k := ls_rel% "libsignal_cli::stores::path" "memcpy")
      (by rw [path_fnOff, (ls_stub% "memcpy")])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (session2MemcpySpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, session2MemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [Spec.inImage, session2MemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro := SpqrV1.Alloc.session_memcpy_region_ro_ok_at (b := img.base) hRO pathName
      (ls_rel% "libsignal_cli::stores::path" "memcpy")
      (by rw [path_fnOff, (ls_stub% "memcpy")])
    apply SpqrV1.Alloc.subroutine_ok_inImage img
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
        (stackAt s0.sp extHookStack ∗ R) := by
      simp only [session2MemcpyBytesAtSpecX, sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] at hpre ⊢
      exact hpre
    refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [session2MemcpyBytesAtSpecX, sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] at hpost ⊢
      exact hpost
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

theorem memcpy_bytesAt_ok_at_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      ((session2MemcpyBytesAtSpecX ro).inImage img) := by
  cases ro
  · have hmc := memcpy_ok_at2_ext_x hC (name := pathName)
      (k := ls_rel% "libsignal_cli::stores::path" "memcpy")
      (by rw [path_fnOff, (ls_stub% "memcpy")])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (session2MemcpySpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, session2MemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [Spec.inImage, session2MemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro := SpqrV1.Alloc.session_memcpy_region_ro_ok_at_x_of_roX hRO pathName
      (ls_rel% "libsignal_cli::stores::path" "memcpy")
      (by rw [path_fnOff, (ls_stub% "memcpy")])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (SpqrV1.Alloc.sessionMemcpyRegionROSpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
      simpa only [Spec.inImage, session2MemcpyBytesAtSpecX, SpqrV1.Alloc.sessionMemcpyRegionROSpecX,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] using hpre
    refine hmc_ro.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [Spec.inImage, session2MemcpyBytesAtSpecX, SpqrV1.Alloc.sessionMemcpyRegionROSpecX,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

theorem memcpyROOkExtX_of_withStack {img : Obj.Image}
    {ext : String → Option (State → State)} {roStk : Nat}
    (hro : roStk ≤ extHookStack)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk)) :
    SpqrV1.Alloc.MemcpyROOkExtX img ext := by
  have hfn : libsignalSessionCode.fnOff memcpyName = num% (ls_off% "memcpy") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "memcpy")
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk) := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
      (name := memcpyName) (hname := memcpyName) (k := 0)
      hfn (Nat.add_zero _) (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) hRO
    simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  have hlt : extHookStack ≤ 2 ^ 64 := by decide
  let btm := fun sp => memRegion (sp - BitVec.ofNat 64 extHookStack) (extHookStack - roStk)
  apply SpqrV1.Alloc.subroutine_ok_inImage img
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk).pre (dst, src, bs) s0 ∗
      (btm s0.sp ∗ R) := by
    dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecX,
      SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, btm] at hpre ⊢
    rw [stackAt_split_ge s0.sp hro hlt] at hpre
    simp only [sepConj_assoc] at hpre ⊢
    rwa [← sepConj_assoc (memRegion _ _) (stackAt s0.sp roStk) R,
      sepConj_comm (memRegion _ _) (stackAt s0.sp roStk), sepConj_assoc] at hpre
  refine h0.mono_outcome (dst, src, bs) (btm s0.sp ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SpqrV1.Alloc.sessionMemcpyRegionROSpecX,
      SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, btm] at hpost ⊢
    rw [stackAt_split_ge s0.sp hro hlt]
    simp only [sepConj_assoc] at hpost ⊢
    rwa [← sepConj_assoc (stackAt s0.sp roStk) (memRegion _ _) R,
      sepConj_comm (stackAt s0.sp roStk) (memRegion _ _), sepConj_assoc] at hpost
  · rw [show (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk).onPanic (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk).onExit (dst, src, bs) code s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk).onOom (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1

theorem memcpy_bytesAt_ok_at_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (ro : Bool)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      ((session2MemcpyBytesAtSpecX ro).inImage img) :=
  memcpy_bytesAt_ok_at_roX hC (memcpyROOkExtX_of_withStack hro hRO) ro

/-! ## 3. Layout-Independent `SepWPp` Call & Panic Helpers -/

abbrev pathOnPanic (A : RustAlloc) (img : Obj.Image) (stk : Nat)
    (x0 : PathGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pathSpec A img stk).onPanic x0 s0 sf ∗ R)

theorem step_shim_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withEncRepeatedCS s0 session2ShimSpecX))
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = stackAt fsp extHookStack ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        (stackAt fsp extHookStack ∗ F) Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact hfsp_align
  refine SepWPp.call_cs (x := ()) (F := F)
    hshim hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withEncRepeatedCS, session2ShimSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withEncRepeatedCS, session2ShimSpecX, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withEncRepeatedCS, session2ShimSpecX, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

theorem step_handle_error_panic {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {call_pc ret : BitVec 64} {s0 s : State}
    (hpanic : (tripleRatchetProgAtExt img.base ext).externAt? call_pc = some Rust.panicked)
    {x0 : PathGhost} {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have hext : (tripleRatchetProgAtExt img.base ext).externAt? s.pc = some Rust.panicked := by
    rwa [hpc]
  refine SepWPp.panic hrun hext fun hm => ?_
  simpa only [pathSpec, Spec.inImage, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, htr])) hm

theorem step_alloc_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk size : Nat}
    {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (halloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withEncRepeatedCS s0 (rustAllocSpecWithStack A)))
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk size 1)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (A.pool ∗ stackAt fsp extHookStack) ∗ F)
    (hoom_next : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s0.trace ++ [allocFailedEvent] →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((A.pool ∗ stackAt fsp extHookStack) ∗ F) Q (pathOnPanic A img stk x0 s0 R))
    (halloc_next : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((A.pool ∗ stackAt fsp extHookStack ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact hfsp_align
  refine SepWPp.call_cs (x := (size, 1)) (F := F)
    halloc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withEncRepeatedCS, rustAllocSpecWithStack, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlay⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withEncRepeatedCS, rustAllocSpecWithStack, sepConj_assoc,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    have hcs_s0 := hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)
    simp only [withEncRepeatedCS, rustAllocSpecWithStack, hsp, BitVec.ofNat_eq_ofNat]
    by_cases hoom : sm.readReg64 .x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]
      have hpure_front :
          A.pool ∗ stackAt fsp extHookStack ∗ ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗ F =
          ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗ ((A.pool ∗ stackAt fsp extHookStack) ∗ F) := by
        ac_rfl
      rw [hpure_front]
      refine SepWPp.pure_elim fun htrm => ?_
      rw [htr] at htrm
      exact hoom_next sm hpcm hrunm hspm hoom htrm hcsm hcs_s0
    · simp only [hoom, ite_false, sepConj_assoc]
      have hpure_front :
          A.pool ∗ stackAt fsp extHookStack ∗
            ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F =
          ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            ((A.pool ∗ stackAt fsp extHookStack ∗
              A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size) ∗ F) := by
        ac_rfl
      rw [hpure_front]
      refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
      exact halloc_next sm hpcm hrunm hspm hoom (htrm.trans htr) hcsm hcs_s0

theorem step_memcpy_ro_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat} {ro : Bool}
    {call_pc dst src fsp ret_pc ret : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State}
    (hmc : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withEncRepeatedCS s0 (session2MemcpyBytesAtSpecX ro)))
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ SpqrV1.ChainProofs.bytesAt ro src bs ∗
      stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        (((dst ↦ₛ bs) ∗ SpqrV1.ChainProofs.bytesAt ro src bs ∗
          stackAt fsp extHookStack) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact hfsp_align
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withEncRepeatedCS, session2MemcpyBytesAtSpecX, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withEncRepeatedCS, session2MemcpyBytesAtSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withEncRepeatedCS, session2MemcpyBytesAtSpecX, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

theorem step_cli_reserve_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk additional : Nat}
    {call_pc v curCap curPtr fsp ret_pc ret : BitVec 64} {curBs : List (BitVec 8)}
    {s0 s : State}
    (hres : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withEncRepeatedCS s0 (SpqrV1.Varint.doReserveSpecOf resStack A)))
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt fsp resStack) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional))
          newPtr curBs ∗ A.pool ∗ stackAt fsp resStack) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact hfsp_align
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional) (F := F)
    hres hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withEncRepeatedCS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withEncRepeatedCS, doReserveSpecOf, doReserveSpec, pathSpec, Spec.inImage,
      allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.Path.Helpers
