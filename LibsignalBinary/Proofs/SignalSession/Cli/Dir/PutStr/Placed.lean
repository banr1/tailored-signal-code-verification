/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Hit
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `[LibsignalPlacement]` `<signal_session::stores::Dir>::put::<&str>` (Block `543`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.PutStr.Helpers hiding atOff arrayAt_append

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

abbrev atOff543 [LibsignalPlacement] (k : Nat) : BitVec 64 :=
  (blkPl_543).base + BitVec.ofNat 64 k

/-- Opaque equality wrapper so `wp_steps` and `wp_norm_lhs` keep `curBase` atomic. -/
structure CurEq (c b : BitVec 64) : Prop where
  out : c = b

theorem stackAt_split_sp {sp s_sp : BitVec 64} {sub n : Nat}
    (hsp : s_sp = sp) (hle : sub ≤ n) (hmax : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (s_sp - BitVec.ofNat 64 n) (n - sub) ∗ stackAt s_sp sub := by
  subst hsp
  exact stackAt_split_sub s_sp hle hmax

theorem sepWPp_eq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P' Q Qp)
    (hP : P = P') :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

abbrev lsHandleErrorSymCli : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem panic_at_dirPutStr_handle_error_543 [LibsignalPlacement] {H : LibsignalHooks}
    (hpan : CliPanicHooksPlaced H) :
    (lsProg_543 H).externAt? (lsρ lsHandleErrorSymCli) = some Rust.panicked :=
  ls_panicAt_of_cliPanic hpan (sym := lsHandleErrorSymCli)

theorem shim_ok_at_dirPutStr_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl session2ShimSpecX) := by
  have h := shim_lscro_of_cli (callerProg := lsProg_543 H) (stk := extHookStack) hC
  intro u R s0 hpc hrun hpre hal hL
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)).pre u s0 ∗ R := by
    apply satisfies_lscro_pre hcrl0
    simpa only [session2ShimSpecX, withStack, sessionShimSpec, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj, true_and] using hpre0
  exact h u R s0 hpc hrun hpre' hal hL

theorem alloc_ok_at_dirPutStr_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  alloc_lscro_of_cli (callerProg := lsProg_543 H) hC

theorem dealloc_ok_at_dirPutStr_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := lsProg_543 H) hC

theorem memcpy_bytesAt_lscro_ok_at_543 [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (lsProg_543 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (withStack (SpqrV1.Alloc.sessionMemcpyBytesAtSpec ro) extHookStack)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_543 H)
      (stk := extHookStack) hC
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    rcases hmc (dst, src, bs) R s0 hpc hrun hpre' hal hL with ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro : subroutine_ok (lsProg_543 H) (lsρ memcpyName)
        SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
      ls_hook_ok_ultra_of_mem hRO (by decide)
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨_hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        SpqrV1.Alloc.sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
          (stackAt s0.sp extHookStack ∗ R) := by
      simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    rcases hmc_ro (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal hL with
      ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [StoreKit.withLsCodeRoLoaded, withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

theorem bcmp_lscro_ok_at_dirPutStr_543 [LibsignalPlacement]
    (H : LibsignalHooks)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec) :
    subroutine_ok (lsProg_543 H) (lsρ cliBcmpName)
      (StoreKit.withLsCodeRoLoaded lsmpl cliBcmpSpec) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem hBcmp (by decide))

theorem call_lscro_wpp [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (x : α) {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    {φ : Prop} (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog target_pc s P Q Qp := by
  intro R' hm hL
  have hm_pre : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    apply satisfies_lscro_pre hcrl
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun hm_pre hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpan sm⟩)⟩
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hexit] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hoom] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

abbrev DirPutStrPostPlaced [LibsignalPlacement] (A : RustAlloc) (x : DirPutStrGhost)
    (s0 : State) (stk : Nat) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutStrSpecPlaced A stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev DirPutStrPanicPlaced [LibsignalPlacement] (A : RustAlloc) (x : DirPutStrGhost)
    (s0 : State) (stk : Nat) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutStrSpecPlaced A stk).onPanic x s0 sf ∗ R)

theorem sepWPp_cut_543 [LibsignalPlacement] {H : LibsignalHooks} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP (lsProg_543 H) mid s P fun sm Pm =>
      ∀ s', s' = sm → StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        SepWPp (lsProg_543 H) ret s' Pm Q Qp) :
    SepWPp (lsProg_543 H) ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm rfl (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_cut_rebase_543 [LibsignalPlacement] {H : LibsignalHooks}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP (lsProg_543 H) mid s P fun sm Pm =>
      ∀ s1 P1, StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem → (s1 = sm ∧ P1 = Pm) →
        SepWPp (lsProg_543 H) ret s1 P1 Q Qp) :
    SepWPp (lsProg_543 H) ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm Pm (hcrl.of_keepsFrozen hsteps.keepsFrozen) ⟨rfl, rfl⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem panic_false_wpp_543 [LibsignalPlacement] {A : RustAlloc} {x : DirPutStrGhost}
    {s0 : State} {stk : Nat} {R : SepProp} {sf : State} {F : SepProp} :
    DirPutStrPanicPlaced A x s0 stk R sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

theorem panic_callee_wpp_543 [LibsignalPlacement] {A : RustAlloc} {x : DirPutStrGhost}
    {s0 s sf : State} {stk : Nat} {R F : SepProp}
    (htr : s.trace = s0.trace) :
    DirPutStrPanicPlaced A x s0 stk R sf
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro hm
  have hm' : sf.mem ⊨ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ (anyHeap ∗ F ∗ R) := by
    simpa only [sepConj_assoc] using hm
  rw [satisfies_pure_sepConj] at hm'
  exact allowPanic_panicked (allocFailedIn_of_trace_eq htr hm'.1) hm

theorem tailcall_lscro_frame [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (x : α) {φ : Prop} {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Q sf (spec.post x s sf ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hm_pre : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    apply satisfies_lscro_pre hcrl
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun hm_pre hsp hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨_, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, _, hpost, hret sf hpcf hrunf hspf hcsf⟩⟩
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hpan] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hexit] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hoom] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Shared post-drop tail of the hit branch starting at `+188` on Block `543`. -/
private theorem step_hit_copy_and_exit_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr curBase namePtr bCap bPtr d0 d1 d2 : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 188)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = curBase + 24#64) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ d0) ∗ ((curBase + 32#64) ↦₆₄ d1) ∗
        ((curBase + 40#64) ↦₆₄ d2) ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool)
      (DirPutStrPostPlaced A x s0 stk R)
      (DirPutStrPanicPlaced A x s0 stk R) := by
  intro cal
  have hdealloc := dealloc_ok_at_dirPutStr_543 hC
  have hdir_ent :
      vecOf A 48 8 (dirEntryAt A) x.self (pre ++ (x.name, x.bytes) :: rest) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
        dirAt A x.self (x.dir.put x.name x.bytes) := by
    unfold dirAt
    rw [hput_eq]
    exact Entails.refl _
  have hhit_ent :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        (((curBase + 24#64) ↦₆₄ bCap) ∗ ((curBase + 32#64) ↦₆₄ bPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗ vecU8Heap A bCap bPtr x.bytes) ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ⊢
        vecOf A 48 8 (dirEntryAt A) x.self (pre ++ (x.name, x.bytes) :: rest) :=
    vecOf_dirEntry_hit_assemble A x.self cap ptr curBase bCap bPtr
      pre rest x.name x.bytes hcur hle hbound hptr hcap
  clear hcur
  by_cases hnil : x.name = []
  · have hx19_z : s.readReg64 .x19 = 0#64 := by
      rw [hx19, hnil]; rfl
    have hdrop_name : nameBuf A namePtr x.name ⊢ emp := by
      rw [hnil]; exact nameBuf_drop_nil A namePtr
    dsimp only [DirPutStrPostPlaced, DirPutStrPanicPlaced, dirPutStrSpecPlaced,
      StoreKit.withLsCodeRoLoaded, atOff543, savedSlots] at hpc ⊢
    clear hC hdealloc hcrl
    rcases hhigh with ⟨hx27, hx28, hvregs⟩
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.fold hdrop_name (by sep_frame)
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    wp_done
  · have hpos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx19_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    dsimp only [atOff543, savedSlots] at hpc hdealloc ⊢
    clear hC
    apply sepWPp_cut_543 (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    apply SepWP.fold (nameBuf_for_dealloc A namePtr x.name hnil) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hcrl_s1
    rw [show ∀ (P0 L1 M1 D1 N1 B24 S1 Pool : SepProp),
          (P0 ∗ L1 ∗ M1) ∗ D1 ∗ N1 ∗ B24 ∗ S1 ∗ Pool =
            P0 ∗ (Pool ∗ L1 ∗ M1 ∗ D1 ∗ N1 ∗ B24 ∗ S1) from
          fun _ _ _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨_hnp_ne0, hlay_name⟩ => ?_
    have hsp_s1 : s1.sp = s0.sp := by
      rw [hs1]; simp only [wp_norm, arm64_norm]
    have hsp_align_s1 : s1.spAligned = true := by
      simpa only [State.spAligned, hsp_s1] using hsp_align0
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    have hcs_s1 : CalleeSavedPreserved s0 s1 := by
      refine calleeSavedPreserved_of_restored
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    rw [← hsp_s1, stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max]
    apply tailcall_lscro_frame hdealloc (namePtr, x.name.length, 1)
      (F := dirAt A x.self (x.dir.put x.name x.bytes) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.bytesV 24 ∗
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      (hcrl := hcrl_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp := hsp_align_s1)
      (hlr := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
              by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19_toNat,
              by rw [hs1]; simp only [wp_norm, arm64_norm],
              hlay_name⟩)
      (hP := by ac_rfl)
      (hpan := fun _ => rfl)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sf _hpcf _hrunf hspf hcsf
    refine ⟨?_, hspf.trans hsp_s1, hcs_s1.trans hcsf⟩
    intro hm
    dsimp only [rustDeallocExternSpecWithStack] at hm
    dsimp only [dirPutStrSpecPlaced, StoreKit.withLsCodeRoLoaded]
    have hstk_re :
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
          stackAt s1.sp extHookStack =
          stackAt s0.sp stk := by
      rw [← stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max, hsp_s1]
    rw [show ((⌜sf.trace = s1.trace⌝ ∗ A.pool ∗ stackAt s1.sp extHookStack) ∗
          (dirAt A x.self (x.dir.put x.name x.bytes) ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R =
        ⌜sf.trace = s1.trace⌝ ∗
          (dirAt A x.self (x.dir.put x.name x.bytes) ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            (memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
              stackAt s1.sp extHookStack) ∗
            A.pool ∗ R) by ac_rfl] at hm
    rw [satisfies_pure_sepConj, hstk_re] at hm
    rcases hm with ⟨htr_sf1, hmem_sf⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr_sf1.trans htr_s1, ?_⟩
    ac_nf at hmem_sf ⊢
/-- Hit branch entry at `+164` on Block `543`. -/
theorem step_hit_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (oldBs : List (BitVec 8))
    (cap ptr curBase namePtr bCap bPtr oldCap oldPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 164)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx25 : s.readReg64 .x25 = curBase + 32#64) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
        ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Heap A oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool)
      (DirPutStrPostPlaced A x s0 stk R)
      (DirPutStrPanicPlaced A x s0 stk R) := by
  intro cal
  have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur⟩
  clear hcur
  have hdealloc := dealloc_ok_at_dirPutStr_543 hC
  by_cases hold0 : oldCap = 0#64
  · subst hold0
    apply sepWPp_cut_rebase_543 (mid := atOff543 188) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps
    apply SepWP.fold (vecU8Heap_drop_zero A oldPtr oldBs) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
      apply sepWPp_eq_pre
      · exact step_hit_copy_and_exit_543 hC x R s0 s1 pre rest cap ptr curBase namePtr bCap bPtr
          0#64 oldPtr (BitVec.ofNat 64 oldBs.length)
          hstk hstk_max hname32 hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hcrl_s1
          (by rw [hs1]; try dsimp +zetaDelta only [atOff543]; simp only [wp_norm, arm64_norm])
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr)
          ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21)
          (by rw [hs1]; simp only [wp_norm, arm64_norm])
      · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        try ac_rfl
  · have hold_beq : (oldCap == 0#64) = false := beq_false_of_ne hold0
    apply sepWPp_cut_rebase_543 (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps
    apply SepWP.fold (vecU8Heap_for_dealloc A oldCap oldPtr oldBs hold0) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
      rw [show ∀ (P0 L0 M0 Z : SepProp),
            (P0 ∗ L0 ∗ M0) ∗ Z = P0 ∗ L0 ∗ M0 ∗ Z from
            fun _ _ _ _ => by ac_rfl]
      refine sepWPp_pure_left fun ⟨_holdp_ne0, hlay_old⟩ => ?_
      have hsp_s1 : s1.sp = s0.sp - 80#64 := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp
      have htr_s1 : s1.trace = s0.trace := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr
      rw [stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
      apply call_lscro_wpp hdealloc (oldPtr, oldCap.toNat, 1)
        (ret_pc := atOff543 188)
        (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curBase x.name ∗
          ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
          arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
            ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0)
        (hcrl := hcrl_s1)
        (hpc := by rw [hs1]; rfl)
        (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := by
          have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff543]; simp only [wp_norm, arm64_norm])
        (hspec := rfl)
        (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                hlay_old⟩)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl)
        (hpan := fun _ => panic_false_wpp_543)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro sm hpcm hrunm hspm hcsm hcrlm
      dsimp only [rustDeallocExternSpecWithStack]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun htr_sm0 => ?_
      have hstk_back :
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            stackAt s1.sp extHookStack =
            stackAt (s0.sp - 80#64) cal := by
        rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
      rw [show ∀ (Pool StkE A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 : SepProp),
            Pool ∗ StkE ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 =
            A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ (A20 ∗ StkE) ∗ A21 ∗ Pool from
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by ac_rfl]
      rw [hstk_back]
      have hhigh_s1 : PresHigh s0 s1 :=
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
      exact step_hit_copy_and_exit_543 hC x R s0 sm pre rest cap ptr curBase namePtr bCap bPtr
        oldCap oldPtr (BitVec.ofNat 64 oldBs.length)
        hstk hstk_max hname32 hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hcrlm
        hpcm hrunm
        (hspm.trans hsp_s1)
        (htr_sm0.trans htr_s1)
        (hhigh_s1.of_callee hcsm)
        (hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19))
        (hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20))
        (hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21))
        (hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]))

/-- Miss exit at `+244` on Block `543`. -/
theorem step_miss_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 244)
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
    (hx24 : s.readReg64 .x24 = ptr) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool)
      (DirPutStrPostPlaced A x s0 stk R)
      (DirPutStrPanicPlaced A x s0 stk R) := by
  intro cal
  have hpush : ∀ (s1 : State) (cap1 ptr1 : BitVec 64),
      x.dir.changed.length < cap1.toNat →
      s1.pc = atOff543 256 →
      s1.status = .Running →
      s1.spAligned = true →
      s1.sp = s0.sp - 80#64 →
      s1.trace = s0.trace →
      PresHigh s0 s1 →
      s1.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
      s1.readReg64 .x20 = x.bytesV →
      s1.readReg64 .x21 = namePtr →
      s1.readReg64 .x22 = x.self →
      s1.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
      s1.readReg64 .x24 = ptr1 →
      SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s1
        ((x.self ↦₆₄ cap1) ∗ ((x.self + 8#64) ↦₆₄ ptr1) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap1 ptr1 x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool)
        (DirPutStrPostPlaced A x s0 stk R)
        (DirPutStrPanicPlaced A x s0 stk R) := by
    intro s1 cap1 ptr1 hlt1 hpc1 hrun1 hspa1 hsp1 htr1 hhigh1
      hr19 hr20 hr21 hr22 hr23 hr24
    dsimp only [DirPutStrPostPlaced, DirPutStrPanicPlaced, dirPutStrSpecPlaced,
      StoreKit.withLsCodeRoLoaded, atOff543] at hpc1 ⊢
    rcases hhigh1 with ⟨hr27, hr28, hvregs1⟩
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (vecBuf_dirEntry_expose_slot A cap1 ptr1 x.dir.changed hlt1)))))
    dsimp only
    rw [show ∀ (A1 A2 A3 P0 B1 B2 B3 E6 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B1 ∗ B2 ∗ B3 ∗ E6) ∗ Z =
            P0 ∗ E6 ∗ A1 ∗ A2 ∗ A3 ∗ B1 ∗ B2 ∗ B3 ∗ Z from
          fun _ _ _ _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨hle1, hbound1, hptr1, hcap1_ne⟩ => ?_
    set slot := ptr1 + BitVec.ofNat 64 (x.dir.changed.length * 48)
    refine sepWPp_exists_left fun u0 => ?_
    simp only [sepConj_assoc]
    refine sepWPp_exists_left fun u1 => ?_
    refine sepWPp_exists_left fun u2 => ?_
    refine sepWPp_exists_left fun u3 => ?_
    refine sepWPp_exists_left fun u4 => ?_
    refine sepWPp_exists_left fun u5 => ?_
    apply SepWPp.of_sepWP_ret
    have hslot_eq : ptr1 + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
      madd_slot_eq ptr1 x.dir.changed.length
    have hlen1_eq : BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
      rw [← BitVec.ofNat_add]
    wp_steps
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold
      (vecOf_dirEntry_push_assemble A x.self cap1 ptr1 namePtr bCap bPtr
        x.dir.changed x.name x.bytes hle1 hbound1 hptr1 hcap1_ne)
      (by sep_frame)
    have hput : (x.dir.put x.name x.bytes).changed = x.dir.changed ++ [(x.name, x.bytes)] :=
      setOrPush_eq_append_singleton_of_forall_ne x.name x.bytes x.dir.changed hmiss
    have hdir :
        vecOf A 48 8 (dirEntryAt A) x.self (x.dir.changed ++ [(x.name, x.bytes)]) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ⊢
          dirAt A x.self (x.dir.put x.name x.bytes) := by
      unfold dirAt
      rw [hput]
      exact Entails.refl _
    apply SepWP.fold hdir (by sep_frame)
    wp_done
  have hpull_len :
      vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed =
        ⌜x.dir.changed.length ≤ cap.toNat⌝ ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed := by
    apply Entails.antisymm
    · unfold vecBuf
      refine Entails.pure_left fun h => ?_
      exact Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))
    · exact Entails.pure_left fun _ => Entails.refl _
  rw [hpull_len]
  rw [show ∀ (A1 A2 A3 P0 B Z : SepProp),
        A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B) ∗ Z = P0 ∗ A1 ∗ A2 ∗ A3 ∗ B ∗ Z from
        fun _ _ _ _ _ _ => by ac_rfl]
  refine sepWPp_pure_left fun hle_cap => ?_
  by_cases heq_bv : BitVec.ofNat 64 x.dir.changed.length = cap
  · have hcap_eq : x.dir.changed.length = cap.toNat := by
      have ht := congrArg BitVec.toNat heq_bv
      rwa [ofNat_toNat_of_lt (by omega)] at ht
    have hcap32 : cap.toNat < 2 ^ 32 := by omega
    have hbeq_eq : (BitVec.ofNat 64 x.dir.changed.length == cap) = true :=
      beq_iff_eq.mpr heq_bv
    apply sepWPp_cut_543 (mid := lsmpl.base 586) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hcrl_s1
    have hsp_s1 : s1.sp = s0.sp - 80#64 := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    rw [← hsp_s1, stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega)]
    have hvec_in :
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed =
          vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
      unfold vecAt vecHeader
      ac_rfl
    apply call_lscro_wpp hgrow ⟨x.self, cap, ptr, x.dir.changed⟩
      (ret_pc := atOff543 328)
      (F := strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
        savedSlots s0)
      (hcrl := hcrl_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp_align := by
        have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align)
      (hlr := by rw [hs1]; dsimp [atOff543]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm], hcap32⟩)
      (hP := by
        rw [← hvec_in]
        ac_rfl)
      (hpan := fun _ => panic_callee_wpp_543 (s := s1) htr_s1)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sm hpcm hrunm hspm hcsm hcrlm
    have hsp_sm : sm.sp = s0.sp - 80#64 := hspm.trans hsp_s1
    have hsp_align_sm : sm.spAligned = true := by
      have hsp_eq : sm.sp = s.sp := hspm.trans (by rw [hs1]; simp only [wp_norm, arm64_norm])
      simpa only [State.spAligned, hsp_eq] using hsp_align
    have hhigh_s1 : PresHigh s0 s1 :=
      ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
    have hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
      hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
    have hx20_sm : sm.readReg64 .x20 = x.bytesV :=
      hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
    have hx21_sm : sm.readReg64 .x21 = namePtr :=
      hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
    have hx22_sm : sm.readReg64 .x22 = x.self :=
      hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
    have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
    dsimp only [growOneDirBaseSpec]
    simp only [sepConj_assoc]
    refine sepWPp_pure_left fun htr_sm0 => ?_
    have htr_sm : sm.trace = s0.trace := htr_sm0.trans htr_s1
    refine sepWPp_exists_left fun ptr' => ?_
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    have hlt_new : x.dir.changed.length < newCap.toNat :=
      growOne_cap_gt hcap_eq hlen32
    unfold vecAt vecHeader
    simp only [sepConj_assoc]
    apply sepWPp_cut_543 (mid := atOff543 256) hcrlm
    dsimp only [atOff543] at hpcm ⊢
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 hs2 _hcrl_s2
    have hstack_back :
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
          stackAt s1.sp growStk =
          stackAt (s0.sp - 80#64) cal := by
      rw [← stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega), hsp_s1]
    have hrearr :
        (x.self ↦₆₄ newCap) ∗ ((x.self + 8#64) ↦₆₄ ptr') ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) newCap ptr' x.dir.changed ∗
          stackAt s1.sp growStk ∗ A.pool ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
          savedSlots s0 =
        (x.self ↦₆₄ newCap) ∗ ((x.self + 8#64) ↦₆₄ ptr') ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) newCap ptr' x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          (memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
            stackAt s1.sp growStk) ∗
          savedSlots s0 ∗
          A.pool := by
      ac_rfl
    rw [hrearr, hstack_back]
    exact hpush s2 newCap ptr' hlt_new
      (by rw [hs2]; dsimp [atOff543]; simp only [wp_norm, arm64_norm])
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hrunm)
      (by
        have hsp_eq : s2.sp = sm.sp := by rw [hs2]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hsp_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact htr_sm)
      ⟨by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.1,
       by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.1,
       by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.2⟩
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx19_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx20_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx21_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx22_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx23_sm)
      (by rw [hs2]; simp only [wp_norm, arm64_norm])
  · have hlt_cap : x.dir.changed.length < cap.toNat := by
      by_contra hge
      have heq_nat : cap.toNat = x.dir.changed.length := by omega
      exact heq_bv (ofNat_eq_of_toNat_eq heq_nat).symm
    have hbeq_ne : (BitVec.ofNat 64 x.dir.changed.length == cap) = false :=
      beq_false_of_ne heq_bv
    apply sepWPp_cut_543 (mid := atOff543 256) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 _hcrl_s1
    exact hpush s1 cap ptr hlt_cap
      (by rw [hs1]; simp only [wp_norm, arm64_norm])
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (by
        have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr)
      ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
      (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx24)

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

/-- Loop invariant and induction over `suf` starting at `+132` on Block `543`. -/
theorem step_loop_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hsp_align0 : s0.spAligned = true) :
    let cal := max growStk extHookStack
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ p ∈ pre, p.1 ≠ x.name) →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
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
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool)
        (DirPutStrPostPlaced A x s0 stk R)
        (DirPutStrPanicPlaced A x s0 stk R) := by
  intro cal suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact (hsuf rfl).elim
  | cons e rest ih =>
    intro pre s _hsuf hsplit hpre_ne hcrl hpc hrun hsp_align hsp htr hhigh
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
    have hbcmp := bcmp_lscro_ok_at_dirPutStr_543 H hBcmp
    generalize hcur_raw : ptr + BitVec.ofNat 64 (pre.length * 48) = curBase at hx25
    have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur_raw.symm⟩
    clear hcur_raw
    have hlen_split : x.dir.changed.length = pre.length + (rest.length + 1) := by
      rw [hsplit, List.length_append, List.length_cons]
    let _ := hlen_split
    have hlatch : ∀ (sl : State),
        e.1 ≠ x.name →
        StoreKit.LibsignalCodeRoLoaded lsmpl sl.mem →
        sl.pc = atOff543 120 →
        sl.status = .Running →
        sl.spAligned = true →
        sl.sp = s0.sp - 80#64 →
        sl.trace = s0.trace →
        PresHigh s0 sl →
        sl.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
        sl.readReg64 .x20 = x.bytesV →
        sl.readReg64 .x21 = namePtr →
        sl.readReg64 .x22 = x.self →
        sl.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
        sl.readReg64 .x24 = ptr →
        sl.readReg64 .x25 = curBase + 32#64 →
        sl.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48) →
        SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) sl
          ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool)
          (DirPutStrPostPlaced A x s0 stk R)
          (DirPutStrPanicPlaced A x s0 stk R) := by
      intro sl he_ne hcrl_l hpcl hrunl hspal hspl htrl hhighl
        hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26
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
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
        · subst hP2
          let _ := hr25
          let _ := hr26_48
          apply sepWPp_eq_pre
          · exact step_miss_543 hgrow x R s0 s2 cap ptr namePtr bCap bPtr
              hstk hstk_max hlen32 hmiss_all hcrl_s2
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
          · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl
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
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
        · subst hP2
          let _ := hne_48
          let _ := hx25_add
          let _ := hx26_sub
          let _ := hr25
          let _ := hr26
          apply sepWPp_eq_pre
          · exact ih (pre ++ [e]) s2 (List.cons_ne_nil _ _)
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
          · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl
    have hcap_ne : ∀ (h : x.dir.changed.length ≤ cap.toNat), cap ≠ 0 := by
      intro h h0
      subst h0
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      omega
    have hvbuf_open :
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ⊢
          ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
            (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
              (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A eCap ePtr e.1 ∗
              vecU8 A (curBase + 24#64) e.2 ∗
              A.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A) 48 ptr pre ∗
              arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48)) := by
      unfold vecBuf
      refine Entails.pure_left fun ⟨hle_c, hbnd_c, hptr_c⟩ => ?_
      have hcn := hcap_ne hle_c
      simp only [hcn, ↓reduceIte]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c, hcn⟩ ?_
      have happ : arrayAt (dirEntryAt A) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            dirEntryAt A e curBase ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
      rw [happ]
      unfold dirEntryAt
      have hv1 : vecU8 A curBase e.1 =
          ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1 := by
        unfold vecU8
        simp only [vecU8At_eq_header_heap]
      rw [hv1]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun eCap => Entails.trans ?_ (Entails.sepExists_intro eCap)
      refine Entails.sepExists_elim fun ePtr => Entails.trans ?_ (Entails.sepExists_intro ePtr)
      exact entails_eq (by ac_rfl)
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvbuf_open))))
    rw [show ∀ (A1 A2 A3 P0 E1 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ E1) ∗ Z =
            P0 ∗ E1 ∗ A1 ∗ A2 ∗ A3 ∗ Z from
          fun _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨hle_c, hbnd_c, hptr_c, hcap_c⟩ => ?_
    refine sepWPp_exists_left fun eCap => ?_
    try simp only [sepConj_assoc]
    refine sepWPp_exists_left fun ePtr => ?_
    try simp only [sepConj_assoc]
    have he_len_pull :
        vecU8Heap A eCap ePtr e.1 =
          ⌜e.1.length < 2 ^ 63⌝ ∗ vecU8Heap A eCap ePtr e.1 := by
      apply Entails.antisymm
      · unfold vecU8Heap
        refine Entails.pure_left fun ⟨h1, h2, h3⟩ => ?_
        exact Entails.pure_right (by omega) (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
      · exact Entails.pure_left fun _ => Entails.refl _
    rw [he_len_pull]
    rw [show ∀ (C0 C1 C2 P0 H1 Z : SepProp),
          C0 ∗ C1 ∗ C2 ∗ (P0 ∗ H1) ∗ Z = P0 ∗ C0 ∗ C1 ∗ C2 ∗ H1 ∗ Z from
          fun _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun he_len63 => ?_
    let _ := he_len63
    have hvbuf_close :
        (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
          ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
          vecU8Heap A eCap ePtr e.1 ∗
          vecU8 A (curBase + 24#64) e.2 ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ⊢
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed := by
      have he1 := vecU8_of_header_heap A curBase eCap ePtr e.1
      unfold vecBuf
      simp only [hcap_c, ↓reduceIte]
      have happ : arrayAt (dirEntryAt A) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            (vecU8 A curBase e.1 ∗ vecU8 A (curBase + 24#64) e.2) ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
        unfold dirEntryAt
        ac_rfl
      rw [happ]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c⟩ ?_
      rw [show (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1 ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) =
          ((curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1) ∗
          (A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48)) by ac_rfl]
      exact Entails.trans (sepConj_mono_left he1) (entails_eq (by ac_rfl))
    by_cases hlen_eq : e.1.length = x.name.length
    · have hlen_beq :
          (BitVec.ofNat 64 e.1.length == BitVec.ofNat 64 x.name.length) = true := by
        rw [hlen_eq]; exact beq_self_eq_true _
      apply sepWPp_cut_rebase_543 (mid := lsρ cliBcmpName) hcrl
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hlen_beq
        have hsp_s1 : s1.sp = s0.sp - 80#64 := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp
        have htr_s1 : s1.trace = s0.trace := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr
        have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
          ofNat_toNat_of_lt (by omega)
        rw [vecU8Heap_expose_bytes A eCap ePtr e.1, nameBuf_expose_bytes A namePtr x.name,
          stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
        apply call_lscro_wpp hbcmp ⟨ePtr, false, e.1, namePtr, false, x.name⟩
          (ret_pc := atOff543 160)
          (F := (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Rest A eCap ePtr e.1 ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            nameBufRest A namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0 ∗
            A.pool)
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
            try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            repeat rw [ite_false_eq]
            repeat rw [bv_sub_eq_add_neg64]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl)
          (hpan := fun _ => panic_false_wpp_543)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro sm hpcm hrunm hspm hcsm hcrlm
        dsimp only [cliBcmpSpec, SpqrV1.ChainProofs.bytesAt]
        try simp only [sepConj_assoc]
        refine sepWPp_pure_left fun ⟨hbcmp_iff, htr_sm0⟩ => ?_
        have hstk_back :
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
              stackAt s1.sp extHookStack =
              stackAt (s0.sp - 80#64) cal := by
          rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
        have hhigh_s1 : PresHigh s0 s1 :=
          ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
        have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
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
        by_cases heq_name : e.1 = x.name
        · have hw0_z :
              (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = true :=
            w0_cbnz_zero (hbcmp_iff.mpr heq_name)
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
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
          · subst hP2
            let _ := hw0_z
            let _ := hx22_sm
            let _ := hx23_sm
            let _ := hx24_sm
            let _ := hx26_sm
            let _ := hvbuf_close
            let _ := hlatch
            have hprep_hit :
                (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
                  (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
                  ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
                  vecU8Rest A eCap ePtr e.1 ∗
                  vecU8 A (curBase + 24#64) e.2 ∗
                  A.live ptr (cap.toNat * 48) 8 ∗
                  arrayAt (dirEntryAt A) 48 ptr pre ∗
                  arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                  memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                    ((cap.toNat - x.dir.changed.length) * 48) ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBufRest A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ∗
                  A.pool ⊢
                ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                    ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
                    A.live ptr (cap.toNat * 48) 8 ∗
                    arrayAt (dirEntryAt A) 48 ptr pre ∗
                    vecU8 A curBase x.name ∗
                    ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
                    ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
                    vecU8Heap A oldCap oldPtr e.2 ∗
                    arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                    memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
                      ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
                    strRefAt (x.self + 0x18#64) x.dir.path ∗
                    SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                    nameBuf A namePtr x.name ∗
                    (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                    ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                    vecU8Heap A bCap bPtr x.bytes ∗
                    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                    stackAt (s0.sp - 80#64) cal ∗
                    savedSlots s0 ∗
                    A.pool := by
              have ha32 : curBase + 24#64 + 8#64 = curBase + 32#64 := by bv_omega
              have ha40 : curBase + 24#64 + 16#64 = curBase + 40#64 := by bv_omega
              have hv2 : vecU8 A (curBase + 24#64) e.2 =
                  ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
                    ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
                    ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
                    vecU8Heap A oldCap oldPtr e.2 := by
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
                    ((ePtr ↦ₛ e.1) ∗ vecU8Rest A eCap ePtr e.1) ⊢
                    vecU8 A curBase x.name := by
                rw [← vecU8Heap_expose_bytes, heq_name]
                exact vecU8_of_header_heap A curBase eCap ePtr x.name
              rw [← hstk_back, ← hlen_hit, nameBuf_expose_bytes A namePtr x.name]
              rw [show ∀ (B1 B2 StkE C0 C1 C2 ER O0 O1 O2 OH L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
                    B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ (O0 ∗ O1 ∗ O2 ∗ OH) ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                      S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
                    (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER)) ∗
                    (S0 ∗ S1 ∗ S2 ∗ L0 ∗ P0 ∗ O0 ∗ O1 ∗ O2 ∗ OH ∗ R0 ∗ M0 ∗
                      Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
                    intros; ac_rfl]
              exact Entails.trans (sepConj_mono_left he_assemble) (entails_eq (by ac_rfl))
            apply sepWPp_eq_pre
            · apply sepWPp_weaken_pre hprep_hit
              have hpull_ex1 : ∀ (Φ : BitVec 64 → SepProp), (∃∗ a, Φ a) = (∃∗ a, Φ a) ∗ emp :=
                fun _ => (sepConj_emp _).symm
              rw [hpull_ex1]
              refine sepWPp_exists_left fun oldCap => ?_
              rw [sepConj_emp, hpull_ex1]
              refine sepWPp_exists_left fun oldPtr => ?_
              rw [sepConj_emp]
              exact step_hit_543 hC x R s0 s2 pre rest e.2 cap ptr curBase namePtr bCap bPtr oldCap oldPtr
                hstk hstk_max hname32 hput_eq hcur'.out (by rw [← hlen_hit]; exact hle_c) hbnd_c hptr_c hcap_c
                hsp_align0 hcrl_s2
                (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
                (by
                  have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                  have hsp_eq' : sm.sp = s.sp := hspm.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm])
                  simpa only [State.spAligned, hsp_eq, hsp_eq'] using hsp_align)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspm.trans hsp_s1)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htr_sm0.trans htr_s1)
                ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.2⟩
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx19_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx20_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx21_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_sm)
            · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
              repeat rw [ite_false_eq]
              repeat rw [bv_sub_eq_add_neg64]
              try rw [emp_sepConj]
              try rw [sepConj_emp]
              try simp only [wp_norm, arm64_norm]
              try rw [Nat.mul_comm 48]
              try ac_rfl
        · have hw0_nz :
              (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
            w0_cbnz_nonzero (fun hz => heq_name (hbcmp_iff.mp hz))
          apply sepWPp_cut_rebase_543 (mid := atOff543 120) hcrlm
          dsimp +zetaDelta only [atOff543] at hpcm ⊢
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s2 P2 hcrl_s2 ⟨hs2, hP2⟩
          · subst hP2
            let _ := hw0_nz
            have hclose_miss :
                (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
                  (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
                  ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
                  vecU8Rest A eCap ePtr e.1 ∗
                  vecU8 A (curBase + 24#64) e.2 ∗
                  A.live ptr (cap.toNat * 48) 8 ∗
                  arrayAt (dirEntryAt A) 48 ptr pre ∗
                  arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                  memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                    ((cap.toNat - x.dir.changed.length) * 48) ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  (x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBufRest A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ∗
                  A.pool ⊢
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBuf A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  stackAt (s0.sp - 80#64) cal ∗
                  savedSlots s0 ∗
                  A.pool := by
              rw [← hstk_back, nameBuf_expose_bytes A namePtr x.name]
              rw [show ∀ (B1 B2 StkE C0 C1 C2 ER VO L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
                    B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                      S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
                    (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER) ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗
                    (S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
                    intros; ac_rfl]
              rw [← vecU8Heap_expose_bytes]
              exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by ac_rfl))
            apply sepWPp_eq_pre
            · apply sepWPp_weaken_pre hclose_miss
              exact hlatch s2 heq_name hcrl_s2
                (by rw [hs2]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
                (by
                  have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                  have hsp_eq' : sm.sp = s.sp := hspm.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm])
                  simpa only [State.spAligned, hsp_eq, hsp_eq'] using hsp_align)
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
            · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
              repeat rw [ite_false_eq]
              repeat rw [bv_sub_eq_add_neg64]
              try rw [emp_sepConj]
              try rw [sepConj_emp]
              try simp only [wp_norm, arm64_norm]
              try rw [Nat.mul_comm 48]
              try ac_rfl
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
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hlen_beq
        let _ := hbcmp
        have hclose_len :
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A eCap ePtr e.1 ∗
              vecU8 A (curBase + 24#64) e.2 ∗
              A.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A) 48 ptr pre ∗
              arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48) ∗
              (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool ⊢
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool := by
          rw [show ∀ (C0 C1 C2 EH VO L0 P0 R0 M0 Z : SepProp),
                C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗ Z =
                  (C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗ Z from
                fun _ _ _ _ _ _ _ _ _ _ => by ac_rfl]
          exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by ac_rfl))
        apply sepWPp_eq_pre
        · apply sepWPp_weaken_pre hclose_len
          exact hlatch s1 he_ne_name hcrl_s1
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
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl
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

private theorem pull_alloc_pure_right (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ P1 ∗ P2 ∗ R := by
  ac_rfl

private theorem shim_pre_eq (s : State) :
    session2ShimSpecX.pre () s = ⌜True⌝ ∗ stackAt s.sp extHookStack := by
  apply Entails.antisymm
  · dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
    exact Entails.pure_right trivial (Entails.refl _)
  · dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
    exact Entails.pure_left fun _ => Entails.refl _

/-- Shared loop preheader `+104..+116` on Block `543` when `x.dir.changed = e0 :: rest0`. -/
private theorem step_preheader_543 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 s : State)
    (e0 : List (BitVec 8) × List (BitVec 8))
    (rest0 : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hchanged : x.dir.changed = e0 :: rest0)
    (hsp_align0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
    (hx24 : s.readReg64 .x24 = ptr) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool)
      (DirPutStrPostPlaced A x s0 stk R)
      (DirPutStrPanicPlaced A x s0 stk R) := by
  intro cal
  apply sepWPp_cut_rebase_543 (mid := atOff543 132) hcrl
  dsimp +zetaDelta only [atOff543] at hpc ⊢
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
  · subst hP1
    have hx25_init :
        ptr + 32#64 =
          ptr + BitVec.ofNat 64 (([] : List (List (BitVec 8) × List (BitVec 8))).length * 48) + 32#64 := by
      change ptr + 32#64 = ptr + 0#64 + 32#64
      bv_omega
    have hx26_init :
        ((BitVec.ofNat 64 (e0 :: rest0).length + (BitVec.ofNat 64 (e0 :: rest0).length) <<< 1) <<< 4) =
          BitVec.ofNat 64 ((e0 :: rest0).length * 48) :=
      preheader_mul48 _
    let _ := hx23
    let _ := hx24
    let _ := hx25_init
    let _ := hx26_init
    apply sepWPp_eq_pre
    · exact step_loop_543 hC hBcmp hgrow x R s0 cap ptr namePtr bCap bPtr
        hstk hstk_max hname32 hlen32 hsp_align0 (e0 :: rest0) [] s1
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
        (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26_init)
    · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
      try simp only [sp_slot_norm]
      try rw [emp_sepConj]
      try rw [sepConj_emp]
      try simp only [wp_norm, arm64_norm]
      try rw [Nat.mul_comm 48]
      try ac_rfl
/-- `Dir::put::<&str>` satisfies `dirPutStrSpecPlaced A stk` on Block 543 under `[LibsignalPlacement]`. -/
theorem dirPutStr_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543) (dirPutStrSpecPlaced A stk) := by
  have hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A growStk) :=
    ls_transfer_lscro (callerProg := lsProg_543 H) hGrow (by decide) hjGrow hjGrow_unmut
  clear hGrow
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align0
  rw [show lsmpl.base 543 = atOff543 0 by dsimp [atOff543]; rw [BitVec.add_zero]; rfl] at hpc
  obtain ⟨hcrl0, hpre_inner⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [dirPutStrSpecPlaced] at hpre_inner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_inner
  rcases hpre_inner with ⟨⟨hx0, hx1, hx2_nat, hx3, hname32, hlen32⟩, hmem_spatial⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.name.length :=
    ofNat_eq_of_toNat_eq hx2_nat
  have hstk_max : stk ≤ 2 ^ 64 := by
    have hm1 : s0.mem ⊨ vecU8 A x.bytesV x.bytes ∗ stackAt s0.sp stk ∗
        (dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          A.pool ∗ R) :=
      satisfies_eq' (by ac_rfl) hmem_spatial
    unfold vecU8 at hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
    rcases hm1 with ⟨bc, bp, hmb⟩
    rw [vecU8At_eq_header_heap] at hmb
    unfold stackAt at hmb
    have hmb' : s0.mem ⊨ (x.bytesV ↦₆₄ bc) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
        (((x.bytesV + 8#64) ↦₆₄ bp) ∗ ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bc bp x.bytes ∗
          (dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            A.pool ∗ R)) :=
      satisfies_eq' (by ac_rfl) hmb
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
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        A.pool) ∗ R :=
    satisfies_eq' (by ac_rfl) hm_init
  refine ⟨_, R, hm_ord, ?_⟩
  clear hpre hm_init hm_ord
  have hshim := shim_ok_at_dirPutStr_543 hC
  have halloc := alloc_ok_at_dirPutStr_543 hC
  have hmemcpy := memcpy_bytesAt_lscro_ok_at_543 A H hC hRO x.nameRo
  by_cases hnil : x.name = []
  · have hx2_zero : s0.readReg64 .x2 = 0#64 := by
      rw [hx2, hnil]; rfl
    have hname_fold :
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ⊢
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ nameBuf A 1#64 x.name := by
      rw [hnil]
      exact Entails.trans (entails_eq' (sepConj_emp _).symm) (sepConj_mono_right (nameBuf_of_nil A))
    cases hdir_cases : x.dir.changed with
    | nil =>
      apply sepWPp_cut_rebase_543 (mid := atOff543 244) hcrl0
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
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
        · exact step_miss_543 hgrow x R s0 s1 cap ptr 1#64 bCap bPtr
            hstk hstk_max hlen32
            (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
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
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl
    | cons e0 rest0 =>
      have hlen_pos : 0 < (e0 :: rest0).length := by simp
      have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
        beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
      apply sepWPp_cut_rebase_543 (mid := atOff543 104) hcrl0
      dsimp +zetaDelta only [atOff543] at hpc ⊢
      wp_steps
      apply SepWP.fold hname_fold (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hshim
        let _ := halloc
        let _ := hmemcpy
        let _ := hx1
        let _ := hx2
        let _ := hx2_zero
        let _ := hlen_nz
        rw [← hdir_cases]
        apply sepWPp_eq_pre
        · exact step_preheader_543 hC hBcmp hgrow x R s0 s1 e0 rest0 cap ptr 1#64 bCap bPtr
            hstk hstk_max hname32 hlen32 hdir_cases hsp_align0 hcrl_s1
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
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl
  · have hname_pos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx2_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hname_pos (by omega)
    have hname_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    have hlay_name : LayoutOk x.name.length 1 :=
      layoutOk_u8_of_lt hname_pos (by omega)
    apply sepWPp_cut_rebase_543 (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
    dsimp +zetaDelta only [atOff543] at hpc ⊢
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
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
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0 ∗
          A.pool)
        (hcrl := hcrl_s1)
        (hpc := by rw [hs1]; rfl)
        (hrun := by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := hspa_s1)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff543]; try simp only [wp_norm, arm64_norm])
        (hspec := shim_pre_eq s1)
        (hφ := trivial)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64']
          try simp only [sp_slot_norm]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl)
        (hpan := fun _ => panic_false_wpp_543)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro s2 hpcs2 hruns2 hsps2 hcss2 hcrls2
      dsimp only [session2ShimSpecX, withStack, sessionShimSpec]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun htr_s20 => ?_
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
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s3 P3 hcrl_s3 ⟨hs3, hP3⟩
      · subst hP3
        have hsp_s3 : s3.sp = s1.sp := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact hsps2
        have hspa_s3 : s3.spAligned = true := by
          simpa only [State.spAligned, hsp_s3] using hspa_s1
        have htr_s3 : s3.trace = s0.trace := by
          rw [hs3]; try simp only [wp_norm, arm64_norm]; try exact htr_s2
        rw [← hsp_s3]
        apply call_lscro_wpp halloc (x.name.length, 1)
          (ret_pc := atOff543 60)
          (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
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
                  hlay_name⟩)
          (hP := by
            try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            repeat rw [bv_sub_eq_add_neg64']
            try simp only [sp_slot_norm]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl)
          (hpan := fun _ => panic_false_wpp_543)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro s4 hpcs4 hruns4 hsps4 hcss4 hcrls4
        dsimp only [rustAllocSpecWithStack]
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
        by_cases hoom : s4.readReg64 .x0 = 0
        · have hoom_beq_z : (s4.readReg64 .x0 == 0#64) = true := beq_iff_eq.mpr hoom
          simp only [hoom, ↓reduceIte]
          try simp only [sepConj_assoc]
          rw [pull_alloc_pure_right]
          refine sepWPp_pure_left fun htrace_oom => ?_
          apply sepWPp_cut_rebase_543 (mid := lsρ lsHandleErrorSymCli) hcrls4
          dsimp +zetaDelta only [atOff543] at hpcs4 ⊢
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s5 P5 _hcrl_s5 ⟨hs5, hP5⟩
          · subst hP5
            let _ := hBcmp
            let _ := hgrow
            let _ := hmemcpy
            let _ := hsp_s4
            let _ := hspa_s4
            let _ := hhigh_s4
            let _ := hx19_s4
            let _ := hx20_s4
            let _ := hx22_s4
            let _ := hx23_s4
            let _ := hoom_beq_z
            let _ := hlen32
            refine SepWPp.panic
              (by rw [hs5]; simp only [wp_norm, arm64_norm]; exact hruns4)
              (by
                have hpc5 : s5.pc = lsρ lsHandleErrorSymCli := by
                  rw [hs5]; rfl
                rw [hpc5]
                exact panic_at_dirPutStr_handle_error_543 hpan)
              fun hm_pan => ?_
            exact allowPanic_panicked
              (allocFailedIn_panicked (allocFailedIn_of_append (by
                rw [hs5]
                try simp only [wp_norm, arm64_norm]
                rw [htrace_oom, htr_s3])))
              hm_pan
        · have hoom_raw : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom
          let allocPtr := s4.readReg64 .x0
          simp only [hoom, ↓reduceIte]
          try simp only [sepConj_assoc]
          rw [pull_alloc_pure_right]
          refine sepWPp_pure_left fun ⟨_halign_ptr, htr_s43⟩ => ?_
          have htr_s4 : s4.trace = s0.trace := htr_s43.trans htr_s3
          apply sepWPp_cut_rebase_543 (mid := lsρ memcpyName) hcrls4
          dsimp +zetaDelta only [atOff543] at hpcs4 ⊢
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s5 P5 hcrl_s5 ⟨hs5, hP5⟩
          · subst hP5
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
              (F := A.pool ∗
                A.live allocPtr x.name.length 1 ∗
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                strRefAt (x.self + 0x18#64) x.dir.path ∗
                (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                vecU8Heap A bCap bPtr x.bytes ∗
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
                try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt, allocPtr]
                repeat rw [bv_sub_eq_add_neg64']
                try simp only [sp_slot_norm]
                try rw [emp_sepConj]
                try rw [sepConj_emp]
                try simp only [wp_norm, arm64_norm]
                try rw [Nat.mul_comm 48]
                try ac_rfl)
              (hpan := fun _ => panic_false_wpp_543)
              (hexit := fun _ _ => rfl)
              (hoom := fun _ => rfl)
            intro s6 hpcs6 hruns6 hsps6 hcss6 hcrls6
            dsimp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec]
            try simp only [sepConj_assoc]
            refine sepWPp_pure_left fun ⟨_hx0_mc, htr_s65⟩ => ?_
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
            have hpost_mc_ent :
                (allocPtr ↦ₛ x.name) ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  stackAt s5.sp extHookStack ∗
                  A.pool ∗
                  A.live allocPtr x.name.length 1 ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s5.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ⊢
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBuf A allocPtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  stackAt (s0.sp - 80#64) cal ∗
                  savedSlots s0 ∗
                  A.pool := by
              rw [show ∀ (BS NB Stk5 Pool Live S0 S1 S2 VB Path B0 B1 B2 BH M0 MC Sav : SepProp),
                    BS ∗ NB ∗ Stk5 ∗ Pool ∗ Live ∗ S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗
                      B0 ∗ B1 ∗ B2 ∗ BH ∗ M0 ∗ MC ∗ Sav =
                    (Live ∗ BS) ∗
                      (S0 ∗ S1 ∗ S2 ∗ VB ∗ Path ∗ NB ∗ B0 ∗ B1 ∗ B2 ∗ BH ∗
                        M0 ∗ (MC ∗ Stk5) ∗ Sav ∗ Pool) by intros; ac_rfl]
              rw [hstk_merge6]
              exact Entails.trans
                (sepConj_mono_left (nameBuf_of_nonempty A allocPtr x.name hnil hoom (by omega)))
                (entails_eq' (by ac_rfl))
            apply sepWPp_weaken_pre hpost_mc_ent
            cases hdir_cases : x.dir.changed with
            | nil =>
              apply sepWPp_cut_rebase_543 (mid := atOff543 244) hcrls6
              dsimp +zetaDelta only [atOff543] at hpcs6 ⊢
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro s7 P7 hcrl_s7 ⟨hs7, hP7⟩
              · subst hP7
                let _ := hBcmp
                let _ := hC
                rw [← hdir_cases]
                apply sepWPp_eq_pre
                · exact step_miss_543 hgrow x R s0 s7 cap ptr allocPtr bCap bPtr
                    hstk hstk_max hlen32
                    (by rw [hdir_cases]; intro _ hm; exact (List.not_mem_nil hm).elim)
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
                · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
                  try simp only [sp_slot_norm]
                  try rw [emp_sepConj]
                  try rw [sepConj_emp]
                  try simp only [wp_norm, arm64_norm]
                  try rw [Nat.mul_comm 48]
                  try ac_rfl
            | cons e0 rest0 =>
              have hlen_pos : 0 < (e0 :: rest0).length := by simp
              have hlen_nz : (BitVec.ofNat 64 (e0 :: rest0).length == 0#64) = false :=
                beq_ofNat_zero_eq_false hlen_pos (by rw [← hdir_cases]; omega)
              apply sepWPp_cut_rebase_543 (mid := atOff543 104) hcrls6
              dsimp +zetaDelta only [atOff543] at hpcs6 ⊢
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro s7 P7 hcrl_s7 ⟨hs7, hP7⟩
              · subst hP7
                let _ := hlen_nz
                rw [← hdir_cases]
                apply sepWPp_eq_pre
                · exact step_preheader_543 hC hBcmp hgrow x R s0 s7 e0 rest0 cap ptr allocPtr bCap bPtr
                    hstk hstk_max hname32 hlen32 hdir_cases hsp_align0 hcrl_s7
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
                · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
                  try simp only [sp_slot_norm]
                  try rw [emp_sepConj]
                  try rw [sepConj_emp]
                  try simp only [wp_norm, arm64_norm]
                  try rw [Nat.mul_comm 48]
                  try ac_rfl

/-- Caller-transferable `[LibsignalPlacement]` `Dir::put::<&str>` contract for any block `< 619`. -/
theorem dirPutStr_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg growProg : Program} {i jGrow : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg growProg jGrow H]
    {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hi : i < 619 := by decide)
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 543) (dirPutStrSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 543)
    (dirPutStr_placed_ok_of_deps hC hpan hRO hBcmp hjGrow hjGrow_unmut hGrow hstk) hi

end CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers

namespace CryptoVerification.SignalSession.Cli.PutStr

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

/-- `Dir::put::<&str>` satisfies `dirPutStrSpecPlaced A stk` on Block 543 under `[LibsignalPlacement]`. -/
theorem dirPutStr_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543) (dirPutStrSpecPlaced A stk) :=
  PlacedHelpers.dirPutStr_placed_ok_of_deps hC hpan hRO hBcmp hjGrow hjGrow_unmut hGrow hstk

/-- Caller-transferable `[LibsignalPlacement]` `Dir::put::<&str>` contract for any block `< 619`. -/
theorem dirPutStr_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg growProg : Program} {i jGrow : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg growProg jGrow H]
    {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hi : i < 619 := by decide)
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 543) (dirPutStrSpecPlaced A stk) :=
  PlacedHelpers.dirPutStr_placed_caller_ok_of_deps hC hpan hRO hBcmp hGrow hstk hi hjGrow hjGrow_unmut

end CryptoVerification.SignalSession.Cli.PutStr
