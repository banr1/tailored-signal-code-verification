/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
import all Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 3 Call Combinators, Relative Targets, and Stack Split Helpers

Provides `[LibsignalPlacement]` relative symbol targets and `SepWPp` call combinators
(`s3_step_to_placed`, `s3_call_placed`, `s3_call_alloc_placed`, `s3_panic_at_placed`) on
`initProgPlaced`, while re-exporting pure stack-split helpers from `Stage3Lemmas/Defs`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## Relative call and hook targets on `initProgPlaced` -/

theorem initEntryPlaced_eq [LibsignalPlacement] :
    initEntryPlaced = (blkPl_521).base := rfl

theorem initPcPlaced_eq [LibsignalPlacement] (k : Nat) :
    initPcPlaced k = (blkPl_521).base + BitVec.ofNat 64 k := rfl

theorem shim_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl session2ShimSpecX) := by
  have h := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.shim extHookStack (by decide) (by decide))
  refine subroutine_ok_mono h (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withStack,
      sessionShimSpec, session2ShimSpecX] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withStack,
      sessionShimSpec, session2ShimSpecX] at hpost ⊢
    exact hpost

theorem alloc_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustAllocSpecWithStack A extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.alloc

theorem dealloc_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc

theorem memcpy_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX) := by
  have h := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.session_memcpy_region extHookStack (by decide) (by decide))
  refine subroutine_ok_mono h (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem kyberEncaps_ok_at_init_placed [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsKemEncapsSym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.Initiator.kyberEncapsStubSpec
          (Pqxdh.Initiator.initiatorModelPrims X ⟨W.C, W.Q⟩))) := by
  have hraw : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsKemEncapsSym)
      (Pqxdh.Initiator.kyberEncapsStubSpec
        (Pqxdh.Initiator.initiatorModelPrims X ⟨W.C, W.Q⟩)) := by
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    exact ls_hook_ok_ultra_of_mem
      ⟨CryptoVerification.E2E.kemEncapsHook W.Q.encaps, hh.kemEncaps,
        Pqxdh.Initiator.kemEncapsHook_ok_initiatorModelPrims X ⟨W.C, W.Q⟩⟩
  exact LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hraw

abbrev lsRawVecHandleErrorSymS3 : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev lsAllocErrorSymS3 : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

theorem panic_raw_vec_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    (initProgPlaced mmpl gh W).externAt? (lsρ lsRawVecHandleErrorSymS3) = some Rust.panicked := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  exact (ls_externAt?_of_mem (sym := lsRawVecHandleErrorSymS3)).trans hh.panic_raw

theorem panic_alloc_error_at_init_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    (initProgPlaced mmpl gh W).externAt? (lsρ lsAllocErrorSymS3) = some Rust.panicked := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  exact (ls_externAt?_of_mem (sym := lsAllocErrorSymS3)).trans hh.panic_alloc

/-! ## `SepWPp` stepping and call combinators -/

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiatePlaced.spAligned_cur_s3
    [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem _root_.CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InInitiatePlaced.of_call_s3
    [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {s0 s sm : State} {k_in k_out : Nat}
    (h : InInitiatePlaced s0 s k_in)
    (hsteps : Steps (initProgPlaced mmpl gh W) s sm)
    (hpcm : sm.pc = initPcPlaced k_out)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (htrm : sm.trace = s.trace) :
    InInitiatePlaced s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
      (by simpa using htrm) NoFsEv.nil
  exact
    { pc := hpcm
      run := hrunm
      sp := hspm.trans h.sp
      fp := hfp.trans h.fp
      x19 := hx19.trans h.x19
      files0 := hfs_eq.trans h.files0
      inv := h.inv.of_keepsFrozen hsteps.keepsFrozen
      vregs := hvregs.trans h.vregs
      spAligned := h.spAligned }

/-- Steps a trace-preserving basic block `s → mid` while lifting `LibsignalCodeRoLoaded` and `fs.files`. -/
theorem s3_step_to_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {mid ret : BitVec 64} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP (initProgPlaced mmpl gh W) mid s P (fun sm Pm =>
      sm.trace = s.trace ∧
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
        sm.fs.files = s.fs.files →
        SepWPp (initProgPlaced mmpl gh W) ret sm Pm Q Qp (initOom s0)))) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp (initOom s0) := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, htrm, hnext⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (hh.fs (prog := initProgPlaced mmpl gh W)) hsteps (evs := [])
        (by simpa using htrm) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_keepsFrozen hsteps.keepsFrozen) hfs_eq R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem initPanicPostPlaced_of_allocFailed [LibsignalPlacement] {A : RustAlloc} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sf : State} (Pf : SepProp)
    (h : allocFailedIn s0 sf) :
    InitPanicPostPlaced A S x stk s0 sf Pf := by
  simp only [InitPanicPostPlaced, initSlotSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  exact Entails.pure_right (Or.inr h) (Entails.top_right fun _ => trivial)

/-- `subroutine_ok` call combinator on `initProgPlaced` for `withLsCodeRoLoaded lsmpl spec` callees. -/
theorem s3_call_placed [LibsignalPlacement] {α : Type} {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = initPcPlaced k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s.trace → InInitiatePlaced s0 sm k_out) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine sepWPp_conseq_oom hpre ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨ spec.pre g s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre g s ∗ (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall g (F ∗ R') hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hctrl.inv.of_keepsFrozen hsteps.keepsFrozen)
        (InInitiatePlaced.of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic g s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by
      simpa only [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan,
      hpanic sm _ (initPanicPostPlaced_of_allocFailed _ halloc0)⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

/-- `__rustc::__rust_alloc` call combinator on `initProgPlaced`. -/
theorem s3_call_alloc_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in)
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_null : ∀ sm : State,
      sm.pc = initPcPlaced k_out → sm.status = .Running →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s.trace ++ [allocFailedEvent] →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0))
    (hnext_ok : ∀ sm : State,
      InInitiatePlaced s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have halloc := alloc_ok_at_init_placed hh
  have hpre' : P ⊢ (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustAllocSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlay⟩ (Entails.of_eq (by ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_
  intro R' hm hL
  have hm_pre0 : s.mem ⊨
      (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  have hm_pre : s.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustAllocSpecWithStack A extHookStack)).pre (sz, 1) s ∗ (F ∗ R') :=
    satisfies_withLsCodeRoLoaded_pre hctrl.inv hm_pre0
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome halloc (sz, 1) (F ∗ R') hpc hctrl.run hm_pre
      (InInitiatePlaced.spAligned_cur_s3 hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [hlr] at hpcm
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, rustAllocSpecWithStack] at hpost
    by_cases hnull : sm.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨
          ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s.sp extHookStack ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      obtain ⟨htrm, hmem_null'⟩ := hpost'
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_null sm hpcm hrunm hnull htrm R' hmem_null' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨
          ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            ((A.pool ∗ stackAt s.sp extHookStack ∗
              A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      obtain ⟨⟨_, htrm⟩, hmem_ok'⟩ := hpost'
      have hctrl' := InInitiatePlaced.of_call_s3 hh hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_ok sm hctrl' hcsm hnull htrm R' hmem_ok' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · simp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Discharges `Rust.panicked` on `initProgPlaced` once `allocFailedIn s0 s` holds. -/
theorem s3_panic_at_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hext : (initProgPlaced mmpl gh W).externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  SepWPp.panic (P := P) (hrun := hrun) (hext := hext)
    (hqp := hpanic (Rust.panicked s) P
      (initPanicPostPlaced_of_allocFailed P
        (by simpa only [allocFailedIn, Rust.panicked] using hfail)))

theorem s3_shim_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      sm.trace = s.trace → SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ session2ShimSpecX.pre () s ∗ F := hpre
  refine s3_call_placed hh (shim_ok_at_init_placed hh) () F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2ShimSpecX] at h
  · intro _ _ _ h; simp [session2ShimSpecX] at h
  · intro _ _ h; simp [session2ShimSpecX] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2ShimSpecX, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

theorem s3_memcpy_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsρ memcpyName)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ session2MemcpySpecX.pre (dst, src, bs) s ∗ F := Entails.trans hpre (by
    simp only [session2MemcpySpecX, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by ac_rfl)))
  refine s3_call_placed hh (memcpy_ok_at_init_placed hh) (dst, src, bs) F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [session2MemcpySpecX] at h
  · intro _ _ _ h; simp [session2MemcpySpecX] at h
  · intro _ _ h; simp [session2MemcpySpecX] at h
  · intro sm _ _ _ hcsm _ hof; simp only [session2MemcpySpecX, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm hx0m htrm)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
