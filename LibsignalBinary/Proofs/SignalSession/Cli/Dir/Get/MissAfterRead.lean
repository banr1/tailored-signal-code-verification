/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Hit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import ProofLib.SepLogic.WPp

/-!
# Post-I/O Result Construction (`+336`..`+508`) for `<signal_session::stores::Dir>::get`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `Ok(outBs)` branch at `+336`..`+376`: moves the 24-byte `Vec<u8>` header into `x.ret + 8`,
    writes `okTagVec`, and finishes via `step_epilogue_284` or `step_dealloc_epilogue_464`. -/
theorem step_after_read_ok
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {outBs : List (BitVec 8)}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : Except.ok outBs = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((((ioVecAt A (s0.sp - 112#64) (.ok outBs) ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail))
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  refine sepWPp_unfold_vecU8 fun outCap outPtr hout_le hout_cap_lt hout_ptr_ne => ?_
  have hcmn : (outCap + 1#64 == 0#64) = false := cap_cmn1_beq_zero_false hout_cap_lt
  have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by simp only [BitVec.add_assoc]; rfl
  have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by simp only [BitVec.add_assoc]; rfl
  have hrepack_out :
      ((x.ret + 8#64) ↦₆₄ outCap) ∗
        ((x.ret + 16#64) ↦₆₄ outPtr) ∗
        ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ∗
        (outPtr ↦ₛ outBs) ∗
        (if outCap = 0 then emp
         else A.live outPtr outCap.toNat 1 ∗
           memRegion (outPtr + BitVec.ofNat 64 outBs.length) (outCap.toNat - outBs.length)) ⊢
      vecU8 A (x.ret + 8#64) outBs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro outCap)
    refine Entails.trans ?_ (Entails.sepExists_intro outPtr)
    rw [vecU8At_expose, hret8, hret16]
    exact Entails.pure_right ⟨hout_le, hout_cap_lt, hout_ptr_ne⟩ (Entails.refl _)
  have hsp0_24 :
      ((s0.sp - 112#64) ↦₆₄ outCap) ∗
        ((s0.sp - 112#64 + 8#64) ↦₆₄ outPtr) ∗
        ((s0.sp - 112#64 + 16#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 336 44
  clear hfn
  generalize hentry_raw :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
  generalize hprog_raw :
    libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
  have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
  clear hentry_raw hprog_raw
  examples_hide_fetches
  by_cases hpcap : pathCap = 0
  · subst hpcap
    simp only [↓reduceIte, emp_sepConj]
    refine seq_frozen_state (mid := fnStart + 284#64) hfz ?_
    wp_steps
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.fold hp24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz_epi
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_epilogue_284 (r := .ok outBs) (Extra := dirGetRoBundle img.base w0 w1 wTail)
        hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2]⟩)
      (by sep_frame)
  · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
    simp only [hpcap, ↓reduceIte]
    refine seq_frozen_state (mid := fnStart + 464#64) hfz ?_
    wp_steps
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz_d
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_dealloc_epilogue_464 (r := .ok outBs)
        (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
        (Extra := dirGetRoBundle img.base w0 w1 wTail)
        hC hcstk hstk hfull hsp0_al hfz_d
        (by simp only [wp_norm, arm64_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hpcap hpth_cap_lt
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2]⟩)
      (by sep_frame)

/-- `Err(())` branch at `+336`..`+508`: allocates 22 bytes, copies `.rodata`, builds `speAt`,
    and finishes via `step_epilogue_284` or `step_dealloc_epilogue_464`. -/
theorem step_after_read_err
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : (Except.error () : Except Unit (List (BitVec 8))) = x.dir.get rd s0.fs.files x.name ∧
      s.trace = s0.trace) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((((ioVecAt A (s0.sp - 112#64) (.error ()) ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail))
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  have hsp0_24_err :
      ((s0.sp - 112#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 112#64 + 8#64) 16 ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)
  have hpfx_s : s0.trace <+: s.trace := ⟨[], by simp [hres.2]⟩
  have hadrp1 := adrp_add_unreadable_eq hb
    (by rw [Program.fnAddr_rebase, dirGet_fnOff] :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName =
        img.base + bv% (ls_off% "<libsignal_cli::stores::Dir>::get"))
  have hadrp2 := adrp_add_readOp_eq hb
    (by rw [Program.fnAddr_rebase, dirGet_fnOff] :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName =
        img.base + bv% (ls_off% "<libsignal_cli::stores::Dir>::get"))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hadrp1 hadrp2
  have hshim := hC.shim_ok_at dirGetName
    (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
  have halloc := hC.alloc_ok_at dirGetName
    (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc")
    (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
  have hpanic := panic_at_handle_error_dirGet img.base ext
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 336 12
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 380 84
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 500 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc
  clear hfn
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  generalize hentry_raw :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
  generalize hprog_raw :
    libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
  have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
  clear hentry_raw hprog_raw
  examples_hide_fetches
  refine seq_frozen_state
    (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hfz ?_
  wp_steps
  apply SepWP.fold hsp0_24_err (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfz1
  refine SepWPp.call_inImage_frame (x := ())
    (T := stackAt (s0.sp - 112#64) extHookStack)
    hshim hfz1 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs)
    (by simp only [withStack, sessionShimSpec, emp_sepConj, pure_true_sepConj, wp_norm, hsp])
    trivial (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQp_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hfz2 hsym2 => ?_)
  simp only [withStack, sessionShimSpec, wp_norm, hsp, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have hhcs1 : HighCalleeSaved s0 sf1 :=
    hhcs.of_step_call hcs1
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
  have hsp1_al : sf1.spAligned = true :=
    spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
  have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
  have hx19_1 : sf1.readReg64 .x19 = x.ret := by
    have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
  have hx21_1 : sf1.readReg64 .x21 = pathPtr := by
    have := hcs1.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
  have htr1_eq : sf1.trace = s.trace := htr1
  have hlay22 : LayoutOk 22 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine seq_frozen_state
    (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc"))
    hfz2 ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfz3
  refine SepWPp.call_inImage_frame (x := (22, 1))
    (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
    halloc hfz3 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp1_al)
    (by wp_norm_lhs) (by simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], hlay22⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQp_false)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hfz4 hsym4 => ?_)
  simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]
  have hhcs2 : HighCalleeSaved s0 sf2 :=
    hhcs1.of_step_call hcs2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
  have hsp2_al : sf2.spAligned = true :=
    spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
  have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
  have hx19_2 : sf2.readReg64 .x19 = x.ret := by
    have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
  have hx21_2 : sf2.readReg64 .x21 = pathPtr := by
    have := hcs2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21_1
  by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
    rw [ite_true_eq hoom]
    simp only [sepConj_assoc]
    refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
      fun htr2 => ?_
    have htr2_eq : sf2.trace = sf1.trace ++ [allocFailedEvent] := by
      simpa only [wp_norm, arm64_norm] using htr2
    apply SepWPp.of_sepWP
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
    exact dirGetPanicQp_of_panicked
      (by rw [htr1_eq]; exact hpfx_s)
      htr2_eq
      (by simp only [wp_norm, arm64_norm])
  · set buf := sf2.readReg64 (Reg.gpr 0#5)
    have hoom_ne : buf ≠ 0#64 := hoom
    have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
    rw [ite_false_eq hoom]
    simp only [sepConj_assoc]
    refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
      fun ⟨_, htr2⟩ => ?_
    have htr2_eq : sf2.trace = s.trace := by
      rw [htr2]; simp only [wp_norm, arm64_norm, htr1_eq]
    have hmem22 :
        memRegion buf 22 =
          (∃∗ b1 : BitVec 64, ∃∗ b0 : BitVec 64,
            (buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) := by
      rw [memRegion_split buf 8 14 (by decide),
          memRegion_split (buf + 8#64) 8 6 (by decide),
          ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    rw [hmem22]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun b1 => sepWPp_exists_left fun b0 => ?_
    unfold dirGetRoBundle
    refine seq_frozen_state (mid := fnStart + 424#64) hfz4 ?_
    wp_steps
    apply SepWP.fold (write_22_overlap_mid buf w1) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz5
    rw [ProofLib.memRegion_eight (buf + 14#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun bt => ?_
    have herr_len : (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail).length = 22 := by
      simp [unpack64_length]
    by_cases hpcap : pathCap = 0
    · subst hpcap
      simp only [↓reduceIte, emp_sepConj]
      refine seq_frozen_state (mid := fnStart + 284#64) hfz5 ?_
      wp_steps
      apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
      apply SepWP.fold (getResultAt_err_of_ro A x.ret buf (readOpStrAddr img.base)
        (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail) herr_len hoom) (by sep_frame)
      apply SepWP.fold hp24 (by sep_frame)
      apply SepWP.fold hcstk_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz6
      rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
      refine SepWPp.perm
        (step_epilogue_284 (r := .error ())
          (Extra := (unreadableStrAddr img.base ↦₆₄ᵣ w0) ∗
            ((unreadableStrAddr img.base + 8#64) ↦₆₄ᵣ w1) ∗
            ((unreadableStrAddr img.base + 14#64) ↦₆₄ᵣ wTail))
          hstk hfull hsp0_al
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs2.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
                exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
          ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2]⟩)
        (by sep_frame)
    · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
      simp only [hpcap, ↓reduceIte]
      refine seq_frozen_state (mid := fnStart + 464#64) hfz5 ?_
      wp_steps
      apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
      apply SepWP.fold (getResultAt_err_of_ro A x.ret buf (readOpStrAddr img.base)
        (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail) herr_len hoom) (by sep_frame)
      apply SepWP.fold hcstk_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz6
      rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
      refine SepWPp.perm
        (step_dealloc_epilogue_464 (r := .error ())
          (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
          (Extra := (unreadableStrAddr img.base ↦₆₄ᵣ w0) ∗
            ((unreadableStrAddr img.base + 8#64) ↦₆₄ᵣ w1) ∗
            ((unreadableStrAddr img.base + 14#64) ↦₆₄ᵣ wTail))
          hC hcstk hstk hfull hsp0_al hfz6
          (by simp only [wp_norm, arm64_norm, *])
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp2_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs2.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
                exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hpcap hpth_cap_lt
          ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2]⟩)
        (by sep_frame)

/-- Combined post-I/O continuation at `+336`..`+508`. -/
theorem step_after_read
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      (((ioVecAt A (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail))
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hdrop := vecU8At_drop_buf A pathCap pathPtr pth hpth_le hpth_cap_lt
  have hpre_drop :
      ((ioVecAt A (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail) ⊢
      (((ioVecAt A (s0.sp - 112#64) r ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail) := by
    simp only [sepConj_assoc]
    rw [← sepConj_assoc (pathPtr ↦ₛ pth)]
    exact sepConj_mono_right (sepConj_mono_left hdrop)
  refine sepWPp_weaken_pre hpre_drop ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  cases r with
  | ok outBs =>
    exact step_after_read_ok hC hcstk hstk hfull hsp0_al hpth_cap_lt hp24
      hfz hsym hpc hrun hsp_al hsp hhcs hx19 hx21 hres
  | error u =>
    cases u
    exact step_after_read_err hC hcstk hstk hfull hsp0_al hb hpth_cap_lt hp24
      hfz hsym hpc hrun hsp_al hsp hhcs hx19 hx21 hres

end CryptoVerification.SignalSession.Cli.Get.Helpers
