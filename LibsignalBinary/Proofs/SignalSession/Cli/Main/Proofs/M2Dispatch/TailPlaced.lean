/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.HelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Convergence Tails for `main_m2` Dispatch (Block `617`)

Verifies the four shared convergence blocks of `main`'s argument parser under `[LibsignalPlacement]`:
OOM panic (`M+0xfb8`), parse-failure exit (`M+0xb54`), peer-address drop on parse failure
(`M+0xb44`), and successful parse epilogue (`M+0x550`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. OOM Panic Tail (`M+0xfb8 .. M+0xfc0`) -/

theorem step_panic_f84_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {s0 s : State} {ret w4 v1 : BitVec 64} {F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hs : InMainPlaced CodeOk s0 s 0xfb8) (htr : s.trace = s0.trace ++ [allocFailedEvent])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) :
    SepWPp (mProgPlaced H) ret s
      ((((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x48#64) ↦₆₄ w4 ∗
        ((s0.sp - BitVec.ofNat 64 mainFrameSize) + 0x1c8#64) ↦₆₄ v1) ∗ F)
      Q Qp oom := by
  have hext : ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
      some Rust.panicked := hc.handleErrorPanic
  obtain ⟨hpc, hrun, hsp, _, hinv, _, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align : (s0.sp - BitVec.ofNat 64 mainFrameSize) &&& 15#64 = 0#64 :=
    fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align ⊢
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsHandleErrorSymMain) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro _
  refine SepWPp.panic (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hpanic _ _ (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm]; exact htr)).1)

/-! ## 2. Parse-Failure Exit Tail (`M+0xb54 .. M+0xb80`) -/

theorem step_parseFail_af8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf vcap vptr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hs : InMainPlaced CodeOk s0 s 0xb54)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp) :
    SepWPp (mProgPlaced H) ret s
      (argsBuf A vcap vptr ps ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ Rest)
      Q Qp oom := by
  have hdealloc := dealloc_keepsFs_placed_ok hc
  have hlen_le : i.argv.length ≤ 1820 := (argvFits_bounds hok.2).1
  have hlen_pos : 0 < i.argv.length := List.length_pos_of_ne_nil hne
  have hncap : BitVec.ofNat 64 i.argv.length ≠ 0#64 := by
    intro h0; have htn := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i.argv.length < 2 ^ 64)] at htn; omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  refine SepWPp.weaken_pre (sepConj_mono_left (argsBuf_to_dealloc A ps hvcap)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvcap_lt, hlay1⟩ => ?_
  rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hext_le hsub64]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
  have hvcap_beq : (vcap == 0#64) = false := beq_false_of_ne hvcap
  have hncap_beq : (BitVec.ofNat 64 i.argv.length == 0#64) = false := beq_false_of_ne hncap
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hinv1
  refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (vptr, vcap.toNat * 16, 8))
    (k_ret := 0xb68)
    (F := argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗ memRegion fsp 0x480 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗ Rest)
    hdealloc hinv1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [rustDeallocExternSpecWithStack]
    refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; ac_rfl))
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; exact lsl4_toNat hvcap_lt,
          by simp only [arm64_norm, *], hlay1⟩ (Entails.refl _)))
  intro sm1 hin1 hcs1 hfs1
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [arm64_norm, hsp]
  have hx19_1 : sm1.readReg64 (.gpr 19#5) = buf := hcs1.1.trans (by simp only [arm64_norm, *])
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (show
      A.pool ∗ stackAt fsp extHookStack ∗
        (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗ memRegion fsp 0x480 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ Rest) =
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        (A.pool ∗ stackAt fsp extHookStack ∗ mainSaved s0 ∗ memRegion fsp 0x480 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ Rest) by ac_rfl))
      (sepConj_mono_left (argsBuf_to_dealloc A ps hncap))) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hncap_lt, hlay2⟩ => ?_
  obtain ⟨hpc1, hrun1, hsp1, hfp1, hinv1', hvregs1, _⟩ := hin1
  rw [hfsp] at hsp1; rw [mPcPlaced_eq] at hpc1
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv1'
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hinv2
  refine main_call_keepsFs_placed (CodeOk := CodeOk)
    (x := (buf, (BitVec.ofNat 64 i.argv.length).toNat * 16, 8))
    (k_ret := 0xb80)
    (F := mainSaved s0 ∗ memRegion fsp 0x480 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗ Rest)
    hdealloc hinv2
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [rustDeallocExternSpecWithStack]
    refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp1]; ac_rfl))
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; exact lsl4_toNat hncap_lt,
          by simp only [arm64_norm, *], hlay2⟩ (Entails.refl _)))
  intro sm2 hin2 hcs2 hfs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2 => ?_
  have hw26 : (sm2.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 2 := by
    have hx26_2 : sm2.readReg64 (.gpr 26#5) = 2#64 :=
      hcs2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    rw [hx26_2]; rfl
  have htr_final : sm2.trace = s0.trace :=
    htr2.trans ((by simp only [arm64_norm, *] : _ = sm1.trace).trans
      (htr1.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)))
  have hfs_final : sm2.fs = s0.fs :=
    hfs2.trans ((by simp only [arm64_norm, *] : _ = sm1.fs).trans
      (hfs1.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs)))
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (sepWPp_of_mainOom (hexit sm2 2 ⟨hin2, hw26⟩ ⟨rfl, hparse, htr_final, hfs_final⟩))
  dsimp only [retMem]
  simp only [arm64_norm, hsp1]
  rw [hfsp, stackAt_split_ge fsp hext_le hsub64]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (ProofLib.entails_anyHeap Rest)))))

/-! ## 3. Drop-Address Parse-Failure Tail (`M+0xb44 .. M+0xb80`) -/

theorem step_drop_addr_ae8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf vcap vptr cap ptr len devw : BitVec 64} {me : AddrV}
    {ps : List (BitVec 64 × List (BitVec 8))} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hs : InMainPlaced CodeOk s0 s 0xb44)
    (hx22 : s.readReg64 (.gpr 22#5) = ptr) (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx20 : s.readReg64 (.gpr 20#5) = vptr) (hx1 : s.readReg64 .x1 = cap)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp) :
    SepWPp (mProgPlaced H) ret s
      (addrWords A me cap ptr len devw ∗ argsBuf A vcap vptr ps ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ Rest)
      Q Qp oom := by
  by_cases hcap : cap = 0#64
  · subst hcap
    dsimp only [addrWords, ownedBytes]; rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    have h0eq : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0eq, ↓reduceIte, emp_sepConj]
    refine SepWPp.pure_elim fun _ => ?_
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb54 :=
      ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       hinv1, by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
    rw [← mProgPlaced_eq]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (step_parseFail_af8_placed (buf := buf) (vcap := vcap) (vptr := vptr) (ps := ps) (Rest := Rest)
        hc hstk hstk64 hok hne hparse hin1
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit)
  · have hdealloc := dealloc_keepsFs_placed_ok hc
    have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
    have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
    dsimp only [addrWords]; rw [sepConj_assoc]
    refine SepWPp.weaken_pre (sepConj_mono_left (ownedBytes_to_dealloc A me.name hcap)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hcap_lt, hlay⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (show
        A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
          (⌜devw.setWidth 8 = me.device⌝ ∗ argsBuf A vcap vptr ps ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ Rest) =
        ⌜devw.setWidth 8 = me.device⌝ ∗
          (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ argsBuf A vcap vptr ps ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ Rest)
        by ac_rfl)) ?_
    refine SepWPp.pure_elim fun _ => ?_
    rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hext_le hsub64]
    have hcap_beq : (cap == 0#64) = false := beq_false_of_ne hcap
    obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (ptr, cap.toNat, 1)) (k_ret := 0xb54)
      (F := argsBuf A vcap vptr ps ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ memRegion fsp 0x480 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ Rest)
      hdealloc hinv1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
      (by simp only [arm64_norm, *])
      (hP := ?_) (hnext := ?_)
    · dsimp only [rustDeallocExternSpecWithStack]
      refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; ac_rfl))
        (sepConj_mono_left (pure_intro_entails
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], hlay⟩ (Entails.refl _)))
    intro sm hin hcs hfs_m
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_m => ?_
    have hx19_m : sm.readReg64 (.gpr 19#5) = buf := hcs.1.trans (by simp only [arm64_norm, *])
    have hx20_m : sm.readReg64 (.gpr 20#5) = vptr := hcs.2.1.trans (by simp only [arm64_norm, *])
    have hx23_m : sm.readReg64 (.gpr 23#5) = vcap := hcs.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcs.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have htr_m' : sm.trace = s0.trace :=
      htr_m.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)
    have hfs_m' : sm.fs = s0.fs :=
      hfs_m.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs)
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_parseFail_af8_placed (ps := ps) (Rest := Rest) hc hstk hstk64 hok hne hparse hin
        hx19_m hx20_m hx23_m hx24_m hvcap htr_m' hfs_m' hexit)
    simp only [arm64_norm, hsp]
    rw [hfsp, stackAt_split_ge fsp hext_le hsub64]; exact Entails.of_eq (by ac_rfl)

/-! ## 4. Successful Parse Epilogue (`M+0x550 .. M+0x568`) -/

theorem step_ok_tail_548_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf vcap vptr p0 : BitVec 64} {w : CallW} {c : CallV}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : InMainPlaced CodeOk s0 s 0x550)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hw0 : s.readReg64 (.gpr 25#5) = w.w0) (hw2 : s.readReg64 (.gpr 22#5) = w.w2)
    (hw6 : s.readReg64 (.gpr 26#5) = w.w6)
    (hw5 : (s.readReg64 (.gpr 28#5) ||| ((s.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64) = w.w5)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) ret s'
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) ret s
      (argsBuf A vcap vptr ps ∗ callHeap A w c ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗ ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ Statics)
      Q Qp oom := by
  dsimp only
  have hdealloc := dealloc_keepsFs_placed_ok hc
  have hext_le : extHookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  refine SepWPp.weaken_pre (sepConj_mono_left (argsBuf_to_dealloc A ps hvcap)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvcap_lt, hlay⟩ => ?_
  rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hext_le hsub64]
  have hvcap_beq : (vcap == 0#64) = false := beq_false_of_ne hvcap
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp ⊢
  generalize hx21_orig : s.readReg64 (.gpr 21#5) = w21_0 at hw5
  generalize hx28_orig : s.readReg64 (.gpr 28#5) = w28_0 at hw5
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hinv1
  refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (vptr, vcap.toNat * 16, 8))
    (k_ret := 0x568)
    (F := callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗ ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
      ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗ Statics)
    hdealloc hinv1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [rustDeallocExternSpecWithStack]
    refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; ac_rfl))
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; exact lsl4_toNat hvcap_lt,
          by simp only [arm64_norm, *], hlay⟩ (Entails.refl _)))
  intro sm hin hcs hfs_m
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_m => ?_
  have hx19_m : sm.readReg64 (.gpr 19#5) = buf := hcs.1.trans (by simp only [arm64_norm, *])
  have hx21_m : sm.readReg64 (.gpr 21#5) = ((w21_0.setWidth 32).setWidth 64) :=
    hcs.2.2.1.trans (by simp only [arm64_norm, *])
  have hx22_m : sm.readReg64 (.gpr 22#5) = w.w2 := hcs.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx25_m : sm.readReg64 (.gpr 25#5) = w.w0 := hcs.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx26_m : sm.readReg64 (.gpr 26#5) = w.w6 := hcs.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx28_m : sm.readReg64 (.gpr 28#5) = w28_0 :=
    hcs.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hatCall : AtCallPlaced CodeOk s0 sm w i.argv.length buf := {
    base := hin, x19 := hx19_m, x24 := hx24_m, w0 := hx25_m, w2 := hx22_m, w6 := hx26_m,
    w5 := by rw [hx28_m, hx21_m, zext32_idemp]; exact hw5
    x21lo := by rw [hx21_m]; exact zext32_lt w21_0
    trace := htr_m.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)
    fs := hfs_m.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs) }
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_ (hnext sm w c hparse hatCall)
  simp only [arm64_norm, hsp]
  rw [hfsp, stackAt_split_ge fsp hext_le hsub64]
  have hloc := locals_merge_call fsp w
  refine Entails.trans (Entails.of_eq (show
      A.pool ∗ stackAt fsp extHookStack ∗
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ (fsp + 0x40#64) ↦₆₄ w.w3 ∗ (fsp + 0x48#64) ↦₆₄ w.w4 ∗
          (fsp + 0x58#64) ↦₆₄ w.w1 ∗ memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ Statics) =
      (((fsp + 0x40#64) ↦₆₄ w.w3 ∗ (fsp + 0x48#64) ↦₆₄ w.w4 ∗ (fsp + 0x58#64) ↦₆₄ w.w1 ∗
          memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp) ∗
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ stackAt fsp extHookStack) ∗
          A.pool ∗ Statics)) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hloc) (Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
