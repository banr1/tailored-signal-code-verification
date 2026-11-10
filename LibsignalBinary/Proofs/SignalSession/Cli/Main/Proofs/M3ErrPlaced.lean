/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Relocatable Error-Path `coins` & `input` Cleanup for `main` Hop M3 (Block `617`)

Verifies the `coins` and `input` drop guards at `M+0x624` and `M+0x638` on Block `617` under
`[LibsignalPlacement]`, delegating to `step_dealloc_in_0x650_placed` / `step_drop_call_0x660_placed`
(`exit 2`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops.M3Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 800000 in
/-- Continuation dropping optional `input` from `M+0x638` (`sub x8, x23, #1; mov x27, x22;
ldr x22, [sp, #0x58]; cmn x8, #2; mov w26, #2; b.hs 0x660`), then calling
`step_dealloc_in_0x650_placed` or `step_drop_call_0x660_placed`. -/
theorem step_err_in_0x638_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {P : Prop} {i : Inputs} {c : CallV}
    {w : CallW} {s0 s st : State} {ret : BitVec 64} {stk hookStack resStack n : Nat} {buf inCap inPtr : BitVec 64}
    {inOk : Bool} {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x638)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (herr : ErrHistP P i s0 s st)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        P ∧ s'.trace = s.trace)
      Q Qp) :
    SepWPp (mProgPlaced H) ret st
      (optOwnedBytes A inOk inCap inPtr ∗
        callHeap A w c ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hfocus58 :
      locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] =
      ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr] 0x58 8 [] := by
    simp only [locals, localsFrom, localsCtx]; ac_rfl
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  cases inOk with
  | false =>
    rw [optOwnedBytes_false]
    refine SepWPp.pure_elim fun hneg1 => ?_
    have hcarry := drop_guard_carry_neg1
    rw [hfocus58]
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x660#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x660 := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by simp only [arm64_norm, *]
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    have herr1 : ErrHistP P i s0 s _ :=
      herr.of_eq (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
    refine SepWPp.weaken_pre ?_
      (step_drop_call_0x660_placed (code := 2) (c := c) (w := w) (inPtr := inPtr) (ps := ps)
        hc hstk hstk64 hin1
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hx19]); try rfl)
        (by (try simp only [arm64_norm, hx20]); try rfl)
        (by (try simp only [arm64_norm, hx21]); try rfl)
        (by (try simp only [arm64_norm]); try rfl)
        (by (try simp only [arm64_norm, hx24]); try rfl)
        (by (try simp only [arm64_norm, hx25]); try rfl)
        (by (try simp only [arm64_norm]); try rfl)
        (fun s' htr' hfs' => by
          have herr' := herr1.of_eq htr' hfs'
          exact ⟨rfl, herr'.1, herr'.2⟩)
        hexit)
    rw [hfocus58]
    exact Entails.of_eq (by ac_rfl)
  | true =>
    rw [optOwnedBytes_true]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun inLen => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun inBs => ?_
    rw [ownedBytes_pure A inCap inPtr inLen inBs, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, _, hin_lt, _⟩ => ?_
    rw [hfocus58]
    by_cases hcap0 : inCap = 0#64
    · have hcarry := drop_guard_carry_zero
      rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x660#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0x660 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      have herr1 : ErrHistP P i s0 s _ :=
        herr.of_eq (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
      refine SepWPp.weaken_pre ?_
        (step_drop_call_0x660_placed (code := 2) (c := c) (w := w) (inPtr := inPtr) (ps := ps)
          hc hstk hstk64 hin1
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx20]); try rfl)
          (by (try simp only [arm64_norm, hx21]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (by (try simp only [arm64_norm, hx25]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (fun s' htr' hfs' => by
            have herr' := herr1.of_eq htr' hfs'
            exact ⟨rfl, herr'.1, herr'.2⟩)
          hexit)
      rw [hfocus58]
      refine Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A hcap0)) ?_
      rw [emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · have hncarry_cs := drop_guard_ncarry_cs hcap0 hin_lt
      have hncarry_cc := drop_guard_ncarry_cc hcap0 hin_lt
      rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x650#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0x650 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      have herr1 : ErrHistP P i s0 s _ :=
        herr.of_eq (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
      refine SepWPp.weaken_pre ?_
        (step_dealloc_in_0x650_placed (code := 2) (c := c) (w := w)
          (inCap := inCap) (inPtr := inPtr) (inLen := inLen) (inBs := inBs) (ps := ps)
          hc hstk hstk64 hin1 hcap0
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx20]); try rfl)
          (by (try simp only [arm64_norm, hx21]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx23]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (by (try simp only [arm64_norm, hx25]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (fun s' htr' hfs' => by
            have herr' := herr1.of_eq htr' hfs'
            exact ⟨rfl, herr'.1, herr'.2⟩)
          hexit)
      rw [hfocus58]
      exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Full error-entry continuation at `M+0x624` under `[LibsignalPlacement]`. -/
theorem step_err_0x624_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {P : Prop} {i : Inputs} {c : CallV}
    {w : CallW} {s0 s st : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf coinsCap coinsPtr inCap inPtr : BitVec 64} {coinsOk inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hst : InMainPlaced CodeOk s0 st 0x624)
    (hx0 : st.readReg64 .x0 = coinsPtr)
    (hx1 : st.readReg64 .x1 = coinsCap)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx21 : st.readReg64 (.gpr 21#5) = w.w5)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (herr : ErrHistP P i s0 s st)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        P ∧ s'.trace = s.trace)
      Q Qp) :
    SepWPp (mProgPlaced H) ret st
      (optOwnedBytes A coinsOk coinsCap coinsPtr ∗
        optOwnedBytes A inOk inCap inPtr ∗
        callHeap A w c ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  cases coinsOk with
  | false =>
    rw [optOwnedBytes_false]
    refine SepWPp.pure_elim fun hneg1 => ?_
    have hcarry := drop_guard_carry_neg1
    have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
    rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x638#64) hinv
    wp_steps
    apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
      (by (try simp only [arm64_norm, *]); try rfl)
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x638 := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
      run := by simp only [arm64_norm, *]
      sp := by (try simp only [arm64_norm]); exact hst.sp
      fp := by (try simp only [arm64_norm]); exact hst.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
      spAligned := hst.spAligned
    }
    exact step_err_in_0x638_placed (c := c) (w := w) (inCap := inCap) (inPtr := inPtr)
      (inOk := inOk) (ps := ps) hc hstk hstk64 hin1
      (by (try simp only [arm64_norm, hx19]); try rfl)
      (by (try simp only [arm64_norm, hx20]); try rfl)
      (by (try simp only [arm64_norm, hx21]); try rfl)
      (by (try simp only [arm64_norm, hx22]); try rfl)
      (by (try simp only [arm64_norm, hx23]); try rfl)
      (by (try simp only [arm64_norm, hx24]); try rfl)
      (by (try simp only [arm64_norm, hx25]); try rfl)
      (herr.of_eq (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl))
      hexit
  | true =>
    rw [optOwnedBytes_true]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun cLen => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun cBs => ?_
    rw [ownedBytes_pure A coinsCap coinsPtr cLen cBs, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, _, hc_lt, _⟩ => ?_
    by_cases hcap0 : coinsCap = 0#64
    · have hcarry := drop_guard_carry_zero
      have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
      rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x638#64) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      have hin1 : InMainPlaced CodeOk s0 _ 0x638 := {
        inv := hinv1
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hst.sp
        fp := by (try simp only [arm64_norm]); exact hst.fp
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_err_in_0x638_placed (c := c) (w := w) (inCap := inCap) (inPtr := inPtr)
          (inOk := inOk) (ps := ps) hc hstk hstk64 hin1
          (by (try simp only [arm64_norm, hx19]); try rfl)
          (by (try simp only [arm64_norm, hx20]); try rfl)
          (by (try simp only [arm64_norm, hx21]); try rfl)
          (by (try simp only [arm64_norm, hx22]); try rfl)
          (by (try simp only [arm64_norm, hx23]); try rfl)
          (by (try simp only [arm64_norm, hx24]); try rfl)
          (by (try simp only [arm64_norm, hx25]); try rfl)
          (herr.of_eq (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl))
          hexit)
      exact Entails.trans (sepConj_mono_left (ownedBytes_entails_emp_of_cap0 A hcap0))
        (Entails.of_eq (by rw [emp_sepConj]))
    · have hncarry_cs := drop_guard_ncarry_cs hcap0 hc_lt
      have hncarry_cc := drop_guard_ncarry_cc hcap0 hc_lt
      have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
      rw [mPcPlaced_eq] at hpc; rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustDeallocSymCli) hinv
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv1
      refine SepWPp.weaken_pre
        (P' := ownedBytes A coinsCap coinsPtr cLen cBs ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗
          (optOwnedBytes A inOk inCap inPtr ∗ callHeap A w c ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
               cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
               cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
               cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗ anyHeap))
        (Entails.of_eq (by ac_rfl))
        (call_dealloc_ownedBytes_placed hc hstk hstk64 hinv1
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm]); exact hst.sp)
          (by (try simp only [arm64_norm]); exact hst.fp)
          (by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs)
          hst.spAligned (retOff := 0x638)
          (by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, hx0]); try rfl)
          (by (try simp only [arm64_norm, hx1]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          hcap0 fun sf hin_f hcs_f hfs_f htr_f => ?_)
      have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
      have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
        rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
      have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by rw [hcs_f.2.2.1]; simp only [arm64_norm, hx21]
      have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
      have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := by rw [hcs_f.2.2.2.2.1]; simp only [arm64_norm, hx23]
      have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
        rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
      have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
        rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
      have herr_f : ErrHistP P i s0 s sf :=
        herr.of_eq (by simpa only [arm64_norm] using htr_f) (by simpa only [arm64_norm] using hfs_f)
      refine SepWPp.weaken_pre ?_
        (step_err_in_0x638_placed (c := c) (w := w) (inCap := inCap) (inPtr := inPtr)
          (inOk := inOk) (ps := ps) hc hstk hstk64 hin_f
          hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f herr_f hexit)
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
