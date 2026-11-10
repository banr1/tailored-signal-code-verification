/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

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

theorem step_send_arm_35c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 w3 w4 w1 : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ([(p1, bs1), (p2, bs2)] : List (BitVec 64 × List (BitVec 8))).map (·.2) =
      i.argv.map bytesOfString)
    (hcmd : bs1 = utf8 "send")
    (hs : InMainPlaced CodeOk s0 s 0x360)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) ret s'
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2)] ∗
          argvAtP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) ret s
      ((vptr ↦₆₄ p1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        argsBufTail A vcap vptr [(p1, bs1), (p2, bs2)] ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2)] ∗
        argvAtP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        memRegion (fsp + 0x1b8#64) 32 ∗ m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ Statics)
      Q Qp oom := by
  dsimp only
  have haddr := address_keepsFs_placed_ok hc
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  dsimp only [argvAtP]
  rw [cStrAt_split p2 bs2]
  rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hres_le hsub64]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align0 := fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 580) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := ⟨fsp + 0x1b8#64, p2, bs2⟩)
    (k_ret := 0x36c)
    (F := (vptr ↦₆₄ p1) ∗ ((vptr + 8#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
      ((vptr + 16#64) ↦₆₄ p2) ∗ ((vptr + 24#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      argsBufTail A vcap vptr [(p1, bs1), (p2, bs2)] ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2)] ∗
      ((s0.readReg64 .x1) ↦₆₄ p0) ∗ cStrAt p0 (bytesOfString "libsignal-cli") ∗
      ((s0.readReg64 .x1 + 8#64) ↦₆₄ p1) ∗ cStrAt p1 bs1 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ p2) ∗
      ((p2 + BitVec.ofNat 64 bs2.length) ↦₈ 0#8) ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ 0#64) ∗
      mainSaved s0 ∗
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
      m2LocalsRest fsp ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - resStack) ∗ Statics)
    haddr hinv1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_)
    (hpanic := fun _ _ _ hm => panic_of_address ((by simp only [arm64_norm, *] : _ = s.trace).trans htr) hpanic hm)
    (hnext := ?_)
  · dsimp only [addressSpec]
    refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp]; ac_rfl))
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *]⟩ (Entails.refl _)))
  intro sm hin hcs hfs_m
  dsimp only [addressSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr_m, _⟩ => ?_
  have hx19_m : sm.readReg64 (.gpr 19#5) = buf := hcs.1.trans (by simp only [arm64_norm, *])
  have hx20_m : sm.readReg64 (.gpr 20#5) = vptr := hcs.2.1.trans (by simp only [arm64_norm, *])
  have hx23_m : sm.readReg64 (.gpr 23#5) = vcap := hcs.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have htr_m' : sm.trace = s0.trace :=
    htr_m.trans ((by simp only [arm64_norm, *] : _ = s.trace).trans htr)
  have hfs_m' : sm.fs = s0.fs :=
    hfs_m.trans ((by simp only [arm64_norm, *] : _ = s.fs).trans hfs)
  obtain ⟨hpc_m, hrun_m, hsp_m, hfp_m, hinv_m, hvregs_m, _⟩ := hin
  rw [hfsp] at hsp_m
  rw [mPcPlaced_eq] at hpc_m
  simp only [arm64_norm, hsp]
  cases hparse2 : addrParse uuidParse bs2 with
  | none =>
    dsimp only
    have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
      rw [← hps]; simp only [List.map_cons, List.map_nil, parseArgs, hcmd, ↓reduceIte, hparse2, Option.map_none]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv_m
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hin2 : InMainPlaced CodeOk s0 _ 0xb54 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv2
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    have h32 : ((fsp + 440#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        memRegion (fsp + 448#64) 24 ⊢ memRegion (fsp + 0x1b8#64) 32 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        (Entails.trans
          (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x1b8#64) 0xffffffffffffffff#64))
          (Entails.of_eq (ProofLib.memRegion_split (fsp + 0x1b8#64) 8 24 (by decide)).symm))
    refine SepWPp.weaken_pre (by
      have hloc := Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h32))))
        (locals_merge_memRegion fsp w3 w4 w1)
      rw [argsBuf_two_cons A (p1, bs1) (p2, bs2) hvcap]
      have hp_n : ∀ (P2S PL S0 M1B8 AB2 AB1 X0 C0 X1 C1 X2 N2 X3 MS W3 W4 W1 M2 STX ST : SepProp),
          P2S ∗ PL ∗ S0 ∗ M1B8 ∗ (AB2 ∗ AB1 ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ N2 ∗ X3 ∗
            MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ STX ∗ ST) ⊢
            (W3 ∗ W4 ∗ W1 ∗ M1B8 ∗ M2) ∗
              (AB2 ∗ AB1 ∗ MS ∗ (STX ∗ S0) ∗ PL ∗
                (P2S ∗ X0 ∗ C0 ∗ X1 ∗ C1 ∗ X2 ∗ N2 ∗ X3 ∗ ST)) :=
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
      exact Entails.trans (hp_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (Entails.trans (sepConj_mono_left hloc) (perm_parseFail_pre _ _ _ _ _ _ _))) ?_
    rw [← stackAt_split_ge fsp hres_le hsub64, ← hfsp, ← mProgPlaced_eq]
    exact step_parseFail_af8_placed hc hstk hstk64 hok hne hparse_none hin2
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      hvcap (by simp only [arm64_norm, htr_m']) (by simp only [arm64_norm, hfs_m']) hexit
  | some peer =>
    have hparse_ok : parseArgs uuidParse (i.argv.map bytesOfString) = some (.send peer) := by
      rw [← hps]; simp only [List.map_cons, List.map_nil, parseArgs, hcmd, ↓reduceIte, hparse2, Option.map_some]
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun g => ?_
    have hpure_g : ∀ (A0 B0 C0 P0 R1 R2 : SepProp),
        A0 ∗ B0 ∗ C0 ∗ (P0 ∗ R1) ∗ R2 = P0 ∗ (R1 ∗ A0 ∗ B0 ∗ C0 ∗ R2) :=
      fun _ _ _ _ _ _ => by ac_rfl
    rw [hpure_g]
    refine SepWPp.pure_elim fun ⟨hgname, _, hgdev⟩ => ?_
    refine SepWPp.weaken_pre
      (sepConj_mono_left (protocolAddressAt_to_words A (fsp + 0x1b8#64) hgname hgdev)) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun devw => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hcap_ne => ?_
    have hcmn : (g.name.cap + 1#64 == 0#64) = false := cmn1_false hcap_ne
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x550#64) hinv_m
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hin2 : InMainPlaced CodeOk s0 _ 0x550 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv2
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    let w : CallW := ⟨0x8000000000000002#64, g.name.cap, g.name.ptr,
      BitVec.ofNat 64 peer.name.length, devw,
      ((sm.readReg64 (.gpr 21#5)).setWidth 32).setWidth 64, sm.readReg64 (.gpr 26#5)⟩
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_ok_tail_548_placed (buf := buf) (vcap := vcap) (vptr := vptr) (p0 := p0)
        (w := w) (c := .send peer) (ps := [(p1, bs1), (p2, bs2)]) (Statics := Statics)
        hc hstk hstk64 hparse_ok hin2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, w]) (by simp only [arm64_norm, *, w])
        (by simp only [arm64_norm, *, w]) (by simp only [arm64_norm, BitVec.zero_or, w])
        hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hnext)
    dsimp only [w, callHeap, argvAtP]
    rw [cStrAt_split p2 bs2, hfsp, stackAt_split_ge fsp hres_le hsub64,
      argsBuf_two_eq A (p1, bs1) (p2, bs2) hvcap]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcells : ((fsp + 440#64) ↦₆₄ g.name.cap) ∗ ((fsp + 448#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ∗ ((fsp + 464#64) ↦₆₄ devw) ⊢
        memRegion (fsp + 440#64) 32 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        cells4_to_memRegion_32 (fsp + 0x1b8#64) g.name.cap g.name.ptr
          (BitVec.ofNat 64 peer.name.length) devw
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_left (pure_intro_entails trivial (Entails.refl _))))
    have hp_s : ∀ (C0 C1 C2 C3 AW R0 : SepProp),
        (C0 ∗ C1 ∗ C2 ∗ C3 ∗ AW) ∗ R0 ⊢ (C0 ∗ C1 ∗ C2 ∗ C3) ∗ (AW ∗ R0) :=
      fun _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
    exact Entails.trans (hp_s _ _ _ _ _ _)
      (Entails.trans (sepConj_mono_left hcells) (Entails.of_eq (by ac_rfl)))

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
