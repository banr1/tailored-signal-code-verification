/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendArmPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.RecvArmPlaced
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

private theorem ps_two_of_map {i : Inputs} {ps : List (BitVec 64 × List (BitVec 8))}
    (hn : i.argv.length = 2) (hps : ps.map (·.2) = i.argv.map bytesOfString) :
    ∃ a1 a2 p1 bs1 p2 bs2,
      i.argv = [a1, a2] ∧ ps = [(p1, bs1), (p2, bs2)] ∧
      bs1 = bytesOfString a1 ∧ bs2 = bytesOfString a2 := by
  generalize hargv : i.argv = argv at hn hps ⊢
  rcases argv with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩ <;>
    rcases ps with _ | ⟨⟨p1, bs1⟩, _ | ⟨⟨p2, bs2⟩, _ | _⟩⟩ <;>
    simp_all

private theorem list_len_four {α : Type} {l : List α} (h : l.length = 4) :
    ∃ b0 b1 b2 b3, l = [b0, b1, b2, b3] := by
  match l with
  | [b0, b1, b2, b3] => exact ⟨b0, b1, b2, b3, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => simp at h

theorem step_send_recv_2f4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ []) (hn : i.argv.length = 2)
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hs : AtM2DispatchPlaced CodeOk s0 s i.argv.length buf vcap vptr)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
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
    SepWPp (mProgPlaced H) ret s
      (argsBuf A vcap vptr ps ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
      Q Qp oom := by
  obtain ⟨a1, a2, p1, bs1, p2, bs2, _, rfl, _, _⟩ := ps_two_of_map hn hps
  have ⟨_, hbs1_le, _⟩ := cliInputsOk_elem hok hps (List.mem_cons_self ..)
  obtain ⟨hbase, _, hx19, hx20, _, hx23, hx24, hvcap, htr, hfs⟩ := hs
  simp only [hn, ↓reduceIte] at hbase
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
  rw [mPcPlaced_eq] at hpc
  rw [argsBuf_two_eq A (p1, bs1) (p2, bs2) hvcap, locals_split_m2 (s0.sp - BitVec.ofNat 64 mainFrameSize)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w1 => ?_
  by_cases hlen4 : bs1.length = 4
  · obtain ⟨b0, b1, b2, b3, rfl⟩ := list_len_four hlen4
    let wcmd : BitVec 32 := b3 ++ (b2 ++ (b1 ++ b0))
    have hwcmd : (b3 ++ b2 ++ b1 ++ b0 : BitVec 32) = wcmd := by dsimp only [wcmd]; bv_bits
    by_cases hsend : wcmd = 0x646e6573#32
    · dsimp only [argvAtP]
      rw [cStrAt_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32 p1 b0 b1 b2 b3, hwcmd, hsend]
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x360#64) hinv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv1
      have hcmd : [b0, b1, b2, b3] = utf8 "send" := (le32_send_iff b0 b1 b2 b3).mp hsend
      have hin1 : InMainPlaced CodeOk s0 _ 0x360 := {
        pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
        run := by simp only [arm64_norm, *]
        sp := by simp only [arm64_norm, *]
        fp := by simp only [arm64_norm, *]
        inv := hinv1
        vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
        spAligned := hsp0 }
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre ?_
        (step_send_arm_35c_placed (buf := buf) (vcap := vcap) (vptr := vptr) (p0 := p0)
          (p1 := p1) (p2 := p2) (w3 := w3) (w4 := w4) (w1 := w1)
          (bs1 := [b0, b1, b2, b3]) (bs2 := bs2) (Statics := Statics)
          hc hstk hstk64 hok hne hps hcmd hin1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hpanic hexit hnext)
      dsimp only [argvAtP]
      rw [cStrAt_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32 p1 b0 b1 b2 b3, hwcmd, hsend]
      exact Entails.of_eq (by ac_rfl)
    · have hsend_neq : (wcmd == 0x646e6573#32) = false := beq_false_of_ne hsend
      have hnot_send : [b0, b1, b2, b3] ≠ utf8 "send" := fun hc => hsend ((le32_send_iff ..).mpr hc)
      by_cases hrecv : wcmd = 0x76636572#32
      · dsimp only [argvAtP]
        rw [cStrAt_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32 p1 b0 b1 b2 b3, hwcmd, hrecv]
        rw [mProgPlaced_eq]
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x32c#64) hinv
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv1
        have hcmd : [b0, b1, b2, b3] = utf8 "recv" := (le32_recv_iff b0 b1 b2 b3).mp hrecv
        have hin1 : InMainPlaced CodeOk s0 _ 0x32c := {
          pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, *]
          fp := by simp only [arm64_norm, *]
          inv := hinv1
          vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
          spAligned := hsp0 }
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre ?_
          (step_recv_arm_32c_placed (buf := buf) (vcap := vcap) (vptr := vptr) (p0 := p0)
            (p1 := p1) (p2 := p2) (w3 := w3) (w4 := w4) (w1 := w1)
            (bs1 := [b0, b1, b2, b3]) (bs2 := bs2) (Statics := Statics)
            hc hstk hstk64 hok hne hps hcmd hin1
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hpanic hexit hnext)
        dsimp only [argvAtP]
        rw [cStrAt_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32 p1 b0 b1 b2 b3, hwcmd, hrecv]
        exact Entails.of_eq (by ac_rfl)
      · have hnot_recv : [b0, b1, b2, b3] ≠ utf8 "recv" := fun hc => hrecv ((le32_recv_iff ..).mpr hc)
        have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
          rw [← hps]; exact parseArgs_two_bad_cmd uuidParse [b0, b1, b2, b3] bs2 hnot_send hnot_recv
        have hrecv_neq : (wcmd == 0x76636572#32) = false := beq_false_of_ne hrecv
        dsimp only [argvAtP]
        rw [cStrAt_split p1 [b0, b1, b2, b3], bytes4_eq_pointsTo32 p1 b0 b1 b2 b3, hwcmd]
        rw [mProgPlaced_eq]
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv1
        have hin1 : InMainPlaced CodeOk s0 _ 0xb54 := {
          pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
          run := by simp only [arm64_norm, *]
          sp := by simp only [arm64_norm, *]
          fp := by simp only [arm64_norm, *]
          inv := hinv1
          vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
          spAligned := hsp0 }
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre (by
          let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
          rw [← argsBuf_two_eq A (p1, [b0, b1, b2, b3]) (p2, bs2) hvcap]
          have hp1 : ∀ (AB1 AB2 AV MS LOC S PL ST : SepProp),
              AB1 ∗ AB2 ∗ AV ∗ MS ∗ LOC ∗ S ∗ PL ∗ ST ⊢
                LOC ∗ (AB1 ∗ AB2 ∗ MS ∗ S ∗ PL ∗ (AV ∗ ST)) :=
            fun _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
          exact Entails.trans (hp1 _ _ _ _ _ _ _ _)
            (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
              (perm_parseFail_pre _ _ _ _ _ _ _))) ?_
        exact step_parseFail_af8_placed hc hstk hstk64 hok hne hparse_none hin1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hexit
  · have hnot_send : bs1 ≠ utf8 "send" := fun hc => hlen4 (by rw [hc, utf8_send_eq]; rfl)
    have hnot_recv : bs1 ≠ utf8 "recv" := fun hc => hlen4 (by rw [hc, utf8_recv_eq]; rfl)
    have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
      rw [← hps]; exact parseArgs_two_bad_cmd uuidParse bs1 bs2 hnot_send hnot_recv
    have hbs1_lt : bs1.length < 2 ^ 64 := by dsimp only at hbs1_le; omega
    have hlen_beq : (BitVec.ofNat 64 bs1.length == 4#64) = false := by
      apply beq_false_of_ne; intro heq
      have htn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn
      exact hlen4 htn
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0xb54 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv1
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre (by
      let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
      rw [← argsBuf_two_eq A (p1, bs1) (p2, bs2) hvcap]
      have hp2 : ∀ (AB1 AB2 AV MS LOC S PL ST : SepProp),
          AB1 ∗ AB2 ∗ AV ∗ MS ∗ LOC ∗ S ∗ PL ∗ ST ⊢
            LOC ∗ (AB1 ∗ AB2 ∗ MS ∗ S ∗ PL ∗ (AV ∗ ST)) :=
        fun _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
      exact Entails.trans (hp2 _ _ _ _ _ _ _ _)
        (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
          (perm_parseFail_pre _ _ _ _ _ _ _))) ?_
    exact step_parseFail_af8_placed hc hstk hstk64 hok hne hparse_none hin1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hexit

end CryptoVerification.SignalSession.Cli.MainHops.Proofs
