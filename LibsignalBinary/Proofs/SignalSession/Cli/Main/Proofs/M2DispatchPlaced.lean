/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2IfacePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Relocatable `main` M2 Dispatch (`M+0x2f4 / M+0x1b0 → M+0x568 / M+0xb80`, Block `617`)

Verifies the subcommand dispatch half of `main_m2` under `[LibsignalPlacement]` across `send`,
`recv`, `init`, `keygen`, invalid-CLI parse failures (`exit 2`), and OOM panics.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

theorem list_len_four {α : Type} {xs : List α} (h : xs.length = 4) :
    ∃ x0 x1 x2 x3, xs = [x0, x1, x2, x3] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | _⟩⟩⟩⟩ <;> simp at h
  exact ⟨x0, x1, x2, x3, rfl⟩

theorem list_len_six {α : Type} {xs : List α} (h : xs.length = 6) :
    ∃ x0 x1 x2 x3 x4 x5, xs = [x0, x1, x2, x3, x4, x5] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨x0, x1, x2, x3, x4, x5, rfl⟩

theorem ps_three_of_map {argv : List String} {ps : List (BitVec 64 × List (BitVec 8))}
    (hlen : argv.length = 3) (hps : ps.map (·.2) = argv.map bytesOfString) :
    ∃ p1 bs1 p2 bs2 p3 bs3, ps = [(p1, bs1), (p2, bs2), (p3, bs3)] := by
  have hp : ps.length = 3 := by
    have := congrArg List.length hps; simp only [List.length_map, hlen] at this; exact this
  rcases ps with _ | ⟨⟨p1, bs1⟩, _ | ⟨⟨p2, bs2⟩, _ | ⟨⟨p3, bs3⟩, _ | _⟩⟩⟩ <;> simp at hp
  exact ⟨p1, bs1, p2, bs2, p3, bs3, rfl⟩

end CryptoVerification.SignalSession.Cli.MainHops.Proofs

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops.Proofs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 400000 in
/-- Subcommand dispatch half of `main_m2` (`M+0x2f4 / M+0x1b0 → M+0x568 / M+0xb80`) under
`[LibsignalPlacement]` across `send`, `recv`, `init`, `keygen`, parse failures (`exit 2`), and OOM. -/
theorem main_m2_dispatch_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf vcap vptr p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
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
      (argsBuf A vcap vptr ps ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
      Q Qp oom := by
  by_cases hn2 : i.argv.length = 2
  · exact step_send_recv_2f4_placed hc hstk hstk64 hok hne hn2 hps hs hpanic hexit hnext
  · obtain ⟨hbase, _, hx19, hx20, hx21, hx23, hx24, hvcap, htr, hfs⟩ := hs
    simp only [hn2, ↓reduceIte] at hbase
    have hlen_le : i.argv.length ≤ 1820 := (argvFits_bounds hok.2).1
    by_cases hn3 : i.argv.length = 3
    · obtain ⟨p1, bs1, p2, bs2, p3, bs3, rfl⟩ := ps_three_of_map hn3 hps
      have ⟨_, hbs1_le, _⟩ := cliInputsOk_elem hok hps (List.mem_cons_self ..)
      rw [locals_split_m2 (s0.sp - BitVec.ofNat 64 mainFrameSize)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun w3 =>
        SepWPp.exists_elim fun w4 =>
        SepWPp.exists_elim fun w1 => ?_
      rw [argsBuf_three_eq A (p1, bs1) (p2, bs2) (p3, bs3) hvcap]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      by_cases hl4 : bs1.length = 4
      · obtain ⟨b0, b1, b2, b3, rfl⟩ := list_len_four hl4
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x240#64) hinv
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
        intro hinv1
        rw [← mProgPlaced_eq]
        refine SepWPp.weaken_pre ?_
          (step_init_branch_240_placed (buf := buf) (vcap := vcap) (vptr := vptr)
            (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (w3 := w3) (w4 := w4) (w1 := w1)
            hc hstk hstk64 hok hne hps
            ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], hinv1,
             by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs])
            hpanic hexit hnext)
        exact Entails.of_eq (by ac_rfl)
      · have hbs1_lt : bs1.length < 2 ^ 64 := by dsimp only at hbs1_le; omega
        have hne4 : (BitVec.ofNat 64 bs1.length == 4#64) = false := by
          apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn; exact hl4 htn
        have hne4' : (BitVec.ofNat 64 bs1.length != 4#64) = true := by simp only [bne, hne4]; rfl
        by_cases hl6 : bs1.length = 6
        · obtain ⟨b0, b1, b2, b3, b4, b5, rfl⟩ := list_len_six hl6
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x1cc#64) hinv
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
          intro hinv1
          rw [← mProgPlaced_eq]
          refine SepWPp.weaken_pre ?_
            (step_keygen_cmd_1cc_placed (buf := buf) (vcap := vcap) (vptr := vptr)
              (p0 := p0) (p1 := p1) (p2 := p2) (p3 := p3) (w3 := w3) (w4 := w4) (w1 := w1)
              hc hstk hstk64 hok hne hn3 hps
              ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], hinv1,
               by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
              (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
              (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
              hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs])
              hpanic hexit hnext)
          rw [← argsBuf_three_eq A (p1, [b0, b1, b2, b3, b4, b5]) (p2, bs2) (p3, bs3) hvcap]
          exact Entails.of_eq (by ac_rfl)
        · have hne6 : (BitVec.ofNat 64 bs1.length == 6#64) = false := by
            apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs1_lt] at htn; exact hl6 htn
          have hne6' : (BitVec.ofNat 64 bs1.length != 6#64) = true := by simp only [bne, hne6]; rfl
          have hnkey : bs1 ≠ utf8 "keygen" := fun hc6 =>
            hl6 ((congrArg List.length hc6).trans (by rw [utf8_keygen_eq]; rfl))
          have hninit : bs1 ≠ utf8 "init" := fun hc4 =>
            hl4 ((congrArg List.length hc4).trans (by rw [utf8_init_eq]; rfl))
          have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none := by
            rw [← hps]; exact parseArgs_three_bad_cmd uuidParse bs1 bs2 bs3 hnkey hninit
          apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *, hn3]) (by simp only [arm64_norm, *])
          intro hinv1
          rw [← mProgPlaced_eq]
          refine SepWPp.weaken_pre (by
            let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
            rw [← argsBuf_three_eq A (p1, bs1) (p2, bs2) (p3, bs3) hvcap]
            have hp3 : ∀ (AB3 AB2 AV MS LOC S PL ST : SepProp),
                AB3 ∗ AB2 ∗ AV ∗ MS ∗ LOC ∗ S ∗ PL ∗ ST ⊢
                  LOC ∗ (AB3 ∗ AB2 ∗ MS ∗ S ∗ PL ∗ (AV ∗ ST)) :=
              fun _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
            exact Entails.trans (hp3 _ _ _ _ _ _ _ _)
              (Entails.trans (sepConj_mono_left (locals_merge_memRegion fsp w3 w4 w1))
                (perm_parseFail_pre _ _ _ _ _ _ _))) ?_
          exact step_parseFail_af8_placed hc hstk hstk64 hok hne hparse_none
            ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *, hn3],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], hinv1,
             by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit
    · have hlen_lt : i.argv.length < 2 ^ 64 := by omega
      have hne3_bv : (BitVec.ofNat 64 i.argv.length == 3#64) = false := by
        apply beq_false_of_ne; intro h; have htn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt] at htn; exact hn3 htn
      have hne3_bv' : (BitVec.ofNat 64 i.argv.length != 3#64) = true := by simp only [bne, hne3_bv]; rfl
      have hparse_none : parseArgs uuidParse (i.argv.map bytesOfString) = none :=
        parseArgs_len_ne uuidParse _ (by simp [hn2]) (by simp [hn3])
      rw [locals_nil]
      obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hbase
      rw [mPcPlaced_eq] at hpc
      rw [mProgPlaced_eq]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xb54#64) hinv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv1
      rw [← mProgPlaced_eq]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (step_parseFail_af8_placed (buf := buf) (vcap := vcap) (vptr := vptr) (ps := ps)
          (Rest := argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗ Statics)
          hc hstk hstk64 hok hne hparse_none
          ⟨by rw [mPcPlaced_eq]; simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], hinv1,
           by simp only [calleeSavedVRegs, arm64_norm, *], hsp0⟩
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          hvcap (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hfs]) hexit)

end CryptoVerification.SignalSession.Cli.MainHops
