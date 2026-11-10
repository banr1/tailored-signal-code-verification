/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `main` M2 Collect Entry (`M+0xc0 .. M+0x11c / M+0x1ac`, Block `617`)

Verifies the initial `from_utf8`, allocator shim, and `__rust_alloc(64, 8)` setup of `main`'s
`Vec<&str>` argument collection on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open M2Steps M2StepsPlaced M2Entry

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace M2EntryPlaced

set_option maxHeartbeats 800000 in
/-- Post-`__rust_alloc(64, 8)` continuation at `M+0x0ec` on Block `617`. -/
theorem step_collect_post_alloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 sf3 : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn1_le : 1 ≤ n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hsp0 : s0.spAligned = true)
    (hpc3 : sf3.pc = (blkPl_617).base + 0x0ec#64) (hrun3 : sf3.status = .Running)
    (hsp3_eq : sf3.sp = fspOf s0) (hfp_3 : sf3.readReg64 .fp = s0.sp - 0x60#64)
    (hinv6 : CodeOk sf3.mem) (hvregs_3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0)
    (hx19_3 : sf3.readReg64 (.gpr 19#5) = buf)
    (hx21_3 : sf3.readReg64 (.gpr 21#5) = (ps[0]'(by omega)).1)
    (hx22_3 : sf3.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (hx23_3 : sf3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (ps[0]'(by omega)).2.length)
    (hx24_3 : sf3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n)
    (hfs3 : sf3.fs = s0.fs)
    {s_call : State}
    (hsp_call : s_call.sp = fspOf s0) (htr_call : s_call.trace = s0.trace)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64),
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (argsBuf A vcap vptr ps ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf3
      ((if sf3.readReg64 .x0 = 0 then
          ⌜sf3.trace = s_call.trace ++ [allocFailedEvent]⌝ ∗ A.pool ∗ stackAt s_call.sp extHookStack
        else
          ⌜(sf3.readReg64 .x0).toNat % 8 = 0 ∧ sf3.trace = s_call.trace⌝ ∗
            A.live (sf3.readReg64 .x0) 64 8 ∗ memRegion (sf3.readReg64 .x0) 64 ∗
            A.pool ∗ stackAt s_call.sp extHookStack) ∗
        (argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗
          memRegion (fspOf s0 + 0x1b8#64) 24 ∗
          memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
          memRegion (fspOf s0 + 0x310#64) 24 ∗
          memRegion (fspOf s0 + 0x328#64) 0x158 ∗
          mainSaved s0 ∗
          memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
          Statics)) Q Qp oom := by
  have h0_ps : 0 < ps.length := by omega
  have hs3_aligned : sf3.spAligned = true := fsp_spAligned hsp0 hsp3_eq
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hstk_ext := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := extHookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  by_cases hv0 : sf3.readReg64 .x0 = 0
  · simp only [hv0, ↓reduceIte]
    apply sepWPp_mono_pre
      (P' := ⌜sf3.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (A.pool ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 0x1b8#64) 24 ∗
          memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗ memRegion (fspOf s0 + 0x310#64) 24 ∗
          memRegion (fspOf s0 + 0x328#64) 0x158 ∗ mainSaved s0 ∗ Statics))
    · simp only [wp_norm, arm64_norm, hsp_call, hsp3_eq, htr_call]
      rw [hstk_ext]
      apply Entails.of_eq
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
      try ac_rfl
    refine sepWPp_pure_elim fun htr_fail => ?_
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xff0#64) hinv6
    wp_step
    apply SepWP.done
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hv0, ↓reduceIte, *]; try bv_omega)
      (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    intro _
    exact step_collect_panic_placed env
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hv0, ↓reduceIte, *]; try bv_omega)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun3])
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr_fail])
      hpanic
  · let vptr0 : BitVec 64 := sf3.readReg64 .x0
    have hv0_beq : (vptr0 == 0#64) = false := beq_eq_false_iff_ne.mpr hv0
    simp only [hv0, ↓reduceIte]
    apply sepWPp_mono_pre
      (P' := ⌜vptr0.toNat % 8 = 0 ∧ sf3.trace = s0.trace⌝ ∗
        (A.live vptr0 64 8 ∗ memRegion vptr0 64 ∗
          memRegion (sf3.sp + 0x310#64) 24 ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 0x1b8#64) 24 ∗
          memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗ memRegion (fspOf s0 + 0x328#64) 0x158 ∗
          mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics))
    · simp only [wp_norm, arm64_norm, hsp_call, hsp3_eq, htr_call]
      rw [hstk_ext]
      apply Entails.of_eq
      simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]
      try ac_rfl
    refine sepWPp_pure_elim fun ⟨_, htr3⟩ => ?_
    rw [memRegion_64_head_words vptr0, memRegion_24_words (sf3.sp + 0x310#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine sepWPp_exists_elim fun hw0 => sepWPp_exists_elim fun hw1 =>
      sepWPp_exists_elim fun hdr0 => sepWPp_exists_elim fun hdr1 =>
      sepWPp_exists_elim fun hdr2 => ?_
    simp only [wp_norm, arm64_norm, hsp3_eq]
    have hcmp1 : (BitVec.ofNat 64 n == 1#64) = decide (n = 1) :=
      ofNat_beq_ofNat (by omega) (by decide)
    have htake1 : [ps[0]] = ps.take 1 := by
      cases ps with
      | nil => simp at h0_ps
      | cons _ _ => rfl
    by_cases hn1 : n = 1
    · apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x1a8#64) hinv6
      wp_step; wp_steps
      apply SepWP.done
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
        (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
      clear hpc3
      intro hinv7
      have hwith : ∀ {s_m : State} {Pm : SepProp},
          s_m.pc = (blkPl_617).base + 0x1a8#64 →
          (s_m.pc = (blkPl_617).base + 0x1a8#64 →
            SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s_m Pm Q Qp oom) →
          SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s_m Pm Q Qp oom := fun h1 k => k h1
      refine hwith
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; try bv_omega) ?_
      intro hpc4
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x1b0#64) hinv7
      wp_step; wp_steps
      apply SepWP.done
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hx24_3, hx25_3, hn1, Bool.false_eq_true, ↓reduceIte, *]; try bv_omega)
        (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
      intro hinv8
      apply sepWPp_mono_pre
        (P' := argsBuf A 4#64 vptr0 ps ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (fspOf s0) [] ∗
          stackAt (fspOf s0) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
      · have hinit : (A.live vptr0 64 8 ∗ (vptr0 ↦₆₄ ps[0].1) ∗
            ((vptr0 + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗ memRegion (vptr0 + 16#64) 48) ⊢
            argsBuf A 4#64 vptr0 ps := by
          have h := argsBuf_init_cap4 A vptr0 ps[0] hv0
          simpa only [htake1, ← hn1, ← hps_len, List.take_length] using h
        have hhdr := words_to_memRegion_24 (fspOf s0 + 0x310#64) 4#64 vptr0 1#64
        rw [locals_nil_split_m2]
        simp only [wp_norm, arm64_norm, hsp3_eq, hx21_3, hx23_3, hn1,
          BitVec.add_assoc, BitVec.reduceAdd,
          show BitVec.ofNat 64 1 = 1#64 by rfl] at hinit hhdr ⊢
        exact Entails.trans
          (entail_with_frame
            (F := ((fspOf s0 + 784#64) ↦₆₄ 4#64 ∗ (fspOf s0 + 792#64) ↦₆₄ vptr0 ∗
                (fspOf s0 + 800#64) ↦₆₄ 1#64) ∗
              argsBuf A 1#64 buf ps ∗
              argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              memRegion (fspOf s0) 440 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
              memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
              mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hinit)
          (entail_with_frame
            (F := argsBuf A 4#64 vptr0 ps ∗
              argsBuf A 1#64 buf ps ∗
              argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              memRegion (fspOf s0) 440 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
              memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
              mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hhdr)
      refine hnext _ 4#64 vptr0 ⟨?_, ?_, ?_, ?_, hinv8, ?_, hsp0_keep (), ?_⟩
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by decide)
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hn1, Bool.false_eq_true, ↓reduceIte]; try bv_omega
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3_eq]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_3]
      · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_3
      · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp3_eq])
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3, hn1]
      · rfl
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hn1]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_3, hn1]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs3]
    · have hn_gt1 : 1 < n := by omega
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x120#64) hinv6
      wp_step; wp_steps
      apply SepWP.done
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_false, Bool.not_false, ↓reduceIte, *]; try bv_omega)
        (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
      intro hinv7
      apply sepWPp_mono_pre_sp (fsp := fspOf s0)
        (F := fun sp => vecHeader (sp + 0x310#64) 4#64 vptr0 (BitVec.ofNat 64 1) ∗
          argsBuf A 4#64 vptr0 (ps.take 1) ∗
          m2LoopMem A s0 stk n buf p0 ps Statics)
      · simp only [wp_norm, arm64_norm, hsp3_eq]
      · have hinit : (A.live vptr0 64 8 ∗ (vptr0 ↦₆₄ ps[0].1) ∗
            ((vptr0 + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗ memRegion (vptr0 + 16#64) 48) ⊢
            argsBuf A 4#64 vptr0 (ps.take 1) := by
          simpa only [htake1] using argsBuf_init_cap4 A vptr0 ps[0] hv0
        dsimp only [m2LoopMem]
        unfold vecHeader
        simp only [wp_norm, arm64_norm, hsp3_eq, hx21_3, hx23_3,
          BitVec.add_assoc, BitVec.reduceAdd,
          show BitVec.ofNat 64 1 = 1#64 by rfl] at hinit ⊢
        exact entail_with_frame
          (F := ((fspOf s0 + 784#64) ↦₆₄ 4#64 ∗ (fspOf s0 + 792#64) ↦₆₄ vptr0 ∗
              (fspOf s0 + 800#64) ↦₆₄ 1#64) ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            memRegion (fspOf s0) 440 ∗ memRegion (fspOf s0 + 440#64) 24 ∗
            memRegion (fspOf s0 + 464#64) 320 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
            mainSaved s0 ∗ stackAt (fspOf s0) (stk - mainFrameSize) ∗ A.pool ∗ Statics) hinit
      refine step_collect_loop_placed env hstk hstk64 hn_le hps_len hascii hpanic hnext
        (n - 1) 1 _ 4#64 vptr0 rfl (Nat.le_refl 1) hn_gt1
        ⟨⟨?_, ?_, ?_, ?_, hinv7, ?_, hsp0_keep (), ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, bne, hv0_beq, hx25_3, hcmp1, hn1, decide_false, Bool.not_false, ↓reduceIte]; try bv_omega
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hrun3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3_eq]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_3]
      · simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_3
      · exact fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp3_eq])
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3]
      · rfl
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]
      · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfs3]

set_option maxHeartbeats 800000 in
/-- Entry phase `M+0x0c0 .. M+0x11c` on Block `617`. -/
theorem step_collect_first_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {A : RustAlloc} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack n : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (env : M2EnvPlaced H A hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hn1_le : 1 ≤ n) (hn_le : n ≤ 1820) (hps_len : ps.length = n)
    (hascii : ∀ k (hk : k < ps.length), ∀ b ∈ ps[k].2, b.toNat < 128)
    (hf : M2FramePlaced CodeOk s0 s 0x0c0)
    (hx19 : s.readReg64 (.gpr 19#5) = buf)
    (hx22 : s.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n))
    (_hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64),
      M2FramePlaced CodeOk s0 s' (if n = 2 then 0x2f4 else 0x1b0) →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 20#5) = vptr →
      s'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 n →
      s'.readReg64 (.gpr 23#5) = vcap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      vcap ≠ 0#64 →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s'
        (argsBuf A vcap vptr ps ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics) Q Qp oom) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s
      (argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics) Q Qp oom := by
  have h0_ps : 0 < ps.length := by omega
  rcases hf with ⟨hpc, hrun, hsp_eq, hfp, hinv, hvregs, hsp0, hs_aligned⟩
  have hsp0_keep : Unit → s0.spAligned = true := fun () => hsp0
  clear hsp0
  have hfocus0 : argsBuf A (BitVec.ofNat 64 n) buf ps =
      (buf ↦₆₄ ps[0].1) ∗ ((buf + 8#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗
        argsBufRest A (BitVec.ofNat 64 n) buf ps 0 := by
    simpa only [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero] using
      argsBuf_focus A (BitVec.ofNat 64 n) buf ps 0 h0_ps
  rw [locals_nil_split_m2, hfocus0]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsFromUtf8Sym) hinv
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro hinv1
  rw [← hfocus0]
  have hargv0 := argvAtP_focus (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
    1 (by simp [hps_len]; omega)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hargv0
  have hstk_utf8 := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := hookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) (fspOf s0 + 0x1b8#64, ps[0].1, ps[0].2) env.utf8_ok hinv1
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp_eq]))
    (ret_pc := (blkPl_617).base + 0x0cc#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtPRest (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) 1 ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      A.pool ∗ Statics)
  · dsimp only [fromUtf8AsciiSpec]
    have hascii0_eq : (∀ b ∈ ps[0].2, b.toNat < 128) = True :=
      propext ⟨fun _ => trivial, fun _ => hascii 0 h0_ps⟩
    rw [hargv0, hstk_utf8]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp_eq, hx19, hascii0_eq, true_and,
      pure_true, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try ac_rfl
  intro sf1 hinv2 hpc1 hrun1 hsp1 hcs1
  have hsp1_eq : sf1.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp_eq] using hsp1
  clear hsp1
  have hx19_1 : sf1.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs1]; simp only [wp_norm, arm64_norm, hx19]
  have hx22_1 : sf1.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs1]; simp only [wp_norm, arm64_norm, hx22]
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs1]; simp only [wp_norm, arm64_norm, hx24]
  have hx25_1 : sf1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := by
    rw [cs_x25 hcs1]; simp only [wp_norm, arm64_norm, hx25]
  have hfp_1 : sf1.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs1]; simp only [wp_norm, arm64_norm, hfp]
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs) hcs1
  have hs1_aligned : sf1.spAligned = true := fsp_spAligned (hsp0_keep ()) hsp1_eq
  clear hpc hrun hs_aligned
  dsimp only [fromUtf8AsciiSpec]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨htr1_raw, hfs1_raw⟩ => ?_
  have htr1 : sf1.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htr1_raw
  have hfs1 : sf1.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs] using hfs1_raw
  clear htr1_raw hfs1_raw
  apply sepWPp_mono_pre
    (P' := ((sf1.sp + 440#64) ↦₆₄ 0#64) ∗
      ((sf1.sp + 448#64) ↦₆₄ ps[0].1) ∗ ((sf1.sp + 456#64) ↦₆₄ BitVec.ofNat 64 ps[0].2.length) ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      stackAt (fspOf s0) (stk - mainFrameSize) ∗
      A.pool ∗ Statics)
  · apply Entails.of_eq
    rw [hargv0]
    simp only [wp_norm, arm64_norm, hsp_eq, hsp1_eq,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [hstk_utf8]
    try ac_rfl
  simp only [wp_norm, arm64_norm, hsp1_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustNoAllocShimSymCli) hinv2
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro hinv3
  have hstk_ext := stackAt_split_ge' (s0.sp - BitVec.ofNat 64 mainFrameSize) (n := extHookStack) (m := stk - mainFrameSize)
    (by omega) (by omega)
  apply sepWPp_mono_pre
    (P' := stackAt (fspOf s0) extHookStack ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      A.pool ∗ Statics)
  · have hsret := words_to_memRegion_24 (fspOf s0 + 0x1b8#64) 0#64 ps[0].1
      (BitVec.ofNat 64 ps[0].2.length)
    simp only [wp_norm, arm64_norm, hsp1_eq, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd] at hsret ⊢
    rw [hstk_ext]
    exact entail_with_frame
      (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        memRegion (fspOf s0) 0x1b8 ∗ memRegion (fspOf s0 + 464#64) 320 ∗
        memRegion (fspOf s0 + 784#64) 24 ∗ memRegion (fspOf s0 + 808#64) 344 ∗
        mainSaved s0 ∗
        memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
        stackAt (fspOf s0) extHookStack ∗ A.pool ∗ Statics) hsret
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) () env.shim_ok hinv3
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp1_eq]))
    (ret_pc := (blkPl_617).base + 0x0e0#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      A.pool ∗ Statics)
  · dsimp only [Spec.keepsFs, withStack, sessionShimSpec]
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp1_eq, emp_sepConj, BitVec.add_assoc, BitVec.reduceAdd]
    try ac_rfl
  intro sf2 hinv4 hpc2 hrun2 hsp2 hcs2
  have hsp2_eq : sf2.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp1_eq] using hsp2
  clear hsp2
  have hx19_2 : sf2.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_1]
  have hx21_2 : sf2.readReg64 (.gpr 21#5) = ps[0].1 := by
    rw [cs_x21 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
  have hx22_2 : sf2.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_1]
  have hx23_2 : sf2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 ps[0].2.length := by
    rw [cs_x23 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
  have hx24_2 : sf2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_1]
  have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := by
    rw [cs_x25 hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx25_1]
  have hfp_2 : sf2.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs2]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_1]
  have hvregs_2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_1) hcs2
  have hs2_aligned : sf2.spAligned = true := fsp_spAligned (hsp0_keep ()) hsp2_eq
  clear hpc1 hrun1 hs1_aligned
  dsimp only [Spec.keepsFs, withStack, sessionShimSpec]
  have hpure_swap : ∀ (F S TR T : SepProp), ((F ∗ (S ∗ TR)) ∗ T) = (F ∗ (TR ∗ (S ∗ T))) := by
    intros; ac_rfl
  rw [hpure_swap]; clear hpure_swap
  refine sepWPp_pure_elim fun hfs2_raw => ?_
  have hpure_swap2 : ∀ (S TR T : SepProp),
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf2 (S ∗ TR ∗ T) Q Qp oom =
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf2 (TR ∗ S ∗ T) Q Qp oom := by
    intro S TR T
    have heq : (S ∗ TR ∗ T) = (TR ∗ S ∗ T) := by ac_rfl
    rw [heq]
  rw [hpure_swap2]; clear hpure_swap2
  refine sepWPp_pure_elim fun htr2_raw => ?_
  have htr2 : sf2.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr1] using htr2_raw
  have hfs2 : sf2.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs1] using hfs2_raw
  clear htr2_raw hfs2_raw
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsRustAllocSymCli) hinv4
  wp_step; wp_steps
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (hrun := by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
  intro hinv5
  apply main_call_rocl (s0 := s0) (CodeOk := CodeOk) (64, 8) env.alloc_ok hinv5
    (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, *])
    (fsp_spAligned (hsp0_keep ()) (by simp only [wp_norm, arm64_norm, hsp2_eq]))
    (ret_pc := (blkPl_617).base + 0x0ec#64)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    (F := argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      memRegion (fspOf s0) 0x1b8 ∗
      memRegion (fspOf s0 + 0x1b8#64) 24 ∗
      memRegion (fspOf s0 + 0x1d0#64) 0x140 ∗
      memRegion (fspOf s0 + 0x310#64) 24 ∗
      memRegion (fspOf s0 + 0x328#64) 0x158 ∗
      mainSaved s0 ∗
      memRegion (fspOf s0 - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - extHookStack) ∗
      Statics)
  · dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
    have hlay : LayoutOk 64 8 := ⟨by decide, ⟨3, rfl⟩, by decide⟩
    apply Entails.of_eq
    simp only [wp_norm, arm64_norm, hsp1_eq, hsp2_eq, hlay, and_self, pure_true, emp_sepConj,
      BitVec.add_assoc, BitVec.reduceAdd,
      show (64#64 : BitVec 64).toNat = 64 by rfl, show (8#64 : BitVec 64).toNat = 8 by rfl]
    try ac_rfl
  intro sf3 hinv6 hpc3 hrun3 hsp3 hcs3
  have hsp3_eq : sf3.sp = fspOf s0 := by simpa only [wp_norm, arm64_norm, hsp2_eq] using hsp3
  clear hsp3
  have hx19_3 : sf3.readReg64 (.gpr 19#5) = buf := by
    rw [cs_x19 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_2]
  have hx21_3 : sf3.readReg64 (.gpr 21#5) = ps[0].1 := by
    rw [cs_x21 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx21_2]
  have hx22_3 : sf3.readReg64 (.gpr 22#5) = buf + BitVec.ofNat 64 (16 * n) := by
    rw [cs_x22 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx22_2]
  have hx23_3 : sf3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 ps[0].2.length := by
    rw [cs_x23 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_2]
  have hx24_3 : sf3.readReg64 (.gpr 24#5) = BitVec.ofNat 64 n := by
    rw [cs_x24 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hx24_2]
  have hx25_3 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n → sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := fun h => by
    rw [cs_x25 hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, h]
  have hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 n := hx25_3 hx25_2
  have hfp_3 : sf3.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [cs_fp hcs3]; simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hfp_2]
  have hvregs_3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0 :=
    calleeSavedVRegs_preserve
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]; exact hvregs_2) hcs3
  dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
  have hpure_swap3 : ∀ (FS AP T : SepProp),
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf3 ((FS ∗ AP) ∗ T) Q Qp oom =
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret sf3 (FS ∗ (AP ∗ T)) Q Qp oom := by
    intro FS AP T
    rw [sepConj_assoc]
  rw [hpure_swap3]; clear hpure_swap3
  refine sepWPp_pure_elim fun hfs3_raw => ?_
  have hfs3 : sf3.fs = s0.fs := by simpa only [wp_norm, arm64_norm, hfs2] using hfs3_raw
  clear hfs3_raw
  have halloc_if_eq : ∀ (POOL STK B1 B21 B22 B23 : SepProp) (c : Prop) [Decidable c],
      (POOL ∗ STK ∗ if c then B1 else B21 ∗ B22 ∗ B23) =
      (if c then B1 ∗ POOL ∗ STK else B21 ∗ B22 ∗ B23 ∗ POOL ∗ STK) := by
    intros
    split_ifs <;> ac_rfl
  rw [halloc_if_eq]; clear halloc_if_eq
  refine step_collect_post_alloc_placed env hstk hstk64 hn1_le hn_le hps_len hascii (hsp0_keep ())
    hpc3 hrun3 hsp3_eq hfp_3 hinv6 hvregs_3 hx19_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hfs3
    ?_ ?_ hpanic hnext
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp2_eq]
  · simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr2]

end M2EntryPlaced

end CryptoVerification.SignalSession.Cli.MainHops
