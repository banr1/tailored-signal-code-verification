/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrC

/-!
# Stage P2 Shared Error Funnel and Unwind Arms 1–2

Proves the unified 6-word `SignalProtocolError` unwind funnel `stageP2_err_funnel_ext_ok`
(`+0x1648 → s0.readReg64 .x30`) and store-error unwinds `p2_arm1_err_ext_ok`
(`get_signed_pre_key` at `+0x0f38`) and `p2_arm2_err_ext_ok` (`get_kyber_pre_key` at `+0x0998`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. `SepProp` Layout, Read-Only Vtable Intro, and `SpeErrSpec` Unpacking Helpers -/

/-- Introduces a read-only image assertion `ro` (e.g. a store-kit vtable) into a `SepWPp` goal
using `img.FrozenLoaded s`. -/
theorem p2_sepWPp_intro_ro {prog : Program} {target : BitVec 64} {img : Obj.Image} {s : State}
    {ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s)
    (hro : ∀ {s' : State} {P' : SepProp}, img.FrozenLoaded s' → (s'.mem ⊨ P') → s'.mem ⊨ ro ∗ P')
    (h : SepWPp prog target s (ro ∗ P) Q Qp) :
    SepWPp prog target s P Q Qp :=
  fun R hm hL => h R (by rw [sepConj_assoc]; exact hro hF hm) hL

theorem p2_bind_sepWP_qp_frame {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_seg F P_seg_post : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hseg : SepWP prog mid s P_seg (fun sm P_m => (P_m ⊢ P_seg_post) ∧ Q_regs sm))
    (hP : P = P_seg ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_seg_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.bind_sepWP_steps_frame ⟨hF, hsym⟩ hseg hP fun sm hst hpcm hrunm ⟨hFm, hsymm⟩ hregs =>
    hnext sm hst hpcm hrunm hFm hsymm hregs

theorem p2_bind_sepWPp_steps_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Unfolds `spkGetPollOutAt` / `kpkGetPollOutAt` (`88` B) on `.error e` into
`preKeyRecordOut64At out 0xffffffffffffffff#64 (S.w0 e) ... u_38 ∗ S.heap e ∗ memRegion (out + 0x40#64) 24`. -/
theorem p2_err88_to_preKeyRecordOut64 {E : Type} (S : SpeErrSpec E) (out : BitVec 64) (e : E) :
    (out ↦₆₄ errTag) ∗ speErrAt S (out + 8#64) e ∗ memRegion (out + 0x38#64) 32 ⊢
      ∃∗ u_38 : BitVec 64,
        preKeyRecordOut64At out 0xffffffffffffffff#64
          (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e) u_38 ∗
        S.heap e ∗
        memRegion (out + 0x40#64) 24 := by
  rw [ProofLib.memRegion_split (out + 0x38#64) 8 24 (by decide),
      ProofLib.memRegion_eight (out + 0x38#64)]
  dsimp only [speErrAt, speWordsAt, preKeyRecordOut64At, errTag]
  sep_norm
  refine Entails.sepExists_elim fun u_38 => Entails.sepExists_right u_38 ?_
  exact Entails.of_eq (by ac_rfl)

/-- Unfolds `preKeyGetPollOutAt` (`56` B) on `.error e` together with trailing `8` B at `out + 0x38`
into `preKeyRecordOut64At out 0xffffffffffffffff#64 (S.w0 e) ... u_38 ∗ S.heap e`. -/
theorem p2_err56_to_preKeyRecordOut64 {E : Type} (S : SpeErrSpec E) (out : BitVec 64) (e : E) :
    ((out ↦₆₄ errTag) ∗ speErrAt S (out + 8#64) e) ∗ memRegion (out + 0x38#64) 8 ⊢
      ∃∗ u_38 : BitVec 64,
        preKeyRecordOut64At out 0xffffffffffffffff#64
          (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e) u_38 ∗
        S.heap e := by
  rw [ProofLib.memRegion_eight (out + 0x38#64)]
  dsimp only [speErrAt, speWordsAt, preKeyRecordOut64At, errTag]
  sep_norm
  refine Entails.sepExists_elim fun u_38 => Entails.sepExists_right u_38 ?_
  exact Entails.of_eq (by ac_rfl)

/-- Folds `preKeyRecordOut64At (sp + 0x3e0#64) ... ∗ memRegion (sp + 0x420#64) 304` back into
`memRegion (sp + 0x3e0#64) 368`. -/
theorem p2_preKeyRecordOut64_to_memRegion368 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At (sp + 0x3e0#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
      memRegion (sp + 0x420#64) 304 ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 64 304 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono_left ?_
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 56 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

/-- Joins `memRegion (sp + 0x420#64) 24 ∗ memRegion (sp + 0x438#64) 280` into
`memRegion (sp + 0x420#64) 304`. -/
theorem p2_memRegion_420_join (sp : BitVec 64) :
    memRegion (sp + 0x420#64) 24 ∗ memRegion (sp + 0x438#64) 280 ⊢
      memRegion (sp + 0x420#64) 304 := by
  rw [ProofLib.memRegion_split (sp + 0x420#64) 24 280 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

/-- Splits `preKeyRecordOut64At (sp + 0xa90#64) ...` (`64` B) into
`cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16`. -/
theorem p2_preKeyRecordOut64_to_cells6_a90 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At (sp + 0xa90#64) w0 w1 w2 w3 w4 w5 w6 w7 ⊢
      cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 := by
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split (sp + 0xac0#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc6 := cells6_fold (sp + 0xa90#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc6); repeat (simp only [BitVec.reduceAdd] at hc6)
  rw [show (sp + 2704#64) ↦₆₄ w0 ∗ ((sp + 2712#64) ↦₆₄ w1 ∗ ((sp + 2720#64) ↦₆₄ w2 ∗
        ((sp + 2728#64) ↦₆₄ w3 ∗ ((sp + 2736#64) ↦₆₄ w4 ∗ ((sp + 2744#64) ↦₆₄ w5 ∗
          ((sp + 2752#64) ↦₆₄ w6 ∗ (sp + 2760#64) ↦₆₄ w7)))))) =
      ((sp + 2704#64) ↦₆₄ w0 ∗ ((sp + 2712#64) ↦₆₄ w1 ∗ ((sp + 2720#64) ↦₆₄ w2 ∗
        ((sp + 2728#64) ↦₆₄ w3 ∗ ((sp + 2736#64) ↦₆₄ w4 ∗ (sp + 2744#64) ↦₆₄ w5))))) ∗
        ((sp + 2752#64) ↦₆₄ w6 ∗ (sp + 2760#64) ↦₆₄ w7) by ac_rfl]
  exact sepConj_mono hc6
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

/-! ## 2. Unified 6-Word `SignalProtocolError` Unwind Funnel (`+0x1648 -> s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Unified Stage P2 Error Funnel (`+0x1648 -> s0.readReg64 .x30`) on `tripleRatchetProgAtExt`:
Composes `p2_err_tail_a_ext_wp`, `drop_process_prekey_impl_state1_ext_ok`, `p2_err_tail_b1_ext_wp`,
`p2_err_tail_b2_ext_wp`, and `p3_err_tail_b_ext_wp` (`prevCap = 0`) /
`p3_err_tail_prev_dealloc_ext_wp` (`prevCap ≠ 0`), writing `speWordsAt outPtr w0 w1 w2 w3 w4 w5`,
setting `[coroPtr + 0x2c0] = 1#8`, preserving `sf.trace = s.trace`, and restoring
`sf.sp = sp + 0xcd0#64` and `ClosureCalleeSaved s0 sf`. -/
theorem stageP2_err_funnel_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooks A img.base ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    w0 w1 w2 w3 w4 w5 r23 u_c8 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ w4) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ w3) ∗
       memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       A.pool ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ w4) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ w3) ∗
          memRegion (sp + 0x370#64) 36 ∗
          cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗
          logOff img ∗
          A.pool ∗
          stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      Qp := by
  have hstep1 := p2_err_tail_a_ext_wp img.base ext s coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 b_4f2
    herr_ne_neg3 hr23_lo hpc hrun hsp_align
    hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  have hinv1 : ImgCallInv img s1 := ⟨hF1, hsym1⟩
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have hdrop := drop_process_prekey_impl_state1_ext_ok (b := img.base) (ext := ext)
  have hstk48 : stackAt sp allocHookStack =
      stackAt (sp - 48#64) (allocHookStack - 48) ∗ cells (sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells sp (allocHookStack - 48) 6 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hinv1 hdrop hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [dropProcessPrekeyImplState1Spec]
      rw [hsp1, show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp1,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl,
      sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = w0 := hx20_cs2.trans hx20_1
  have hx21_2 : s2.readReg64 .x21 = w4 >>> 8 := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = w2 := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = r23 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = w1 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = w5 := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  have hstep3 := p2_err_tail_b1_ext_wp img.base ext s2 coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8 b_390
    hb herr_ne_neg2 hr23_lo hpc2 hrun2 hsp2_align
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, _, hx21_3, hx25_3, hx26_3, hx28_3, _, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hc250 := cells6_fold (coroPtr + 0x250#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hx21_3' : s3.readReg64 .x21 = s3.sp + 0x370#64 := by rw [hx21_3, hsp3]
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3]
  have hx28_3' : s3.readReg64 .x28 = s3.sp + 0xa90#64 := by rw [hx28_3, hsp3]
  have hstep4 := p2_err_tail_b2_ext_wp img.base ext s3 coroPtr w0 outPtr
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    u370 u378 u380 u388 (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u390
    hpc3 hrun3 hsp3_align hx19_3 hx21_3' hx25_3' hx26_3 hx28_3'
  rw [hsp3] at hstep4
  refine p2_bind_sepWP_qp_frame hF3 hsym3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hF4 hsym4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, _, _, hvregs4_3⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (sp_a90_rejoin sp w0 w1 w2 w3 w4 w5) (by sep_focus) ?_
  have hf8 :
      ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ⊢
        memRegion (coroPtr + 0xf8#64) 344 := by
    rw [ProofLib.memRegion_split (coroPtr + 0xf8#64) 8 336 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  refine SepWPp.weaken_frame hf8 (by sep_focus) ?_
  have hx25_4' : s4.readReg64 .x25 = s4.sp + 0x210#64 := by rw [hx25_4, hsp4]
  refine SepWPp.weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 =>
    SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c =>
    SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c =>
    SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  have hzero64 : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero64]
  by_cases hcap : prevCap = 0#64
  · subst hcap
    simp only [↓reduceIte]
    sep_norm
    have hstep5 := p3_err_tail_b_ext_wp img.base ext s4 coroPtr outPtr w0 prevPtr
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc4 hrun4 hsp4_align hx19_4 hx22_4 hx25_4' hx26_4 hx28_4
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_qp_frame hF4 hsym4 hstep5 (by sep_focus)
      fun sf _ hpcf hrunf hFf hsymf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf_4, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f,
      hx25f, hx26f, hx27f, hx28f, hx29f, _, hvregsf_4⟩
    refine SepWPp.weaken_frame
      (Entails.of_eq (speWordsAt_realign_outPtr outPtr w0 w1 w2 w3 w4 w5)) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (sp_370_rejoin sp
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (coro_e0_368_fold coroPtr 0#64 prevPtr 0#64) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0).symm) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ?_
    have htr_full : sf.trace = s.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1]
    have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hvregsf_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
    exact ⟨htr_full, Entails.of_eq (eq_of_sep_emp (by sep_focus)),
      hspf,
      ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, True.intro⟩,
      hvregs_full,
      ⟨hFf, hsymf⟩⟩
  · simp only [hcap, ↓reduceIte]
    sep_norm
    have hstep5 := p3_err_tail_prev_dealloc_hooks_wp img.base ext hH s4 coroPtr outPtr w0
      prevCap prevPtr
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc4 hrun4 hsp4_align hx19_4 hx22_4 hx25_4' hx26_4 hx28_4
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_qp_frame hF4 hsym4 hstep5 (by sep_focus)
      fun sf _ hpcf hrunf hFf hsymf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf_4, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f,
      hx25f, hx26f, hx27f, hx28f, hx29f, _, hvregsf_4⟩
    refine SepWPp.weaken_frame
      (Entails.of_eq (speWordsAt_realign_outPtr outPtr w0 w1 w2 w3 w4 w5)) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (sp_370_rejoin sp
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (coro_e0_368_fold coroPtr prevCap prevPtr 0#64) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0).symm) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ?_
    have htr_full : sf.trace = s.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1]
    have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hvregsf_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
    exact ⟨htr_full, Entails.of_eq (eq_of_sep_emp (by sep_focus)),
      hspf,
      ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, True.intro⟩,
      hvregs_full,
      ⟨hFf, hsymf⟩⟩

theorem stageP2_err_funnel_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : AllocContracts img.base A ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    w0 w1 w2 w3 w4 w5 r23 u_c8 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ w4) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ w3) ∗
       memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       A.pool ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ w4) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ w3) ∗
          memRegion (sp + 0x370#64) 36 ∗
          cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗
          logOff img ∗
          A.pool ∗
          stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      Qp :=
  stageP2_err_funnel_hooks_ok (Qp := Qp) (.of_allocContracts hA) s0 s sp coroPtr outPtr
    prevCap prevPtr w0 w1 w2 w3 w4 w5 r23 u_c8 b_2c0 b_390 b_4f2 hb hprev_lt herr_ne_neg3
    herr_ne_neg2 hr23_lo hinv hsp_eq hpc hrun hsp_align
    hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

/-! ## 3. Store-Error Unwind Arms 1–3 (`+0x0f38`, `+0x0998`, `+0x09c4` -> `s0.readReg64 .x30`) -/

theorem p2_zeroExtend32_extractLsb_lo (w : BitVec 64) :
    ((w.extractLsb' 0 32).zeroExtend 64).extractLsb' 0 32 = w.extractLsb' 0 32 := by
  bv_bits

set_option maxHeartbeats 1200000 in
/-- Arm 1 (`+0x0f38 -> s0.readReg64 .x30`): `SignedPreKeyStore::get_signed_pre_key` `.error e`
unwind through `hspkOk.getFutDrop`, `p2_err1b_hooks_wp`, and `stageP2_err_funnel_hooks_ok`. -/
theorem p2_arm1_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A img.base}
    (hH : StageP2ClosureHooks A img.base ext)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (s0 s : State)
    (sp coroPtr outPtr prevCap prevPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (e : spkKit.GetErr)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
          ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
          ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt spkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  dsimp only [spkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 spkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err1a_ext_wp img.base ext s coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) (img.base + spkKit.getFutDropOff) (spkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    (spkKit.getErr.w1 e) (spkKit.getErr.w2 e) (spkKit.getErr.w3 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418
    (spkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  have hinv1 : ImgCallInv img s1 := ⟨hF1, hsym1⟩
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
      (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    hinv1 hspkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr signedPreKeyId 1#8) (by sep_focus) ?_
  have hstep3 := p2_err1b_hooks_wp img.base ext hH s2 coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) ctxPtr u_a8 u_c0 spkKit.getBoxSize
    spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_err_funnel_hooks_ok (Qp := fun _ _ => False) hH s0 s3 sp coroPtr outPtr prevCap prevPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) (spkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 hb hprev_lt
    (spkKit.getErr.w0_ne_pending e) (spkKit.getErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by rw [htrf, htr3_2, htr2_1, htr1]
  refine ⟨htr_full, ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_arm1_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A img.base}
    (hA : AllocContracts img.base A ext)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (s0 s : State)
    (sp coroPtr outPtr prevCap prevPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (e : spkKit.GetErr)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
          ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
          ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt spkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp :=
  p2_arm1_err_hooks_ok (Qp := Qp) (.of_allocContracts hA) hspkOk s0 s sp coroPtr outPtr
    prevCap prevPtr spkStorePtr spkFutPtr ctxPtr v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    signedPreKeyId b_2c0 b_390 b_4f2 e hb hprev_lt hinv hsp_eq hpc hrun hsp_align
    hx19 hx21 hx23 hx25 hx26 hx27 hvregs

set_option maxHeartbeats 1200000 in
/-- Arm 2 (`+0x0998 -> s0.readReg64 .x30`): `KyberPreKeyStore::get_kyber_pre_key` `.error e`
unwind through `hkpkOk.getFutDrop`, `p2_err2b_hooks_wp`, and `stageP2_err_funnel_hooks_ok`. -/
theorem p2_arm2_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A img.base}
    (hH : StageP2ClosureHooks A img.base ext) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (hb : img.base &&& 0xfff#64 = 0#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
          ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
          ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt kpkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  dsimp only [kpkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 kpkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err2a_ext_wp img.base ext s coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) (img.base + kpkKit.getFutDropOff) (kpkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e) (kpkKit.getErr.w3 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418
    (kpkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
      (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hkpkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8) (by sep_focus) ?_
  have hstep3 := p2_err2b_hooks_wp img.base ext hH s2 coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) ctxPtr u_c0 b_4f1 kpkKit.getBoxSize
    kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_err_funnel_hooks_ok (Qp := fun _ _ => False) hH s0 s3 sp coroPtr outPtr prevCap prevPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e)
    (((kpkKit.getErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 hb hprev_lt
    (kpkKit.getErr.w0_ne_pending e) (kpkKit.getErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (kpkKit.getErr.w1 e))
    ⟨hF3, hsym3⟩ hsp3 hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_arm2_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A img.base}
    (hA : AllocContracts img.base A ext) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (hb : img.base &&& 0xfff#64 = 0#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
          ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
          ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt kpkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp :=
  p2_arm2_err_hooks_ok (Qp := Qp) (.of_allocContracts hA) hkpkOk s0 s sp coroPtr outPtr
    prevCap prevPtr kyberStorePtr kyberFutPtr ctxPtr v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    kyberPreKeyId b_2c0 b_390 b_4f1 b_4f2 e hb hprev_lt hinv hsp_eq hpc hrun hsp_align
    hx19 hx21 hx23 hx25 hx26 hx27 hvregs

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

