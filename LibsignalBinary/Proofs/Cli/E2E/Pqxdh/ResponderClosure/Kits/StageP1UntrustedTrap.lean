/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3Trap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAuxTrap

/-!
# Stage P1 Untrusted-Identity Exit over `trTrapProgAt`

Proves `calleeSavedVRegs`-preserving `stageP1_untrusted_err_ok_kit_trap` (`+0x6e4 →
s0.readReg64 .x30`) and `stageP1_untrusted_ok_kit_trap` (`entry → s0.readReg64 .x30`) over
`trTrapProgAt img.base C abs`.
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
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Unified `SessionRecord` Drop (`+0x3588 -> +0x359c`) & Return Epilogue (`+0x359c -> ret`) -/

set_option maxHeartbeats 1200000 in
theorem p1_err_drop_record_vregs_wp_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s : State) (coroPtr : BitVec 64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       A.pool ∗
       stackAt s.sp dropSessionStructureLocal2Stack)
      (fun s2 P_m =>
        (P_m ⊢
          ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
            ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
            ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            (if prevCap = 0 then emp
             else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗
            A.pool ∗
            stackAt s.sp dropSessionStructureLocal2Stack) ∧
        s2.sp = s.sp ∧
        s2.trace = s.trace ∧
        s2.readReg64 .x19 = coroPtr ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        ImgCallInv img s2)
      Qp := by
  cases opt with
  | none =>
    dsimp only [p1LoadedRecordAt, sessionRecordEmptyHeaderAt]
    sep_norm
    have hstep := p1_err_drop_none_vregs_wp_trap img.base C abs s coroPtr hpc hrun hsp_align hx19
    refine SepWPp.ret_sepWP_steps_frame hinv hstep (by sep_focus)
      fun s2 _ _ _ hinv2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
    refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hinv2⟩
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    refine Entails.pure_right (by decide) ?_
    have hite0 : (0#64 = 0) = True := eq_true rfl
    simp only [hite0, ↓reduceIte]
    sep_norm
    have hf8 :
        ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
          memRegion (coroPtr + 248#64) 344 := by
      rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono_left
          (Q := ((coroPtr + 224#64) ↦₆₄ 0#64) ∗
                ((coroPtr + 232#64) ↦₆₄ 8#64) ∗
                ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                A.pool ∗
                stackAt s.sp dropSessionStructureLocal2Stack) hf8)
        (Entails.of_eq (by ac_rfl)))
  | some r =>
    dsimp only [p1LoadedRecordAt]
    sep_norm
    refine SepWPp.exists_elim fun g => ?_
    refine SepWPp.pure_elim fun _ => ?_
    rw [sessionRecordAt_eq_vecAt_sep_curSessionAt A (coroPtr + 0xe0#64) g r]
    refine SepWPp.weaken_frame (prevVecAt_unpack A coroPtr g.prevCap g.prevPtr) (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun hprev_lt => ?_
    refine SepWPp.weaken_frame
      (Entails.refl (curSessionAt A (coroPtr + 0xf8#64) g.cur r.currentSession))
      (by sep_focus) ?_
    cases hcur_g : g.cur <;> cases hcur_r : r.currentSession
    · dsimp only [curSessionAt, noneCap]
      have hstep := p1_err_drop_none_vregs_wp_trap img.base C abs s coroPtr hpc hrun hsp_align hx19
      refine SepWPp.ret_sepWP_steps_frame hinv hstep (by sep_focus)
        fun s2 _ _ _ hinv2 hregs2 => ?_
      rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
      refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hinv2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      have hf8 :
          ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
            memRegion (coroPtr + 248#64) 344 := by
        rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (sepConj_mono_left
            (Q := ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗
                  ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
                  ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                  (if g.prevCap = 0 then emp
                   else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
                     memRegion g.prevPtr (g.prevCap.toNat * 24)) ∗
                  A.pool ∗
                  stackAt s.sp dropSessionStructureLocal2Stack) hf8)
          (Entails.of_eq (by ac_rfl)))
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · rename_i G ses
      dsimp only [curSessionAt, sessionStateReprAt]
      sep_norm
      refine SepWPp.pure_elim fun _ => ?_
      have hss_split :
          ∃ R_ss : SepProp,
            (sessionStateAt A (coroPtr + 0xf8#64) G ses.state ⊢
              ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ ((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss) ∧
            (((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss ⊢
              sessionStateAt A (coroPtr + 0xf8#64) G ses.state) := by
        unfold sessionStateAt
        exact pure_vecGhost_sep_split
      obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := hss_split
      refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
      sep_norm
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne : G.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
      have hto_call := p1_err_drop_ss_to_call_vregs_wp_trap img.base C abs s coroPtr G.localIk.cap
        hcap_ne hpc hrun hsp_align hx19
      refine SepWPp.bind_sepWP_steps_frame hinv hto_call (by sep_focus)
        fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1, hvregs1⟩
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
      refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
      have hdrop_ss := DropSS3.drop_session_structure3_ok_std3_trap
        (b := img.base) (C := C) (abs := abs) hA
      refine SepWPp.call_nopanic_steps_frame
        (spec := dropSessionStructureLocal2Spec A)
        (x := ⟨coroPtr + 0xf8#64, G, ses.state⟩)
        (T := sessionStateAt A (coroPtr + 0xf8#64) G ses.state ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
        hinv1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
        hx0_1 (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
      dsimp only [dropSessionStructureLocal2Spec]
      rw [hsp1, sepConj_assoc]
      refine SepWPp.pure_elim fun htr2_1 => ?_
      refine SepWPp.done hpc2 hrun2 ?_
      rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
      refine ⟨?_, hsp2_1.trans hsp1, htr2_1.trans htr1,
        hx19_cs2.trans hx19_1, hx22_cs2.trans hx22_1,
        hx25_cs2.trans hx25_1, hx26_cs2.trans hx26_1, hx28_cs2.trans hx28_1,
        hvregs_cs2.trans hvregs1, hinv2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_vregs_wp_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {abs : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hA : AllocHooks A abs)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       memRegion (coroPtr + 0xf8#64) 344 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      Qp := by
  have hx25_s : s.readReg64 .x25 = s.sp + 0x210#64 := by rw [hsp_eq]; exact hx25
  rw [savedRegsAt_eq_sp_c70 sp s0]
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
  let R_tail : SepProp :=
    ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗
    ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗
    ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) ∗
    A.pool ∗
    stackAt sp allocHookStack
  by_cases hcap : prevCap = 0#64
  · subst hcap
    simp only [↓reduceIte]
    sep_norm
    have htail := p3_err_tail_b_vregs_wp_trap
      img.base C abs s coroPtr outPtr 0x800000000000000c#64 prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hinvf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr 0#64 prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))
  · simp only [hcap, ↓reduceIte]
    have htail := p1_err_tail_prev_dealloc_vregs_wp_trap img.base C abs hA s coroPtr outPtr
      0x800000000000000c#64 prevCap prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hinvf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr prevCap prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))

set_option maxHeartbeats 1200000 in
theorem p1_err_drop_and_return_vregs_wp_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hA : AllocHooks A abs)
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s0 s3 : State) (sp coroPtr outPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hinv3 : ImgCallInv img s3)
    (hsp3_s : s3.sp = sp)
    (hpc3 : s3.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx22_3 : s3.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25_3 : s3.readReg64 .x25 = sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx28_3 : s3.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s3
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp untrustedErrCallStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp untrustedErrCallStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s3.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s3 ∧
        ImgCallInv img sf)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt))
    (by sep_focus) ?_
  have hdrop := p1_err_drop_record_vregs_wp_trap (Scope := Scope) (Qp := PanicOomProp s0) hA opt s3 coroPtr
    hinv3 hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hdrop
  refine SepWPp.bind_sepWPp_steps_frame hdrop (by sep_focus)
    fun s4 _ hpc4 hrun4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, hvregs4_3, hinv4⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun prevCap => SepWPp.exists_elim fun prevPtr => ?_
  refine SepWPp.pure_elim fun hprev_lt => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt))
    (by sep_focus) ?_
  have hret := p1_err_tail_prev_vregs_wp_trap (Qp := PanicOomProp s0) hA s0 s4 sp coroPtr outPtr
    prevCap prevPtr cap ptr devWord u_278 b_2c0 peer pad
    hprev_lt hpad hw4 hinv4 hsp4_s hpc4 hrun4 hsp4_align
    hx19_4 (hx22_4.trans hx22_3) (hx25_4.trans hx25_3)
    (hx26_4.trans hx26_3) (hx28_4.trans hx28_3)
  refine SepWPp.bind_sepWPp_steps_frame hret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_4, hcs_f, hvregsf_4, hinvf⟩
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hspf, htrf_4.trans htr4_3, hcs_f, hvregsf_4.trans hvregs4_3, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## 2. Exported Kit Theorems (`stageP1_untrusted_err_ok_kit_trap` & `stageP1_untrusted_ok_kit_trap`) -/

set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_err_ok_kit_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {abs : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A img.base}
    {ikit : IdentityStoreSpec A img.base}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hA : AllocHooks A abs)
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc =
      (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp untrustedErrCallStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          cells (s.sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          logOff img ∗
          kit.storeAt sessStorePtr st ∗
          ikit.identityAt idStorePtr
            (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt s.sp untrustedErrCallStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hstep1 := p1_untrusted_to_clone_vregs_wp_trap img.base C abs s coroPtr remoteAddrPtr
    hpc hrun hsp_align hx19 hx20 hx23
  refine SepWPp.bind_sepWP_steps_frame hinv hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have htr1_pre : s0.trace <+: s1.trace := htr1 ▸ htr
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A peer remoteAddrPtr =
        vecGhostAt A peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt))
    (by sep_focus) ?_
  have hclone := stringClone_ok_cli_trap (A := A) (b := img.base) (C := C) (abs := abs) hA
  refine SepWPp.call_oom_steps_frame
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name))
    (P_spec := vecGhostAt A peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool ∗ stackAt s1.sp extHookStack)
    hinv1 htr1_pre hclone hpc1 hrun1 hsp1_al hx30_1
    (stringClone_pre_intro hx0_1 hx8_1)
    (by rw [hsp1]; sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [stringCloneSpec]
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hstep3 := p1_untrusted_post_clone_vregs_wp_trap img.base C abs s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hb hw4 hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx25_2
  rw [hsp2_s] at hstep3
  refine SepWPp.bind_sepWP_steps_frame hinv2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _, hvregs3_2⟩
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hdrop_ret := p1_err_drop_and_return_vregs_wp_trap
    (Scope := Scope)
    hA hstack_lt opt s0 s3 s.sp coroPtr outPtr cap ptr devWord (s2.readReg64 .x27) b_2c0
    peer pad hpad hw4 hinv3 hsp3_s hpc3 hrun3 hsp_align
    hx19_3 hx22_3 hx25_3 hx26_3 hx28_3
  refine SepWPp.bind_sepWPp_steps_frame hdrop_ret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_3, hcs_f, hvregsf_3, hinvf⟩
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_3, htr3_2, htr2_1, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf_3, hvregs3_2, hvregs_cs2, hvregs1]
  refine ⟨htr_full, ?_, hspf, hcs_f, hvregs_full, hinvf.1, hinvf.2⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
