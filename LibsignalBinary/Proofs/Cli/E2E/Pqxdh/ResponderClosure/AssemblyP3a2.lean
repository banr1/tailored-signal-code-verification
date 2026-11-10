/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEntry
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP3
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

/-!
# Responder Closure Stage P3 `SessionState` Clone (`+0x1778 → +0x1bac`)

Proves `senderChain_clone3_ok`, `stageP3_sub1_ok` (`+0x1778 → +0x195c`), `stageP3_sub2_ok`
(`+0x195c → +0x1bac`), and `stageP3_clone_ok` for freshly initialized Bob `SessionState`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.ChainClone3

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

/-! ## 1. `senderChain_clone3_ok` -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.senderChain_clone3_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.SenderChainClone3Ok_trap b C A abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.senderChain_clone_ok_trap hA

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.senderChain_clone3_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.SenderChainClone3Ok b C A ctl abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.senderChain_clone_ok hA

/-! ## 2. `stageP3_sub1_ok` (`+0x1778 → +0x195c`) -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr u_50 u_98 u_d0 : BitVec 64)
    (u_7c : BitVec 32)
    (locIdBytes remIdBytes rootKeyBytes : List (BitVec 8))
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (hroot_len : rootKeyBytes.length = 32)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
         (locIdPtr ↦ₛ locIdBytes) ∗
       ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
         (remIdPtr ↦ₛ remIdBytes) ∗
       ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
         (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
       ((s.sp + 0x50#64) ↦₆₄ u_50) ∗ ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        ∃ newLocIdPtr newRemIdPtr newRootKeyPtr,
          newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
              (locIdPtr ↦ₛ locIdBytes) ∗
            ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
              (remIdPtr ↦ₛ remIdBytes) ∗
            ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
              (rootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
            A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗
            A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
            A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.sp + 0x930#64 ∧
          s1.readReg64 .x23 = newLocIdPtr ∧ s1.readReg64 .x24 = 33#64 ∧
          s1.readReg64 .x25 = newRemIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  refine SepWPp.bind_sepWP_frame hF hsym
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1a_wp_trap b C abs s coroPtr locIdPtr 33#64 u_d0 4#32 u_7c
      (by decide) hpc hrun hsp_align hx19) (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx27_1, hx29_1⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWPp.bind_sepWPp_frame_dep
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_179c_ok_trap img b C abs hA s0 s1 33#64 33 emp (by decide) (by decide)
      hF1 hsym1 hpc1 hrun1 hsp1_align (htr1.trans htr) hx0_1 hx1_1)
    (by rw [hsp1]; sep_focus)
    fun s2 hpc2 hrun2 ⟨hnew1, hsp2, htr2, hcs2, hF2, hsym2⟩ => ?_
  set newLocIdPtr := s2.readReg64 .x0
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = locIdPtr := hcs2.2.2.1.trans hx21_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  have hloc_bv : BitVec.ofNat 64 locIdBytes.length = 33#64 := by rw [hloc_len]
  refine SepWPp.bind_sepWP_frame hF2 hsym2
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1b_wp_trap b C abs s2 coroPtr locIdPtr newLocIdPtr locIdBytes
      hnew1 (by omega) hpc2 hrun2 hsp2_align rfl hx19_2 hx21_2)
    (by rw [hsp1, hsp2', hloc_bv, hloc_len]; sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3, hx19_3, hx23_3, hx27_3, hx29_3⟩ => ?_
  have hsp3' : s3.sp = s.sp := hsp3.trans hsp2'
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3']; exact hsp_align
  refine SepWPp.bind_sepWP_frame hF3 hsym3
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2a_wp_trap b C abs s3 coroPtr remIdPtr 33#64 (by decide) hpc3 hrun3 hsp3_align hx19_3)
    (by sep_focus)
    fun s4 hpc4 hrun4 hF4 hsym4 ⟨hsp4, htr4, hx0_4, hx1_4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4,
      hx27_4, hx29_4⟩ => ?_
  have hsp4' : s4.sp = s.sp := hsp4.trans hsp3'
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4']; exact hsp_align
  have htr4' : s4.trace = s0.trace := by rw [htr4, htr3, htr2, htr1, htr]
  refine SepWPp.bind_sepWPp_frame_dep
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_18fc_ok_trap img b C abs hA s0 s4 33 emp (by decide) (by decide)
      hF4 hsym4 hpc4 hrun4 hsp4_align htr4' hx0_4 hx1_4)
    (by rw [hsp4']; sep_focus)
    fun s5 hpc5 hrun5 ⟨hnew2, hsp5, htr5, hcs5, hF5, hsym5⟩ => ?_
  set newRemIdPtr := s5.readReg64 .x0
  have hsp5' : s5.sp = s.sp := hsp5.trans hsp4'
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5']; exact hsp_align
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hcs5.1.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = remIdPtr := hcs5.2.2.1.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = s.sp + 0x930#64 := by rw [hcs5.2.2.2.1, hx22_4, hsp3']
  have hx23_5 : s5.readReg64 .x23 = newLocIdPtr := hcs5.2.2.2.2.1.trans (hx23_4.trans hx23_3)
  have hx24_5 : s5.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length := by
    rw [hcs5.2.2.2.2.2.1, hx24_4, hrem_len]
  have hx27_5 : s5.readReg64 .x27 = s.readReg64 .x27 :=
    hcs5.2.2.2.2.2.2.2.2.1.trans (hx27_4.trans (hx27_3.trans hx27_2))
  have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 :=
    hcs5.2.2.2.2.2.2.2.2.2.2.1.trans (hx29_4.trans (hx29_3.trans hx29_2))
  refine SepWPp.bind_sepWP_frame hF5 hsym5
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2b_wp_trap b C abs s5 coroPtr remIdPtr newRemIdPtr remIdBytes
      hnew2 (by omega) hpc5 hrun5 hsp5_align rfl hx19_5 hx21_5 hx24_5)
    (by rw [hsp4', hrem_len]; sep_focus)
    fun s6 hpc6 hrun6 hF6 hsym6 ⟨hsp6, htr6, hx19_6, hx22_6, hx23_6, hx24_6, hx25_6, hx27_6,
      hx29_6⟩ => ?_
  have hsp6' : s6.sp = s.sp := hsp6.trans hsp5'
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6']; exact hsp_align
  refine SepWPp.bind_sepWP_frame hF6 hsym6
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3a_wp_trap b C abs s6 coroPtr rootKeyPtr 32#64 u_98
      (by decide) hpc6 hrun6 hsp6_align hx19_6)
    (by rw [hsp6']; sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 ⟨hsp7, htr7, hx0_7, hx1_7, hx19_7, hx21_7, hx22_7, hx23_7, hx24_7,
      hx25_7, hx26_7, hx27_7, hx29_7⟩ => ?_
  have hsp7' : s7.sp = s.sp := hsp7.trans hsp6'
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7']; exact hsp_align
  have htr7' : s7.trace = s0.trace := by rw [htr7, htr6, htr5, htr4']
  refine SepWPp.bind_sepWPp_frame_dep
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1938_ok_trap img b C abs hA s0 s7 32 emp (by decide) (by decide)
      hF7 hsym7 hpc7 hrun7 hsp7_align htr7' hx0_7 hx1_7)
    (by rw [hsp7']; sep_focus)
    fun s8 hpc8 hrun8 ⟨hnew3, hsp8, htr8, hcs8, hF8, hsym8⟩ => ?_
  set newRootKeyPtr := s8.readReg64 .x0
  have hsp8' : s8.sp = s.sp := hsp8.trans hsp7'
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8']; exact hsp_align
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hcs8.1.trans hx19_7
  have hx21_8 : s8.readReg64 .x21 = rootKeyPtr := hcs8.2.2.1.trans hx21_7
  have hx22_8 : s8.readReg64 .x22 = s.sp + 0x930#64 :=
    hcs8.2.2.2.1.trans (hx22_7.trans (hx22_6.trans hx22_5))
  have hx23_8 : s8.readReg64 .x23 = newLocIdPtr :=
    hcs8.2.2.2.2.1.trans (hx23_7.trans (hx23_6.trans hx23_5))
  have hx24_8 : s8.readReg64 .x24 = 33#64 := by
    rw [hcs8.2.2.2.2.2.1, hx24_7, hx24_6, hrem_len]
  have hx25_8 : s8.readReg64 .x25 = newRemIdPtr :=
    hcs8.2.2.2.2.2.2.1.trans (hx25_7.trans hx25_6)
  have hx26_8 : s8.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length := by
    rw [hcs8.2.2.2.2.2.2.2.1, hx26_7, hroot_len]
  have hx27_8 : s8.readReg64 .x27 = s.readReg64 .x27 :=
    hcs8.2.2.2.2.2.2.2.2.1.trans (hx27_7.trans (hx27_6.trans hx27_5))
  have hx29_8 : s8.readReg64 .x29 = s.readReg64 .x29 :=
    hcs8.2.2.2.2.2.2.2.2.2.2.1.trans (hx29_7.trans (hx29_6.trans hx29_5))
  refine SepWPp.ret_sepWP_frame hF8 hsym8
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3b_wp_trap b C abs s8 coroPtr rootKeyPtr newRootKeyPtr u_50 rootKeyBytes
      hnew3 (by omega) hpc8 hrun8 hsp8_align rfl hx19_8 hx21_8 hx26_8)
    (by rw [hsp7', hsp8', hroot_len]; sep_focus)
    fun s9 _ _ hF9 hsym9 ⟨hsp9, htr9, hx19_9, hx22_9, hx23_9, hx24_9, hx25_9, hx27_9, hx29_9⟩ => ?_
  refine ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, hnew1, hnew2, hnew3, ?_,
    hsp9.trans hsp8', by rw [htr9, htr8, htr7'], hF9, hsym9, hx19_9,
    hx22_9.trans hx22_8, hx23_9.trans hx23_8, hx24_9.trans hx24_8,
    hx25_9.trans hx25_8, hx27_9.trans hx27_8, hx29_9.trans hx29_8⟩
  simp only [hsp1, hsp2', hsp3', hsp4', hsp5', hsp6', hsp7', hsp8', hloc_bv]
  exact Entails.of_eq (by ac_rfl)

/-- Substage P3.Sub1 (`+0x1778 -> +0x195c`): Clones `local_identity_public` (`33` B at `locIdPtr`),
  `remote_identity_public` (`33` B at `remIdPtr`),
and `root_key` (`32` B at `rootKeyPtr`) with OOM handling. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr u_50 u_98 u_d0 : BitVec 64)
    (u_7c : BitVec 32)
    (locIdBytes remIdBytes rootKeyBytes : List (BitVec 8))
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (hroot_len : rootKeyBytes.length = 32)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
         (locIdPtr ↦ₛ locIdBytes) ∗
       ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
         (remIdPtr ↦ₛ remIdBytes) ∗
       ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
         (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
       ((s.sp + 0x50#64) ↦₆₄ u_50) ∗ ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        ∃ newLocIdPtr newRemIdPtr newRootKeyPtr,
          newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
              (locIdPtr ↦ₛ locIdBytes) ∗
            ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
              (remIdPtr ↦ₛ remIdBytes) ∗
            ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
              (rootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
            A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗
            A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
            A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.sp + 0x930#64 ∧
          s1.readReg64 .x23 = newLocIdPtr ∧ s1.readReg64 .x24 = 33#64 ∧
          s1.readReg64 .x25 = newRemIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok_trap
      img b C abs hA s0 s coroPtr locIdPtr remIdPtr rootKeyPtr u_50 u_98 u_d0 u_7c
      locIdBytes remIdBytes rootKeyBytes hloc_len hrem_len hroot_len
      hF hsym hpc hrun hsp_align htr hx19)

/-! ## 3. `stageP3_sub2_ok` (`+0x195c → +0x1bac`) and `stageP3_clone_ok` -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_chainClone3_eq_0x766c4_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name = b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")) := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name) = b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]"))
  rw [show libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name = (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]") from
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")]

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_chainClone3_eq_0x766c4 (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name = b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_chainClone3_eq_0x766c4_trap b C abs

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub2_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr aliceBasePtr ctxPtr
    u_38 u_40 u_48 u_60 u_68 u_70
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter f248 f24c u_30 u_34 u_5c : BitVec 32)
    (sg : SenderChainGhost) (sc : SenderChain)
    (aliceBaseBytes : List (BitVec 8)) (halice_len : aliceBaseBytes.length = 33)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx23 : s.readReg64 .x23 = newLocIdPtr) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (A.pool ∗ stackAt s.sp chainCloneStack ∗
       optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
       memRegion (s.sp + 0x3e0#64) 104 ∗
       ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
       ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
         ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ u_40) ∗ ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗ ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
          (newAliceBasePtr : BitVec 64),
          sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          newAliceBasePtr ≠ 0#64 ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
            optSenderChainHeap A (some sg') (some sc) ∗
            ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
            ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
            A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
              ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗
              ((s.sp + 0x48#64) ↦₆₄ c0) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
            ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
              ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
              ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
              ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
              ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
              ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 1#64 ∧
          s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x23 = newAliceBasePtr ∧
          s1.readReg64 .x24 = 33#64 ∧ s1.readReg64 .x25 = 8#64 ∧ s1.readReg64 .x26 = 0#64 ∧
          s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = 32#64 ∧
            s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  rw [optSenderChainAt_some_eq_cap A (coroPtr + 0x188#64) sg sc]
  simp only [sepConj_assoc]
  refine ChainClone3.sepWPp_pure_mid fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsc_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hsrk_cap_lt
  refine SepWPp.bind_sepWP_frame hF hsym
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a1_wp_trap b C abs s coroPtr sg.srk.cap prevCounter u_5c
      hsc_ne hpc hrun hsp_align hx19) (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx27_1, hx29_1, hx30_1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by
    change (s1.sp &&& 15#64 == 0#64) = true
    rw [hsp1]; exact hsp_align
  have hpc1' : s1.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name := by
    rw [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.fnAddr_chainClone3_eq_0x766c4_trap]; exact hpc1
  have hcall := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.senderChain_clone3_ok_trap (b := b) (C := C) (A := A)
    (abs := abs) hA
  have hopt_reasm :
      (((coroPtr + 0x188#64) ↦₆₄ sg.srk.cap) ∗
        optSenderChainSomeRest A (coroPtr + 0x188#64) sg sc) ⊢
      optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) := by
    rw [optSenderChainAt_some_eq_cap A (coroPtr + 0x188#64) sg sc]
    exact Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
  refine SepWPp.weaken_frame hopt_reasm (by sep_focus) ?_
  refine SepWPp.call_frame_frozen_oom
    (spec := senderChainCloneSpec A)
    (x := ⟨s.sp + 0x3e0#64, coroPtr + 0x188#64, sg, sc⟩)
    (φ := s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x1 = coroPtr + 0x188#64)
    (T := memRegion (s.sp + 0x3e0#64) 104 ∗
      optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
      A.pool ∗ stackAt s1.sp chainCloneStack)
    hF1 hsym1 (htr1.trans htr) hcall hpc1' hrun1 hsp1_al hx30_1
    rfl ⟨hx0_1, hx1_1⟩ (by rw [hsp1]; sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [senderChainCloneSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr2 => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun sg' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = s2.sp + 0x930#64 := by
    rw [hcs2.2.2.2.1, hx22_1, hx22, hsp2']
  have hx23_2 : s2.readReg64 .x23 = newLocIdPtr :=
    hcs2.2.2.2.2.1.trans (hx23_1.trans hx23)
  have hx24_2 : s2.readReg64 .x24 = 33#64 :=
    hcs2.2.2.2.2.2.1.trans (hx24_1.trans hx24)
  have hx25_2 : s2.readReg64 .x25 = newRemIdPtr :=
    hcs2.2.2.2.2.2.2.1.trans (hx25_1.trans hx25)
  have hx27_2 : s2.readReg64 .x27 = s2.sp + 0x370#64 := by
    rw [hcs2.2.2.2.2.2.2.2.2.1, hx27_1, hx27, hsp2']
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
    hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  refine SepWPp.weaken_pre
    (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0x3e0#64) (some sg') (some
      sc))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
    SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
    SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hsc_inl => ?_
  rw [chunks104W6QAt_sp_0x3e0_eq s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5]
  refine SepWPp.bind_sepWP_frame hF2 hsym2
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a2_wp_trap b C abs s2 coroPtr u_48
      c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
      (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64)
      (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
      (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64)
      (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
      (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64)
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx27_2)
    (by rw [hsp2']; sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3, hx19_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3⟩ => ?_
  have hsp3' : s3.sp = s.sp := hsp3.trans hsp2'
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3']; exact hsp_align
  have hx23_3' : s3.readReg64 .x23 = newLocIdPtr := hx23_3.trans hx23_2
  have hx24_3' : s3.readReg64 .x24 = 33#64 := hx24_3.trans hx24_2
  have hx25_3' : s3.readReg64 .x25 = newRemIdPtr := hx25_3.trans hx25_2
  have h3e0_mem :
      (((s2.sp + 0x3e0#64) ↦₆₄ c0) ∗
        ((s2.sp + 0x3e8#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
          ((s2.sp + 0x3f0#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
        ((s2.sp + 0x3f8#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
          ((s2.sp + 0x400#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
        ((s2.sp + 0x408#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
          ((s2.sp + 0x410#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
        ((s2.sp + 0x418#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
          ((s2.sp + 0x420#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
        ((s2.sp + 0x428#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
          ((s2.sp + 0x430#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
        ((s2.sp + 0x438#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
          ((s2.sp + 0x440#64) ↦₆₄ sq5.extractLsb' 64 64)) ⊢
      memRegion (s.sp + 0x3e0#64) 104 := by
    rw [hsp2', ← chunks104W6QAt_sp_0x3e0_eq s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5]
    exact chunks104W6QAt_entails_memRegion (s.sp + 0x3e0#64) c0 sq0 sq1 sq2 sq3 sq4 sq5
  refine SepWPp.weaken_frame h3e0_mem (by sep_focus) ?_
  refine SepWPp.bind_sepWP_frame hF3 hsym3
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4b_wp_trap b C abs s3 coroPtr 32#64 newLocIdPtr newRemIdPtr 33#64 ctxPtr
      u_60 u_68 u_70 hpc3 hrun3 hsp3_align hx19_3 hx23_3' hx24_3' hx25_3')
    (by rw [hsp3']; sep_focus)
    fun s4 hpc4 hrun4 hF4 hsym4 ⟨hsp4, htr4, hx19_4, _, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4,
      hx28_4, hx29_4⟩ => ?_
  have hsp4' : s4.sp = s.sp := hsp4.trans hsp3'
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4']; exact hsp_align
  refine SepWPp.bind_sepWP_frame hF4 hsym4
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a1_x28_wp_trap b C abs s4 coroPtr aliceBasePtr 33#64 u_38 u_40 f248 f24c u_30 u_34
      (by decide) hpc4 hrun4 hsp4_align hx19_4 hx23_4 hx26_4)
    (by rw [hsp4']; sep_focus)
    fun s5 hpc5 hrun5 hF5 hsym5 ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx21_5, hx22_5, hx24_5,
      hx25_5, hx27_5, hx28_5, hx29_5⟩ => ?_
  have hsp5' : s5.sp = s.sp := hsp5.trans hsp4'
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5']; exact hsp_align
  have htr5' : s5.trace = s0.trace := by rw [htr5, htr4, htr3, htr2, htr1, htr]
  rw [hsp1, stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.bind_sepWPp_frame_dep
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1b48_ok_trap img b C abs hA s0 s5 33 emp (by decide) (by decide)
      hF5 hsym5 hpc5 hrun5 hsp5_align htr5' hx0_5 hx1_5)
    (by rw [hsp5']; sep_focus)
    fun s6 hpc6 hrun6 ⟨hnew4, hsp6, htr6, hcs6, hF6, hsym6⟩ => ?_
  set newAliceBasePtr := s6.readReg64 .x0
  have hsp6' : s6.sp = s.sp := hsp6.trans hsp5'
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6']; exact hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6.1.trans hx19_5
  have hx21_6 : s6.readReg64 .x21 = aliceBasePtr := hcs6.2.2.1.trans hx21_5
  have hx22_6 : s6.readReg64 .x22 = 0xffffffffffffffff#64 :=
    hcs6.2.2.2.1.trans (hx22_5.trans hx22_4)
  have hx24_6 : s6.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length := by
    rw [hcs6.2.2.2.2.2.1, hx24_5, halice_len]
  have hx25_6 : s6.readReg64 .x25 = 8#64 :=
    hcs6.2.2.2.2.2.2.1.trans (hx25_5.trans hx25_4)
  have hx27_6 : s6.readReg64 .x27 = ctxPtr :=
    hcs6.2.2.2.2.2.2.2.2.1.trans (hx27_5.trans hx27_4)
  have hx28_6 : s6.readReg64 .x28 = 32#64 :=
    hcs6.2.2.2.2.2.2.2.2.2.1.trans (hx28_5.trans hx28_4)
  have hx29_6 : s6.readReg64 .x29 = s.readReg64 .x29 :=
    hcs6.2.2.2.2.2.2.2.2.2.2.1.trans (hx29_5.trans (hx29_4.trans (hx29_3.trans hx29_2)))
  refine SepWPp.bind_sepWP_frame hF6 hsym6
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a2_x28_wp_trap b C abs s6 coroPtr aliceBasePtr newAliceBasePtr aliceBaseBytes
      hnew4 (by omega) hpc6 hrun6 hsp6_align rfl hx19_6 hx21_6 hx24_6)
    (by rw [halice_len]; sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 ⟨hsp7, htr7, hx19_7, _, hx22_7, hx23_7, hx24_7, hx25_7, hx27_7,
      hx28_7, hx29_7⟩ => ?_
  have hsp7' : s7.sp = s.sp := hsp7.trans hsp6'
  refine SepWPp.ret_sepWP_frame hF7 hsym7
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b_none_wp_trap b C abs s7 coroPtr hpc7 hrun7 hx19_7)
    (by sep_focus)
    fun s8 _ _ hF8 hsym8 ⟨hsp8, htr8, hx19_8, _, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8,
      hx27_8, hx28_8, hx29_8⟩ => ?_
  have halice_bv : BitVec.ofNat 64 aliceBaseBytes.length = 33#64 := by rw [halice_len]
  refine ⟨sg', c0, sq0, sq1, sq2, sq3, sq4, sq5, newAliceBasePtr,
    hsrk', hpriv', hsc_inl, hnew4, ?_,
    hsp8.trans hsp7', by rw [htr8, htr7, htr6, htr5'], hF8, hsym8,
    hx19_8, hx21_8, hx22_8.trans (hx22_7.trans hx22_6),
    hx23_8.trans hx23_7, by rw [hx24_8, hx24_7, halice_bv],
    hx25_8.trans (hx25_7.trans hx25_6), hx26_8,
    hx27_8.trans (hx27_7.trans hx27_6),
    hx28_8.trans (hx28_7.trans hx28_6),
    hx29_8.trans (hx29_7.trans hx29_6)⟩
  rw [optSenderChainAt_some_eq_cap A (coroPtr + 0x188#64) sg sc]
  simp only [hsp1, hsp2', hsp3', hsp4', hsp5', hsp6', hsp7', stackAt_chainClone_eq_alloc s.sp]
  exact Entails.of_eq (by ac_rfl)

/-- Substage P3.Sub2 (`+0x195c -> +0x1bac`): Clones `sender_chain` (`Some (sg,
  sc)` at `coroPtr + 0x188`) via `senderChain_clone3_ok`,
handles `receiver_chains = []` / `pending_* = None` (`p3_seg4b_wp`), clones `alice_base_key`
(`33` B at `aliceBasePtr`) with OOM handling, and takes the empty `pq_ratchet_state` branch
(`[coroPtr + 0x180] = 0#64`) to `+0x1bac`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub2_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr aliceBasePtr ctxPtr
    u_38 u_40 u_48 u_60 u_68 u_70
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter f248 f24c u_30 u_34 u_5c : BitVec 32)
    (sg : SenderChainGhost) (sc : SenderChain)
    (aliceBaseBytes : List (BitVec 8)) (halice_len : aliceBaseBytes.length = 33)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx23 : s.readReg64 .x23 = newLocIdPtr) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (A.pool ∗ stackAt s.sp chainCloneStack ∗
       optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
       memRegion (s.sp + 0x3e0#64) 104 ∗
       ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
       ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
         ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ u_40) ∗ ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗ ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
          (newAliceBasePtr : BitVec 64),
          sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          newAliceBasePtr ≠ 0#64 ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
            optSenderChainHeap A (some sg') (some sc) ∗
            ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
            ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
            A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
              ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗
              ((s.sp + 0x48#64) ↦₆₄ c0) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
            ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
              ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
              ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
              ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
              ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
              ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 1#64 ∧
          s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x23 = newAliceBasePtr ∧
          s1.readReg64 .x24 = 33#64 ∧ s1.readReg64 .x25 = 8#64 ∧ s1.readReg64 .x26 = 0#64 ∧
          s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = 32#64 ∧
            s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub2_ok_trap img b C abs hA
      s0 s coroPtr newLocIdPtr newRemIdPtr aliceBasePtr ctxPtr
      u_38 u_40 u_48 u_60 u_68 u_70
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
      prevCounter f248 f24c u_30 u_34 u_5c sg sc aliceBaseBytes halice_len
      hF hsym hpc hrun hsp_align htr hx19 hx22 hx23 hx24 hx25 hx27)

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
    u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32)
    (sg : SenderChainGhost) (sc : SenderChain)
    (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List (BitVec 8))
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (hroot_len : rootKeyBytes.length = 32) (halice_len : aliceBaseBytes.length = 33)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
       ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
         (locIdPtr ↦ₛ locIdBytes) ∗
       ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
         (remIdPtr ↦ₛ remIdBytes) ∗
       ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
         (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗
         (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
       optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ u_40) ∗
       ((s.sp + 0x48#64) ↦₆₄ u_48) ∗ ((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗ ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗ ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
          newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧ newAliceBasePtr ≠ 0#64 ∧
          sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
              (locIdPtr ↦ₛ locIdBytes) ∗
            ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
              (remIdPtr ↦ₛ remIdBytes) ∗
            ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
              (rootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗
              (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
            optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
            optSenderChainHeap A (some sg') (some sc) ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
            ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
            A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗
            A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
            A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
            A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
            ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
            ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗
            ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
              ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
              ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
              ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
              ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
              ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 1#64 ∧
          s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x23 = newAliceBasePtr ∧
          s1.readReg64 .x24 = 33#64 ∧ s1.readReg64 .x25 = 8#64 ∧ s1.readReg64 .x26 = 0#64 ∧
          s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = 32#64 ∧
            s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  intro R hm hL
  rw [stackAt_chainClone_eq_alloc s.sp] at hm
  have hsub1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub1_ok_trap img b C abs hA s0 s coroPtr
    locIdPtr remIdPtr rootKeyPtr u_50 u_98 u_d0 u_7c
    locIdBytes remIdBytes rootKeyBytes hloc_len hrem_len hroot_len
    hF hsym hpc hrun hsp_align htr hx19
  let F1 : SepProp :=
    memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
    ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
    ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
    ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗ optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
    ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
      ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
    ((s.sp + 0x30#64) ↦₃₂ u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
    ((s.sp + 0x38#64) ↦₆₄ u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ u_40) ∗ ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
    ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
    ((s.sp + 0x68#64) ↦₆₄ u_68) ∗ ((s.sp + 0x70#64) ↦₆₄ u_70) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
    ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
    ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
    ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
    ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
    ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988)
  have hm1 : s.mem ⊨
      (A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
         (locIdPtr ↦ₛ locIdBytes) ∗
       ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
         (remIdPtr ↦ₛ remIdBytes) ∗
       ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
         (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
       ((s.sp + 0x50#64) ↦₆₄ u_50) ∗ ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0)) ∗ (F1 ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F1]; ac_rfl)) hm
  obtain ⟨sm, hsteps1,
      ⟨hpcm, hrunm, P_m, hmm,
        ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, hnew1, hnew2, hnew3,
          hent1, hspm, htrm, hFm, hsymm, hx19m, hx22m, hx23m, hx24m, hx25m, hx27m, hx29m⟩⟩ |
      ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ := hsub1 (F1 ∗ R) hm1 hL
  · have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm]; exact hsp_align
    have hx22m' : sm.readReg64 .x22 = sm.sp + 0x930#64 := by rw [hx22m, hspm]
    have hx27m' : sm.readReg64 .x27 = sm.sp + 0x370#64 := by rw [hx27m, hx27, hspm]
    have hsub2 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub2_ok_trap img b C abs hA s0 sm coroPtr
      newLocIdPtr newRemIdPtr aliceBasePtr ctxPtr
      u_38 u_40 u_48 u_60 u_68 u_70
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
      prevCounter f248 f24c u_30 u_34 u_5c sg sc aliceBaseBytes halice_len
      hFm hsymm hpcm hrunm hspm_align htrm hx19m hx22m' hx23m hx24m hx25m hx27m'
    let F2 : SepProp :=
      ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
        (locIdPtr ↦ₛ locIdBytes) ∗
      ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
        (remIdPtr ↦ₛ remIdBytes) ∗
      ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
        (rootKeyPtr ↦ₛ rootKeyBytes) ∗
      ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗
      A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗
      A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
      ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗
        ((s.sp + 0xd0#64) ↦₆₄ 33#64)
    have hmm2 : sm.mem ⊨
        (A.pool ∗ stackAt sm.sp chainCloneStack ∗
         optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
         memRegion (sm.sp + 0x3e0#64) 104 ∗
         ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
         ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
         ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
         ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
           ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
           ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
         ((sm.sp + 0x30#64) ↦₃₂ u_30) ∗ ((sm.sp + 0x34#64) ↦₃₂ u_34) ∗
         ((sm.sp + 0x38#64) ↦₆₄ u_38) ∗ ((sm.sp + 0x40#64) ↦₆₄ u_40) ∗
           ((sm.sp + 0x48#64) ↦₆₄ u_48) ∗
         ((sm.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((sm.sp + 0x60#64) ↦₆₄ u_60) ∗
         ((sm.sp + 0x68#64) ↦₆₄ u_68) ∗ ((sm.sp + 0x70#64) ↦₆₄ u_70) ∗
         ((sm.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((sm.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sm.sp + 0x930#64) ↦₆₄ u930) ∗ ((sm.sp + 0x938#64) ↦₆₄ u938) ∗
         ((sm.sp + 0x940#64) ↦₆₄ u940) ∗ ((sm.sp + 0x948#64) ↦₆₄ u948) ∗
         ((sm.sp + 0x950#64) ↦₆₄ u950) ∗ ((sm.sp + 0x958#64) ↦₆₄ u958) ∗
         ((sm.sp + 0x960#64) ↦₆₄ u960) ∗ ((sm.sp + 0x968#64) ↦₆₄ u968) ∗
         ((sm.sp + 0x970#64) ↦₆₄ u970) ∗ ((sm.sp + 0x978#64) ↦₆₄ u978) ∗
         ((sm.sp + 0x980#64) ↦₆₄ u980) ∗ ((sm.sp + 0x988#64) ↦₆₄ u988)) ∗ (F2 ∗ R) := by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left hent1) ?_) hmm
      rw [hspm, stackAt_chainClone_eq_alloc s.sp]
      dsimp only [F1, F2]
      exact Entails.of_eq (by ac_rfl)
    obtain ⟨sf, hsteps2,
        ⟨hpcsf, hrunsf, P_sf, hmsf,
          ⟨sg', c0, sq0, sq1, sq2, sq3, sq4, sq5, newAliceBasePtr,
            hsrk', hpriv', hsc_inl, hnew4, hent2,
            hspsf, htrsf, hFsf, hsymsf,
            hx19sf, hx21sf, hx22sf, hx23sf, hx24sf, hx25sf, hx26sf, hx27sf, hx28sf, hx29sf⟩⟩ |
        ⟨hpansf, P_sf, hmsf, hpansfm⟩ | ⟨_, hoomsf⟩⟩ :=
      hsub2 (F2 ∗ R) hmm2 (hsteps1.codeLoaded hL)
    · rw [← sepConj_assoc] at hmsf
      refine ⟨sf, hsteps1.trans hsteps2, Or.inl ⟨hpcsf, hrunsf, P_sf ∗ F2, hmsf, ?_⟩⟩
      refine ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr,
        sg', c0, sq0, sq1, sq2, sq3, sq4, sq5,
        hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, ?_,
        hspsf.trans hspm, htrsf, hFsf, hsymsf,
        hx19sf, hx21sf, hx22sf, hx23sf, hx24sf, hx25sf, hx26sf, hx27sf, hx28sf,
        hx29sf.trans hx29m⟩
      refine Entails.trans (sepConj_mono_left hent2) ?_
      rw [hspm]
      dsimp only [F2]
      exact Entails.of_eq (by ac_rfl)
    · rw [← sepConj_assoc] at hmsf
      exact ⟨sf, hsteps1.trans hsteps2, Or.inr (Or.inl ⟨hpansf, P_sf ∗ F2, hmsf, fun R' hmR' => by
        rw [sepConj_assoc] at hmR'
        have h1 := hpansfm (F2 ∗ R') hmR'
        rw [← sepConj_assoc] at h1
        exact allowPanic_frame id h1⟩)⟩
    · exact (not_satisfies_false_sepConj hoomsf).elim
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps1, Or.inr (Or.inl ⟨hpan, P_m ∗ F1, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F1 ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Combined Stage P3 Clone (`+0x1778 -> +0x1bac`): Composes `stageP3_sub1_ok` (`+0x1778 -> +0x195c`) and `stageP3_sub2_ok` (`+0x195c -> +0x1bac`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
    u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32)
    (sg : SenderChainGhost) (sc : SenderChain)
    (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List (BitVec 8))
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (hroot_len : rootKeyBytes.length = 32) (halice_len : aliceBaseBytes.length = 33)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
       ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
         (locIdPtr ↦ₛ locIdBytes) ∗
       ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
         (remIdPtr ↦ₛ remIdBytes) ∗
       ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
         (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗
         (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
       optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗ ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗ ((s.sp + 0x40#64) ↦₆₄ u_40) ∗
       ((s.sp + 0x48#64) ↦₆₄ u_48) ∗ ((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗ ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗ ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
          newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧ newAliceBasePtr ≠ 0#64 ∧
          sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗
              (locIdPtr ↦ₛ locIdBytes) ∗
            ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗
              (remIdPtr ↦ₛ remIdBytes) ∗
            ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗
              (rootKeyPtr ↦ₛ rootKeyBytes) ∗
            ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗
              (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗
            optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
            optSenderChainHeap A (some sg') (some sc) ∗
            ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
            ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
            A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗
            A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
            A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
            A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗
            ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
            ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
            ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
            ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗
            ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
              ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
              ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
              ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
              ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
              ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 1#64 ∧
          s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x23 = newAliceBasePtr ∧
          s1.readReg64 .x24 = 33#64 ∧ s1.readReg64 .x25 = 8#64 ∧ s1.readReg64 .x26 = 0#64 ∧
          s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = 32#64 ∧
            s1.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap img b C abs hA
      s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
      u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
      prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc
      locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
      hloc_len hrem_len hroot_len halice_len
      hF hsym hpc hrun hsp_align htr hx19 hx27)

end CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

end
