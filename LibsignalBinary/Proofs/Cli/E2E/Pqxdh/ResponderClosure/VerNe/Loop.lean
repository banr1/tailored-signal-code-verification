/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErr
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMoves
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeel
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopSegs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# One-Element `previous_sessions` Loop Composition

Proves `overPrevLoop_cli_of_dec_ext` (`+0x1e78 → +0x2cfc` on `tripleRatchetProgAtExt`) by composing
the loop head (`+0x1e78 → +0x1ee8`), inlined `SessionStructure::decode` (`+0x1ee8 → +0x2620`),
inline `prostSSGQAt` peel, five-step `memcpy` chain (`+0x2620 → +0x1fd4`), and version-mismatch
skip tail (`+0x1fd4 → +0x2cfc`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Framing and scratch repacking helpers -/

private theorem bind_sepWPp_frame_loop {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (P3P4.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stackAt_sub_eq_loop (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

private theorem prevVecAt_open_eq_loop (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
      overPrevElemAt A prevCap prevPtr enc := by
  rw [prevVecAt_one_eq_elemAt A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap, hdrP_coro_eq]
  ac_rfl

private theorem loopScratch_to_decPre (sp : BitVec 64) :
    memRegion (sp + 0x538#64) 1016 ∗
    memRegion (sp + 0x930#64) 48 ∗
    memRegion (sp + 0x960#64) 48 ∗
    memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 344 ∗
    memRegion (sp + 0xbe8#64) 136 =
      memRegion (sp + 0x538#64) 40 ∗
      memRegion (sp + 0x560#64) 320 ∗
      memRegion (sp + 0x6a0#64) 320 ∗
      memRegion (sp + 0x7e0#64) 320 ∗
      overDecScratchPre sp := by
  have h538 :
      memRegion (sp + 0x538#64) 1016 =
        memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
        memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
        memRegion (sp + 0x920#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x538#64) (n := 40) (k := 976) (b' := sp + 0x560#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x560#64) (n := 320) (k := 656) (b' := sp + 0x6a0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x6a0#64) (n := 320) (k := 336) (b' := sp + 0x7e0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x7e0#64) (n := 320) (k := 16) (b' := sp + 0x920#64)
          rfl (by bv_omega) (by decide)]
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48 ∗
        memRegion (sp + 0x990#64) 248 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 48) (k := 296) (b' := sp + 0x960#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 48) (k := 248) (b' := sp + 0x990#64)
          rfl (by bv_omega) (by decide)]
  unfold overDecScratchPre
  rw [h538, h990, h930]
  ac_rfl

private theorem decScratchPost_join_930 (sp : BitVec 64) :
    overDecScratchPost sp ∗ memRegion (sp + 0x930#64) 344 = overDecScratchPre sp := by
  unfold overDecScratchPost overDecScratchPre
  ac_rfl

private theorem mem920_16_split_loop (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 16 =
      ∃∗ u920 : BitVec 64, ((sp + 0x920#64) ↦₆₄ u920) ∗ memRegion (sp + 0x928#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x920#64), sepExists_sepConj_left]

private theorem mem920_16_fold_loop (sp w : BitVec 64) :
    ((sp + 0x920#64) ↦₆₄ w) ∗ memRegion (sp + 0x928#64) 8 ⊢ memRegion (sp + 0x920#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

/-! ## Part 1 (`+0x1e78 → +0x2620`): loop head and `SessionStructure::decode` -/

set_option maxHeartbeats 800000 in
private theorem overPrevLoop_part1_cli_ok {A : RustAlloc} {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGenExt A trackVRegs)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s : State) (coroPtr prevCap prevPtr wd0 u3e0 : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (hcap : prevCap ≠ 0#64)
    (henc : enc = CryptoVerification.E2E.Record.encSession sess)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hpp : sess.pendingPreKey = none)
    (hkpk : sess.pendingKyberPreKey = none)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_le : overDecStackX ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
      (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       memRegion (s.sp + 0x538#64) 1016 ∗
       memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗
       memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       memRegion (s.sp + 0xbe8#64) 136 ∗
       A.pool ∗
       stackAt s.sp overDecStackX)
      (fun s2 P_f =>
        (P_f ⊢
          prostSSGQAt A (s.sp + 0x930#64) (ssgqOf sess) ∗
          overDecScratchPost s.sp ∗
          memRegion (s.sp + 0x538#64) 40 ∗
          memRegion (s.sp + 0x560#64) 320 ∗
          memRegion (s.sp + 0x6a0#64) 320 ∗
          memRegion (s.sp + 0x7e0#64) 320 ∗
          prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          A.pool ∗
          stackAt s.sp overDecStackX ∗
          anyHeap) ∧
        s2.sp = s.sp ∧
        s2.trace = s0.trace ∧
        s2.readReg64 .x19 = coroPtr ∧
        s2.readReg64 .x21 = s.sp + 0x930#64 ∧
        s2.readReg64 .x27 = prevPtr ∧
        s2.readReg64 .x29 = s.sp + 0xc70#64 ∧
        optVRegsEq trackVRegs s2 s ∧
        img.FrozenLoaded s2 ∧
        s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (prevVecAt_open_eq_loop A coroPtr prevCap prevPtr enc hcap))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (loopScratch_to_decPre s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym
    (overPrevLoop_head_cli_wp img ext s coroPtr prevCap prevPtr u3e0 wd0 hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1
      ⟨hsp1, htr1, hx19_1, _, hx21_1, hx24_1, hx25_1, _, hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have hsp1_le : overDecStackX ≤ s1.sp.toNat := by rw [hsp1]; exact hsp_le
  have htr1_0 : s1.trace = s0.trace := htr1.trans htr
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x930#64 := by rw [hx21_1, hsp1]
  have hx29_1' : s1.readReg64 .x29 = s1.sp + 0xc70#64 := by rw [hx29_1, hx29, hsp1]
  have hdec := hDec img ext himg (allocContractsX_of_mem4k hA)
    s0 s1 prevCap prevPtr enc sess henc hQ hver4 hpp hkpk hF1 hsym1 hpc1 hrun1
    hsp1_align hsp1_le htr1_0 hx21_1' hx24_1 hx25_1 hx27_1 hx29_1'
  rw [hsp1] at hdec
  refine bind_sepWPp_frame_loop hdec (by sep_focus)
    fun s2 hpc2 hrun2
      ⟨hsp2_1, htr2, hx19_2, _, hx21_2, _, _, hx27_2, hx29_2, hopt_2_1, hF2, hsym2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (prevVecAt_open_eq_loop A coroPtr prevCap prevPtr enc hcap).symm)
    (by sep_focus) ?_
  have hopt_2_s : optVRegsEq trackVRegs s2 s :=
    optVRegsEq_trans (optVRegsEq_of_vregs_eq trackVRegs hvregs1) hopt_2_1
  refine SepWPp.done hpc2 hrun2
    ⟨Entails.of_eq (by ac_rfl),
     hsp2_1, htr2, hx19_2.trans hx19_1, hx21_2, hx27_2,
     hx29_2.trans (hx29_1.trans hx29), hopt_2_s, hF2, hsym2⟩

/-! ## Part 2 (`+0x2620 → +0x2cfc`): peel, `memcpy` chain, and version-skip tail -/

set_option maxHeartbeats 800000 in
private theorem overPrevLoop_part2_cli_ok {A : RustAlloc}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s2 : State) (coroPtr prevPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (sess : Session (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hkpk : sess.pendingKyberPreKey = none)
    (hF2 : img.FrozenLoaded s2) (hsym2 : s2.symtab = img.symtab)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64)
    (hrun2 : s2.status = .Running)
    (hs2_sp : s2.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr2 : s2.trace = s0.trace)
    (hx19_2 : s2.readReg64 .x19 = coroPtr)
    (hx21_2 : s2.readReg64 .x21 = s.sp + 0x930#64)
    (hx27_2 : s2.readReg64 .x27 = prevPtr)
    (hx29_2 : s2.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64) s2
      (prostSSGQAt A (s.sp + 0x930#64) (ssgqOf sess) ∗
       overDecScratchPost s.sp ∗
       memRegion (s.sp + 0x538#64) 40 ∗
       memRegion (s.sp + 0x560#64) 320 ∗
       memRegion (s.sp + 0x6a0#64) 320 ∗
       memRegion (s.sp + 0x7e0#64) 320 ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       memRegion (errsPtr + 48#64) 144 ∗
       logOff img ∗
       A.pool ∗
       stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗
          memRegion (s.sp + 0x538#64) 1016 ∗
          memRegion (s.sp + 0x930#64) 48 ∗
          memRegion (s.sp + 0x960#64) 48 ∗
          memRegion (s.sp + 0x990#64) 256 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0xbe8#64) 136 ∗
          logOff img ∗
          A.pool ∗
          stackAt s.sp overDecStackX) ∧
        sf.sp = s.sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s2 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  dsimp only [overDecScratchPost]
  refine P3P4.SepWPp.weaken_frame (overPrevPeel_ok_ext A sess hQ hver4 hkpk (s.sp + 0x930#64))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.pure_elim fun ⟨hw0, hr1, hr2, hdropFromMoves⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (mem920_16_split_loop s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u920 => ?_
  have hstk_alloc := stackAt_sub_eq_loop s.sp overDecStackX allocHookStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x930#64 := by rw [hx21_2, hs2_sp]
  have hmv := overPrevMoves_cli_4k_ok img ext hA s2 w0 w1 w2 u920 r1 r2
    hw0 hr1 hr2 hpc2 hrun2 hsp2_align hx21_2'
  rw [hs2_sp] at hmv
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hmv (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3
      ⟨hsp3_2, htr3_2, hx8_3, hx19_3, _, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (mem920_16_fold_loop s.sp (s2.readReg64 .x26)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hdropFromMoves (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun G => SepWPp.exists_elim fun st => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hstk_grow := stackAt_sub_eq_loop s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
  have hx19_3' : s3.readReg64 .x19 = coroPtr := hx19_3.trans hx19_2
  have hx27_3' : s3.readReg64 .x27 = prevPtr := hx27_3.trans hx27_2
  have hx29_3' : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_3.trans hx29_2
  have herr := overPrevErr_cli_4k_ok (A := A) img ext himg hA s0 s3 prevPtr errsPtr msgVer G st
    hver_ne hF3 hsym3 hpc3 hrun3 hsp3_align htr3 hx8_3 hx27_3'
  rw [hsp3] at herr
  refine bind_sepWPp_frame_loop herr (by sep_focus)
    fun sf hpcf hrunf ⟨hspf_3, htrf, hx19_f, _, hx29_f, hvregsf, hFf, hsymf⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  have hfold_post :
      memRegion (s.sp + 0x920#64) 16 ∗ memRegion (s.sp + 0xa88#64) 8 ∗
      memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
      memRegion (s.sp + 0x930#64) 344 = overDecScratchPre s.sp := by
    simpa only [overDecScratchPost, sepConj_assoc] using decScratchPost_join_930 s.sp
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hfold_post) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (loopScratch_to_decPre s.sp).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl),
     hspf_3, htrf, hx19_f.trans hx19_3', hx29_f.trans hx29_3',
     hvregsf.trans hvregs3, hFf, hsymf⟩

/-! ## Full loop theorems -/

set_option maxHeartbeats 600000 in
/-- Composes `OverPrevLoopCliStmtGenExt A trackVRegs` (`+0x1e78 → +0x2cfc`) from `OverPrevDecodeCliStmtGenExt`. -/
theorem overPrevLoop_cli_of_dec_ext {A : RustAlloc} {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGenExt A trackVRegs) :
    OverPrevLoopCliStmtGenExt A trackVRegs := by
  intro img ext himg hA s0 s coroPtr prevCap prevPtr errsPtr wd0 u3e0 msgVer enc
    hcap hver_ne hEnc hF hsym hpc hrun hsp_align hsp_le htr hx19 hx29
  obtain ⟨sess, henc, hQ, hver4, hpp, hkpk⟩ := hEnc
  have hpart1 := overPrevLoop_part1_cli_ok hDec img ext himg hA
    s0 s coroPtr prevCap prevPtr wd0 u3e0 enc sess
    hcap henc hQ hver4 hpp hkpk hF hsym hpc hrun hsp_align hsp_le htr hx19 hx29
  refine bind_sepWPp_frame_loop hpart1 (by sep_focus)
    fun s2 hpc2 hrun2
      ⟨hs2_sp, htr2, hx19_2, hx21_2, hx27_2, hx29_2, hopt2, hF2, hsym2⟩ => ?_
  have hpart2 := overPrevLoop_part2_cli_ok img ext himg hA
    s0 s s2 coroPtr prevPtr errsPtr msgVer sess
    hver_ne hQ hver4 hkpk hF2 hsym2 hpc2 hrun2 hs2_sp hsp_align htr2
    hx19_2 hx21_2 hx27_2 hx29_2
  refine bind_sepWPp_frame_loop hpart2 (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hx19f, hx29f, hvregsf, hFf, hsymf⟩ => ?_
  have hoptf : optVRegsEq trackVRegs sf s :=
    optVRegsEq_trans hopt2 (optVRegsEq_of_vregs_eq trackVRegs hvregsf)
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    hspf, htrf, hx19f, hx29f, hoptf, hFf, hsymf⟩

theorem overPrevLoop_cli_of_dec {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGen trackVRegs) :
    OverPrevLoopCliStmtGen trackVRegs :=
  fun img ext himg hA => overPrevLoop_cli_of_dec_ext hDec img ext himg (.of_AllocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
