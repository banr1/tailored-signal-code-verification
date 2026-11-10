/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks2
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# General-`prevCap` Stage P3 Duplicate-Message Error Exit and Epilogue Helpers

Proves the general-`prevSessionsEmptyAt` common error epilogue (`dropSessionStructure3 → x30`) and
duplicate-message error path (`+0x1cd8 → x30` when `errs.len = 0`), plus `Steps`-threading
combinators used by `Matched.M3PrevCap`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bind_sepWP_frame_steps {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem bind_sepWPp_genPanic_steps {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {P P_stage F : SepProp} {Q_mid : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hsteps hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hoom (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

private theorem mul24_eq_m3err {prevCap : BitVec 64} (_h : prevCap.toNat * 24 < 2 ^ 63) :
    24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
  constructor <;> bv_omega

private theorem p2_err_tail_prev_dealloc_ext_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : GenP3.AllocContractsMem4K b A ext)
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hdealloc := hA.dealloc_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  obtain ⟨hmul1, hmul2⟩ := mul24_eq_m3err hcap_lt
  closure_fetches_range_cli b (Rust.withPanics ext) 0x359c 0x35a0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35d0 0x362c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [BitVec.add_zero]; sep_frame,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` common error epilogue (`dropSessionStructure3 → s0.readReg64 .x30`)
under `AllocContractsMem4K`. -/
theorem stageP3_err_tail_common_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : GenP3.AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr errTag w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hdropSs3 := GenP3.drop_session_structure3_of_dealloc_ext hA.dealloc
  have hpc_drop : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc, tripleRatchetProgAtExt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF hsym hdropSs3 hpc_drop hrun hsp_al hx30
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec])
    hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hF1 hsym1 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1_s => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (P₂ := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj, sepConj_emp]
    have hstep2 := p3_err_tail_b_ext_wp b ext s1 coroPtr outPtr errTag g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hFf hsymf hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregs_f⟩
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hFf, hsymf, hvregs_f.trans hvregs_cs1⟩
  · simp only [hcap, ↓reduceIte]
    have hstack_alloc :
        stackAt s.sp dropSessionStructure2Stack =
          memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
      stackAt_split_bottom s.sp allocHookStack 96 (by decide)
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
    have hstep2 := p2_err_tail_prev_dealloc_ext_4k_wp b ext hA s1 coroPtr outPtr errTag
      g.prevCap g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hFf hsymf hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
    exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hFf, hsymf, hvregs_f.trans hvregs_cs1⟩

/-- General-`prevCap` common error epilogue (`dropSessionStructure3 → s0.readReg64 .x30`):
drops `sessionStateAt A (coroPtr + 0xf8#64) recG recSt` and `prevSessionsEmptyAt A coroPtr g`
into `memRegion (coroPtr + 0xe0#64) 368` (handling both `g.prevCap = 0` and `g.prevCap ≠ 0`). -/
theorem stageP3_err_tail_common_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr errTag w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_err_tail_common_prevEmpty_ext_4k_ok img b ext
    (GenP3.AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr errTag w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hF hsym hpc hrun hsp_align htr hx0 hx19 hx22 hx25 hx26 hx28 hx30

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` duplicate-error tail (`+0x34dc#64 → s0.readReg64 .x30` when `errs.len = 0`)
under `AllocContractsMem4K`. -/
theorem stageP3_err_tail_dup_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : GenP3.AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep1 := p3_err_tail_dup_a_ext_wp b ext s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c
    (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _,
    hx30_1, hvregs_1⟩
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hsp1_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_ext_4k_ok img b ext hA
    s0 s1 coroPtr outPtr 0x8000000000000017#64
    w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hF1 hsym1 hpc1 hrun1 hsp1_align (htr1_s.trans htr)
    hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hFf, hsymf, hvregs_f.trans hvregs_1⟩

/-- General-`prevCap` duplicate-error tail (`+0x34dc#64 → s0.readReg64 .x30` when `errs.len = 0`). -/
theorem stageP3_err_tail_dup_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_err_tail_dup_prevEmpty_ext_4k_ok img b ext
    (GenP3.AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr errsPtr w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` Substage P3.5 duplicate-message error path (`+0x1cd8#64 → s0.readReg64 .x30`)
under `AllocContractsMem4K`. -/
theorem stageP3_sub5_err_dup_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : GenP3.AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hdecomp :
      vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64,
          words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
            speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64)
      (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (P₂ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  have hstep1 := p3_err_dup_ext_wp b ext s coroPtr outPtr hpc hrun hsp_align hx19 hx24
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1,
    hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSs3 := GenP3.drop_session_structure3_of_dealloc_ext hA.dealloc
  have hpc1_drop : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc1, tripleRatchetProgAtExt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗
      stackAt s.sp dropSessionStructure2Stack)
    hF1 hsym1 hdropSs3 hpc1_drop hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp1_s])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000017#64 := hx28_cs2.trans hx28_1
  have htail := stageP3_err_tail_dup_prevEmpty_ext_4k_ok img b ext hA
    s0 s2 coroPtr outPtr errsPtr w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hF2 hsym2 hpc2 hrun2 hsp2_align (htr2_1.trans (htr1_s.trans htr))
    hx19_2 hx24_2 hx25_2 hx26_2 hx28_2
  rw [hsp2_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  have hrec : words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) :=
    hreassemble outPtr
  exact ⟨entails_replace_sub hrec (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hFf, hsymf, by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩

/-- General-`prevCap` Substage P3.5 duplicate-message error path (`+0x1cd8#64 → s0.readReg64 .x30`). -/
theorem stageP3_sub5_err_dup_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_sub5_err_dup_prevEmpty_ext_4k_ok img b ext
    (GenP3.AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr errsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
