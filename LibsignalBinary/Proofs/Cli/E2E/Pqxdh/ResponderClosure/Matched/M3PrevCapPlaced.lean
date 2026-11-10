/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCap
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Relocatable Stage P3 over General `prevSessionsEmptyAt`

Relocatable `[LibsignalPlacement]` and `[LibsignalFullPlacement]` counterparts of `Matched.M3PrevCap`
on Block `518` (`lsProg_518 ext`, `(blkPl_518).base = lsmpl.base 518`).
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

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

abbrev dpClosureEntryM3Placed [LibsignalPlacement] : BitVec 64 := (blkPl_518).base

/-- `dpClosureEntryM3Placed + 0x1cd4 → lsmpl.base 508` (`poll_tryDecrypt`) under
`[LibsignalPlacement]`. -/
theorem p3_bl_tryDecrypt_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd4#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_518 ext) (lsmpl.base 508) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧
        s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x1cd8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev LsTokenInitM3 [LibsignalPlacement] : SepProp :=
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt

/-- Relocatable `[LibsignalPlacement]` `stageP3DispatchPrePrevEmpty` at
`dpClosureEntryM3Placed + 0x1cd8#64`. -/
def stageP3DispatchPrePrevEmptyPlaced [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A (s.sp + 0x270#64) res ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Relocatable `[LibsignalPlacement]` `stageP3DispatchOkMidPrevEmpty` at
`dpClosureEntryM3Placed + 0x34dc#64` (`Ok pt`). -/
def stageP3DispatchOkMidPrevEmptyPlaced [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr ptCap ptPtr : BitVec 64) (g : RecordGhost)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
  prevSessionsEmptyAt A coroPtr g ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

def genP3S5PostFramePlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) : SepProp :=
  LsTokenInitM3 ∗
    ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
    ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
    ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
    protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗
    coinsPost ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
    genP3S5SpillRem sp

theorem postTryDecrypt_entails_s5DispatchPrevEmpty_placed [LibsignalPlacement] {A : RustAlloc}
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (g : RecordGhost) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) :
    (LsTokenInitM3 ∗
      sessionStateAt A (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A (s.sp + 0x270#64) res ∗
      protocolAddressAt A rem remAddrPtr ∗
      protocolAddressAt A loc locAddrPtr ∗
      signalMessageAt A msgG whisperMsgPtr msg ∗
      coinsPost ∗
      FromRecordCallees.lsLogOff ∗
      stackAt s.sp rootStack ∗
      A.pool) ∗
    (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0) ⊢
    stageP3DispatchPrePrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr g
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost := by
  unfold stageP3Sub5ExtraPrePrevEmpty stageP3DispatchPrePrevEmptyPlaced genP3S5PostFramePlaced
  rw [stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp)
    (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

private theorem bind_sepWP_lscro_steps_m3_placed [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun (hcro.of_keepsFrozen hsteps.keepsFrozen)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem sepWPp_frame_closOom_m3_placed {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F_frame : SepProp} {Q : State → SepProp → Prop}
    (hwp : SepWPp prog ret s P (fun sf P_f => Q sf (P_f ∗ F_frame)) (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s (P ∗ F_frame) Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | ⟨hpan, P_f, hmf, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hwp (F_frame ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf; exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f ∗ F_frame, hmf, hQ⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F_frame, hmf, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hoom (F_frame ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem bind_sepWPp_genPanic_steps_framed_m3_placed {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {P P_stage F F_frame : SepProp} {Q_mid Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (P3P4.PanicOomProp s0)) (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm ((P_m ∗ F) ∗ F_frame) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp prog ret s (P ∗ F_frame) Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hm0 : s.mem ⊨ P_stage ∗ ((F ∗ F_frame) ∗ R) := by
    rw [hP] at hm; simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F ∗ F_frame) ∗ R) hm0 hL
  · have hmm' : sm.mem ⊨ ((P_m ∗ F) ∗ F_frame) ∗ R := by simpa only [sepConj_assoc] using hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hsteps hpcm hrunm hqm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ (F ∗ F_frame), hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hoom ((F ∗ F_frame) ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `dpClosureEntryM3Placed + 0x1dfc → +0x34dc` under `[LibsignalPlacement]`. -/
theorem p3_seg7b_x24_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1dfc#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `dpClosureEntryM3Placed + 0x1cd8 → lsmpl.base 48` (`set_session_state`) under
`[LibsignalPlacement]`. -/
theorem p3_seg7a_x24_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s : State) (coroPtr retPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 48) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ FromRecordCallees.lsLogOff ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ FromRecordCallees.lsLogOff ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x1dfc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed, FromRecordCallees.lsLogOff, lsLogFilterAddr, lsMemcpySym] at hmemcpy hpc ⊢
  rw [← hss_len]
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm]⟩

private theorem call_lscl_nopanic_m3 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

/-- Relocatable `[LibsignalPlacement]` Substage P3.5 `Ok` core
(`dpClosureEntryM3Placed + 0x1cd8 → +0x34dc`). -/
theorem stageP3_sub5_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hSetState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A)))
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ FromRecordCallees.lsLogOff ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ FromRecordCallees.lsLogOff ∗
          sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ A.pool ∗ stackAt s.sp setSessionStateStack) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  rw [RawByteMove.sessionStateAt_eq_inline_sep_heap A (s.sp + 0xa90#64) G₂ st₂]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs.length = 344 ∧ RawByteMove.SessionInline G₂ st₂ bs⌝)
    (P₂ := ⌜bs.length = 344 ∧ RawByteMove.SessionInline G₂ st₂ bs⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hbs_len, hinl⟩ => ?_
  have hstep1 := p3_seg7a_x24_placed_wp ext hmemcpy s coroPtr retPtr bs hbs_len hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_steps_m3_placed hcro hstep1 (by sep_focus) fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine call_lscl_nopanic_m3
    (x := (⟨coroPtr + 0xe0#64, s.sp + 0x3e0#64, some (recG, recSt), bs⟩ : SetSessionStateGhost))
    (T := sessionStateAt A (coroPtr + 0xe0#64 + 0x18#64) recG recSt ∗
          ((s.sp + 0x3e0#64) ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
    hcro1 hSetState hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [setSessionStateSpec]; rw [hsp1_s]) (And.intro hx0_1 (And.intro hx1_1 hbs_len))
    (by have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
        rw [h18]; sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [setSessionStateSpec]; rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
  rw [h18]
  refine P3P4.SepWPp.weaken_frame
    (RawByteMove.sessionStateAt_move_bytes_twice A (s.sp + 0xa90#64) (s.sp + 0x3e0#64) (coroPtr + 0xf8#64) G₂ st₂ hinl)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hstep3 := p3_seg7b_x24_placed_wp ext s2 coroPtr hpc2 hrun2 (hx19_cs2.trans hx19_1)
  refine bind_sepWP_lscro_steps_m3_placed hcro2 hstep3 (emp_sepConj _).symm fun sf _ hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_2, htrf_2, hx19_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf_2.trans hsp2_s, htrf_2.trans (htr2_1.trans (htr1_s.trans htr)), hcrof, hx19_f,
    hx24_f.trans (hx24_cs2.trans hx24_1), hx25_f.trans (hx25_cs2.trans hx25_1),
    hx26_f.trans (hx26_cs2.trans hx26_1), hx27_f.trans (hx27_cs2.trans hx27_1),
    hx28_f, hx29_f.trans (hx29_cs2.trans hx29_1), hvregs_f.trans (hvregs_cs2.trans hvregs_1)⟩

/-- Relocatable `[LibsignalPlacement]` Substage P3.5 `vecResultAt (.ok pt)`
(`dpClosureEntryM3Placed + 0x1cd8 → +0x34dc`). -/
theorem stageP3_sub5_decResult_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hSetState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A)))
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.ok pt) ∗ FromRecordCallees.lsLogOff ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ ptCap ptPtr : BitVec 64,
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            FromRecordCallees.lsLogOff ∗ sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool ∗ stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧ sf.trace = s0.trace ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (decResultAt_ok_unpack A (s.sp + 0x270#64) pt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ptCap => SepWPp.exists_elim fun ptPtr => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (P₂ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_ne⟩ => ?_
  have hsub := stageP3_sub5_placed_ok ext hmemcpy hSetState s0 s coroPtr retPtr G₂ recG st₂ recSt
    hcro hpc hrun hsp_align htr hx19
  refine P3P4.SepWPp.ret_sepWPp_frame hsub (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcrof, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩ => ?_
  exact ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcrof, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩

def genP3CallFramePlaced [LibsignalPlacement] (A : RustAlloc) (sp remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (rem loc : AddrGhost)
    (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  memRegion (sp + 0xa90#64) 344 ∗ ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (sp + 0x270#64) 48 ∗
    coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

def genP3PrePlaced [LibsignalPlacement] (A : RustAlloc) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x19 = coroPtr ∧ s.readReg64 .x27 = sp + 0x370#64 ∧ s.readReg64 .x29 = fp⌝ ∗
    sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ A.pool ∗ stackAt sp chainCloneStack ∗
    memRegion (sp + 0x3e0#64) 104 ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    genP3SpillAll sp

def genP3PostSpatialPlaced [LibsignalPlacement] (A : RustAlloc) (sp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
    (∃∗ G₁ : SessionGhost, ⌜CloneRel recG G₁⌝ ∗ sessionStateAt A (sp + 0xa90#64) G₁ st) ∗
    protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (sp + 0x270#64) 48 ∗
    coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool ∗
    memRegion (sp + 0x3e0#64) 104 ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll sp

def genP3PostEqPlaced [LibsignalPlacement] (A : RustAlloc) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x0 = sp + 0x270#64 ∧ s.readReg64 .x1 = sp + 0xa90#64 ∧
    s.readReg64 .x2 = remAddrPtr ∧ s.readReg64 .x3 = locAddrPtr ∧ s.readReg64 .x4 = whisperMsgPtr ∧
    s.readReg64 .x5 = 3#64 ∧ s.readReg64 .x6 = 0#64 ∧ s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧ s.readReg64 .x27 = ctxPtr ∧ s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatialPlaced A sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg

def genP3PostNePlaced [LibsignalPlacement] (A : RustAlloc) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  ⌜s.sp = sp ∧ s.readReg64 .x9 = msgVer.setWidth 64 ∧ s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧ s.readReg64 .x27 = ctxPtr ∧ s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatialPlaced A sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg

def genP3PostPlaced [LibsignalPlacement] (A : RustAlloc) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  if st.version = msgVer then
    genP3PostEqPlaced A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg s
  else
    genP3PostNePlaced A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg s

abbrev cloneExitPCPlaced [LibsignalPlacement] (st : SessionState (List (BitVec 8))) (msgVer : BitVec 32) : BitVec 64 :=
  if st.version = msgVer then dpClosureEntryM3Placed + 0x1cd4#64 else dpClosureEntryM3Placed + 0x1e04#64

def CloneGenVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec →
    subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec →
    ext lsHandleErrorSym = some Rust.panicked →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    ∀ (s0 s : State) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
        (genP3PrePlaced A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3PostPlaced A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

/-- Relocatable `[LibsignalPlacement]` CLI `tryDecryptPlacedSpec` weakened to `DistinctSid`
(matching `Poll.pollTryDecryptPlacedSpecP`). -/
def pollTryDecryptM3PlacedSpecP [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
      s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
      (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
        DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
      SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 48 ∗ CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
    FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool
  post := (_root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).post
  onPanic := (_root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).onPanic

/-- Relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecTPTight` (matching `Poll.pollTryDecryptPlacedSpecTPTight`). -/
def pollTryDecryptM3PlacedSpecTPTight [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { pollTryDecryptM3PlacedSpecP C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LsTokenInitM3 ∗
        (pollTryDecryptM3PlacedSpecP C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      LsTokenInitM3 ∗
        (pollTryDecryptM3PlacedSpecP C A ctl uuidParse S).post x s0 sf
    onPanic := _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S uuidParse }

private theorem stageP3_clone_prevEmpty_vregs_prefix_placed_steps [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    {A : RustAlloc} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (s0 s : State) (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (g : RecordGhost) (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢
        genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗ stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (LsTokenInitM3 ∗
        genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone ext hshim halloc hmemcpy hpanic hcc hscc s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp := LsTokenInitM3 ∗ stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame
  have hP :
      (LsTokenInitM3 ∗
        genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame) =
      genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hcro1
        (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
private theorem stageP3_call_tryDecrypt_placed_steps [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hroot : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))))
    (s0 s s1 : State) (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F : SepProp) (Q : State → SepProp → Prop)
    (hver : st.version = msgVer)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st) (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1cd4#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = s.sp + 0x270#64) (hx1_1 : s1.readReg64 .x1 = s.sp + 0xa90#64)
    (hx2_1 : s1.readReg64 .x2 = remAddrPtr) (hx3_1 : s1.readReg64 .x3 = locAddrPtr)
    (hx4_1 : s1.readReg64 .x4 = whisperMsgPtr) (hx5_1 : s1.readReg64 .x5 = 3#64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hCont : ∀ (s2 : State) (G' : SessionGhost),
      Steps (lsProg_518 ext) s1 s2 →
      (genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic →
      G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G' →
      s2.pc = dpClosureEntryM3Placed + 0x1cd8#64 → s2.status = .Running →
      s2.sp = s.sp → s2.trace = s0.trace → StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x24 = s.sp + 0x370#64 →
      s2.readReg64 .x27 = ctxPtr → calleeSavedVRegs s2 = calleeSavedVRegs s1 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s2
        ((LsTokenInitM3 ∗
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  have hbl := p3_bl_tryDecrypt_placed_wp ext s1 hpc1 hrun1
  refine bind_sepWP_lscro_steps_m3_placed hcro1 hbl (emp_sepConj _).symm
    fun sc hsteps_bl hpcc hrunc hcroc hregsc => ?_
  rw [emp_sepConj]
  rcases hregsc with ⟨hspc_1, htrc_1, hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c,
    hx19_c, hx24_c, hx27_c, _, hx30_c, hvregs_c⟩
  have hspc : sc.sp = s.sp := hspc_1.trans hs1_sp
  have hspc_al : sc.spAligned = true := by simpa only [State.spAligned, hspc] using hsp_align
  have htrc_0 : sc.trace = s0.trace := htrc_1.trans htr1
  let x : TryDecryptGhost := {
    G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
    msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest
  }
  intro R hm hL
  have hpre_c :
      sc.mem ⊨
        (withLsCodeLoaded lsmpl
          (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse
            (LibsignalSpqrV1.spqrV1 C.F K))).pre x sc ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.CoinsTape.cliTapeAt, x]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcroc.1, ?_⟩
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_lt, ?_⟩
    rw [← sepConj_assoc] at hm
    have hx5_byte : (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
      rw [hx5_c, hx5_1]; rfl
    have hp2 : (sc.readReg64 .x0 = s.sp + 0x270#64 ∧ sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
        sc.readReg64 .x2 = remAddrPtr ∧ sc.readReg64 .x3 = locAddrPtr ∧
        sc.readReg64 .x4 = whisperMsgPtr ∧ (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
        (st.remoteIdentity ≠ some st.localIdentity ∨
          DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
        SeedsLen32 st ∧ st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat) = True :=
      propext ⟨fun _ => trivial, fun _ =>
        ⟨hx0_c.trans hx0_1, hx1_c.trans hx1_1, hx2_c.trans hx2_1, hx3_c.trans hx3_1,
         hx4_c.trans hx4_1, hx5_byte, hnot_self, hseeds, hrc_lt, hsp_root⟩⟩
    rw [hp2, pure_true, emp_sepConj]
    simpa only [sepConj_assoc] using hm
  obtain ⟨s2, hsteps2,
      ⟨⟨hpc2_lr, hsp2_c, hrun2⟩, ⟨_, hcs2⟩, hm2⟩ | ⟨hpan, hm_pan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩⟩ :=
    hroot.to_outcome x (F ∗ R) sc hpcc hrunc hpre_c hspc_al hL
  · dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      CryptoVerification.Cli.CoinsTape.cliTapeAfter, TryDecryptGhost.model, x] at hm2
    rw [hspc] at hm2
    have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := hcroc.of_keepsFrozen hsteps2.keepsFrozen
    have hm2_pull :
        s2.mem ⊨
          ⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
          ((∃∗ G' : SessionGhost,
              ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
            LsTokenInitM3 ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) := by
      have heq :
          (LsTokenInitM3 ∗
            (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
              (∃∗ G' : SessionGhost,
                ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
              vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗
              coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
              FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool)) ∗ (F ∗ R) =
          ⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
          ((∃∗ G' : SessionGhost,
              ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
            LsTokenInitM3 ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) := by ac_rfl
      rwa [heq] at hm2
    rw [satisfies_pure_sepConj] at hm2_pull
    rcases hm2_pull with ⟨⟨hnpan, htr2_c⟩, hm2_ex⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_ex
    obtain ⟨G', hm2_G⟩ := hm2_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2_G
    obtain ⟨hdec_rel, hm2_rest⟩ := hm2_G
    have hm2_cont :
        s2.mem ⊨
          ((LsTokenInitM3 ∗
            sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F) ∗ R := by
      have heq2 :
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          (LsTokenInitM3 ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) =
          ((LsTokenInitM3 ∗
            sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F) ∗ R := by ac_rfl
      rwa [heq2] at hm2_rest
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    obtain ⟨sf, hsteps3, hout3⟩ :=
      hCont s2 G' (hsteps_bl.trans hsteps2) hnpan hdec_rel (hpc2_lr.trans hx30_c) hrun2
        (hsp2_c.trans hspc) (htr2_c.trans htrc_0) hcro2
        (hx19_cs2.trans (hx19_c.trans hx19_1)) (hx24_cs2.trans (hx24_c.trans hx24_1))
        (hx27_cs2.trans (hx27_c.trans hx27_1)) (hvregs_cs2.trans hvregs_c)
        R hm2_cont (hsteps2.codeLoaded hL)
    exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight,
      _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
      _root_.CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
      TryDecryptGhost.model, x] at hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pan
    rcases hm_pan with ⟨⟨hpan_or, hpref_c⟩, hm_any⟩
    have hpref_0 : s0.trace <+: s2.trace := htrc_0 ▸ hpref_c
    have hm_any_R : s2.mem ⊨ anyHeap ∗ R := by
      rw [← sepConj_assoc] at hm_any
      exact Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_any
    rcases hpan_or with hmod_pan | hoom_pan
    · refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
        ⌜st.version = msgVer ∧ (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
            s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, Or.inr (fun _ h => h)⟩)⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hver, hmod_pan, hpref_0⟩, hm_any_R⟩
    · have hoom_0 : allocFailedIn s0 s2 := by unfold allocFailedIn at hoom_pan ⊢; rwa [← htrc_0]
      refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
        ⌜allocFailedIn s0 s2 ∧ s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, Or.inl (fun _ h => h)⟩)⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hoom_0, hpref_0⟩, hm_any_R⟩
  · exact (not_satisfies_false_sepConj hexit).elim
  · exact (not_satisfies_false_sepConj hoom).elim

def stageP3ErrPrePrevEmptyM3Placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
  stackAt s.sp growOneSpeStack

/-- Relocatable `[LibsignalPlacement]` Substage P3.5 error path (`dpClosureEntryM3Placed + 0x1cd8 → s0.readReg64 .x30`)
for `Matched/M3PrevErrBPlaced`. -/
def StageP3Sub5ErrPrevEmptyPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64),
      initErrsPtr ≠ 0#64 →
      ∀ (e : SignalProtocolError), e ≠ .panic →
      ∀ (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost)
        (st₂ recSt : SessionState (List (BitVec 8))),
        StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        s.pc = dpClosureEntryM3Placed + 0x1cd8#64 →
        s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true →
        s.trace = s0.trace →
        s.readReg64 .x19 = coroPtr →
        s.readReg64 .x24 = s.sp + 0x370#64 →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
          (stageP3ErrPrePrevEmptyM3Placed A s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
          (fun sf P_f =>
            (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧
            sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
            StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
          (P3P4.PanicOomProp s0)

/-- Caller-lifted `setSessionStateSpec A` at `lsmpl.base 48` on `lsProg_518 ext`. -/
theorem set_session_state_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (set_session_state_placed_ok hmemcpy (drop_session_structure_local1_placed_ok hdealloc)) (by decide)

/-- Caller-lifted `growOneSpeSpec A` at `lsmpl.base 42` on `lsProg_518 ext`. -/
theorem grow_one_spe_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (grow_one_spe_placed_ok hshim halloc hrealloc hpanic) (by decide)

def StageP3PrevEmptyVRegsM3PlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P3 (`dpClosureEntryM3Placed + 0x1778 → +0x34dc` /
`s0.readReg64 .x30`) over general `prevSessionsEmptyAt A coroPtr g` with `Steps` and
`calleeSavedVRegs`. -/
theorem stageP3Gen_prevEmpty_vregs_placed_ok_of_parts [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hErrSub5 : StageP3Sub5ErrPrevEmptyPlacedStmt) :
    StageP3PrevEmptyVRegsM3PlacedStmt := by
  intro A ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hLogClosure hpanic
    hcc hscc hroot
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    g recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hcro hpc hrun hsp_align hsp_root htr hvregs
    hOk hErr hVerNe
  refine stageP3_clone_prevEmpty_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hpanic hcc hscc
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur g msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗
      F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        FromRecordCallees.lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_placed_steps ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2
          hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrevEmpty_placed s0 s coroPtr ctxPtr outPtr initErrsPtr
            remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have herr := hErrSub5 ext hshim halloc hdealloc hmemcpy hGrow hDropSS3 hLogClosure hpanic
        s0 s2 coroPtr outPtr initErrsPtr hinit_ne e he_npan b_2c0
        g G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed at herr
      have herr_post :
          stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom
      apply sepWPp_frame_closOom_m3_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_m3_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmptyPlaced
      rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom
    apply sepWPp_frame_closOom_m3_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := stageP3_ver_ne_prevEmpty_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
      hLogClosure hpanic
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne
      msgVer b_2c0 g G₁ recG st
      hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFramePlaced
    exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` variants -/

/-- Relocatable `[LibsignalFullPlacement]` Substage P3.5 error path
(`dpClosureEntryM3Placed + 0x1cd8 → s0.readReg64 .x30`) discharging Block `519` internally
from `LibsignalFrozen lsmpl s.mem`. -/
def StageP3Sub5ErrPrevEmptyFullPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64),
      initErrsPtr ≠ 0#64 →
      ∀ (e : SignalProtocolError), e ≠ .panic →
      ∀ (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost)
        (st₂ recSt : SessionState (List (BitVec 8))),
        LibsignalFrozen lsmpl s.mem →
        s.pc = dpClosureEntryM3Placed + 0x1cd8#64 →
        s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true →
        s.trace = s0.trace →
        s.readReg64 .x19 = coroPtr →
        s.readReg64 .x24 = s.sp + 0x370#64 →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
          (stageP3ErrPrePrevEmptyM3Placed A s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
          (fun sf P_f =>
            (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e) ∧
            sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
            StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
          (P3P4.PanicOomProp s0)

/-- Relocatable `[LibsignalFullPlacement]` `StageP3PrevEmptyVRegsStmt` on `lsProg_518 ext`,
discharging Block `519` internally from `LibsignalFrozen lsmpl s.mem`. -/
def StageP3PrevEmptyVRegsM3FullPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) →
    subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
theorem stageP3Gen_prevEmpty_vregs_full_placed_ok_of_parts [LibsignalFullPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hErrSub5 : StageP3Sub5ErrPrevEmptyFullPlacedStmt) :
    StageP3PrevEmptyVRegsM3FullPlacedStmt := by
  intro A ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hpanic
    hcc hscc hroot
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    g recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hfr hpc hrun hsp_align hsp_root htr hvregs
    hOk hErr hVerNe
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  refine stageP3_clone_prevEmpty_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hpanic hcc hscc
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur g msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem :=
    libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗
      F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        FromRecordCallees.lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_placed_steps ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2
          hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem :=
      libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrevEmpty_placed s0 s coroPtr ctxPtr outPtr initErrsPtr
            remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have herr := hErrSub5 ext hshim halloc hdealloc hmemcpy hGrow hDropSS3 hpanic
        s0 s2 coroPtr outPtr initErrsPtr hinit_ne e he_npan b_2c0
        g G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed at herr
      have herr_post :
          stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom
      apply sepWPp_frame_closOom_m3_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_m3_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmptyPlaced
      rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom
    apply sepWPp_frame_closOom_m3_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := stageP3_ver_ne_prevEmpty_full_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
      hpanic
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne
      msgVer b_2c0 g G₁ recG st
      hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFramePlaced
    exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
