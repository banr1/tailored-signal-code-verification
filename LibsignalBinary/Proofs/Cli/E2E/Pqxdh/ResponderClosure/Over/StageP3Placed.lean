/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGenPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import all Init.Data.String.Defs

/-!
# Placed Stage P3 Over-Path Specification (`previous_sessions = [enc]`)

Proves `[LibsignalPlacement]` and `[LibsignalFullPlacement]` Stage P3 specifications
(`+0x1778 → +0x34dc` or error exit to `s0.readReg64 .x30`) over a 1-element `previous_sessions`
vector `prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib SepProp
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
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- Placed dispatch precondition at `+0x1cd8` over a 1-element `prevVecAt [enc]`. -/
def stageP3DispatchPrePrev1Placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A (s.sp + 0x270#64) res ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Placed dispatch `Ok(pt)` postcondition at `+0x34dc` over a 1-element `prevVecAt [enc]`. -/
def stageP3DispatchOkMidPrev1Placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (enc pt : List (BitVec 8)) (b_2c0 : BitVec 8)
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
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Placed version-mismatch exit body at `dpClosureEntryM3Placed + 0x1e04` on `lsProg_518 ext`. -/
abbrev OverVerNe1e04CliAtPlacedBody [LibsignalPlacement] (A : RustAlloc)
    (PrevEncOK : List (BitVec 8) → Prop) (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
    initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 →
    ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
    ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), PrevEncOK enc →
    ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
      st.version = 4#32 → rootStack ≤ s.sp.toNat →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
      s1.status = .Running → s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
         ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
         sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
         prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
         memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp rootStack)
        (fun sf P_f =>
          (∃ wd0 : BitVec 64, P_f ⊢
              ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
              ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
              memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
              stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
                (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
        (P3P4.PanicOomProp s0)

theorem bind_sepWP_lscro_steps_prev1_placed [LibsignalPlacement]
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

theorem sepWPp_frame_closOom_prev1_placed {prog : Program} {ret : BitVec 64} {s0 s : State}
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

theorem bind_sepWPp_genPanic_steps_framed_prev1_placed {prog : Program} {mid ret : BitVec 64}
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

theorem postTryDecrypt_entails_s5DispatchPrev1_placed [LibsignalPlacement] {A : RustAlloc}
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) :
    (LsTokenInitM3 ∗
      sessionStateAt A (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A (s.sp + 0x270#64) res ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
      signalMessageAt A msgG whisperMsgPtr msg ∗ coinsPost ∗ FromRecordCallees.lsLogOff ∗
      stackAt s.sp rootStack ∗ A.pool) ∗
    (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp) ⊢
    stageP3DispatchPrePrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost ∗
    overScratch s.sp := by
  unfold stageP3Sub5ExtraPrePrev1 stageP3DispatchPrePrev1Placed genP3S5PostFramePlaced
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  rw [hlog, stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp)
    (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

private theorem stageP3_clone_prev1_vregs_prefix_placed_steps [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    {A : RustAlloc} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
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
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (LsTokenInitM3 ∗
        genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone ext hshim halloc hmemcpy hpanic hcc hscc s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp :=
    LsTokenInitM3 ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp ∗ F_frame
  have hP :
      (LsTokenInitM3 ∗
        genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp ∗ F_frame) =
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

private theorem pull_tryDecrypt_post_prev1 [LibsignalPlacement] {A : RustAlloc}
    {m : Memory} {P_pure : Prop} {G₁ : SessionGhost} {ok : Bool}
    {sp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64}
    {st' : SessionState (List (BitVec 8))}
    {res : Except SignalProtocolError (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {coinsPost F R : SepProp}
    (hm2 : m ⊨
      (LsTokenInitM3 ∗
        (⌜P_pure⌝ ∗
          (∃∗ G' : SessionGhost, ⌜G₁.AfterTryDecrypt ok G'⌝ ∗ sessionStateAt A (sp + 0xa90#64) G' st') ∗
          vecResultAt A (sp + 0x270#64) res ∗
          protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗ coinsPost ∗
          FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool)) ∗ (F ∗ R)) :
    ∃ G' : SessionGhost, P_pure ∧ G₁.AfterTryDecrypt ok G' ∧
      m ⊨ ((LsTokenInitM3 ∗ sessionStateAt A (sp + 0xa90#64) G' st' ∗
        vecResultAt A (sp + 0x270#64) res ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ coinsPost ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool) ∗ F) ∗ R := by
  have heq :
      (LsTokenInitM3 ∗
        (⌜P_pure⌝ ∗
          (∃∗ G' : SessionGhost, ⌜G₁.AfterTryDecrypt ok G'⌝ ∗ sessionStateAt A (sp + 0xa90#64) G' st') ∗
          vecResultAt A (sp + 0x270#64) res ∗
          protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗ coinsPost ∗
          FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool)) ∗ (F ∗ R) =
      ⌜P_pure⌝ ∗
        ((∃∗ G' : SessionGhost, ⌜G₁.AfterTryDecrypt ok G'⌝ ∗ sessionStateAt A (sp + 0xa90#64) G' st') ∗
          LsTokenInitM3 ∗ vecResultAt A (sp + 0x270#64) res ∗
          protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗ coinsPost ∗
          FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool ∗ F ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm2
  rcases hm2 with ⟨hp, hm2_ex⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_ex
  obtain ⟨G', hm2_G⟩ := hm2_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm2_G
  rcases hm2_G with ⟨hrel, hm2_rest⟩
  refine ⟨G', hp, hrel, ?_⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm2_rest

set_option maxHeartbeats 1200000 in
theorem stageP3_call_tryDecrypt_prev1_placed_steps [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hroot : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
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
  refine bind_sepWP_lscro_steps_prev1_placed hcro1 hbl (emp_sepConj _).symm
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
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest }
  intro R hm hL
  have hpre_c : sc.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K))).pre x sc ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsCodeRoLoaded,
      pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.CoinsTape.cliTapeAt, x]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hcroc, ?_⟩
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hpq_lt, ?_⟩
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
  · dsimp only [StoreKit.withLsCodeRoLoaded,
      pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      CryptoVerification.Cli.CoinsTape.cliTapeAfter, TryDecryptGhost.model, x] at hm2
    rw [hspc] at hm2
    have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := hcroc.of_keepsFrozen hsteps2.keepsFrozen
    obtain ⟨G', ⟨hnpan, htr2_c⟩, hdec_rel, hm2_cont⟩ := pull_tryDecrypt_post_prev1 hm2
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    obtain ⟨sf, hsteps3, hout3⟩ :=
      hCont s2 G' (hsteps_bl.trans hsteps2) hnpan hdec_rel (hpc2_lr.trans hx30_c) hrun2
        (hsp2_c.trans hspc) (htr2_c.trans htrc_0) hcro2
        (hx19_cs2.trans (hx19_c.trans hx19_1)) (hx24_cs2.trans (hx24_c.trans hx24_1))
        (hx27_cs2.trans (hx27_c.trans hx27_1)) (hvregs_cs2.trans hvregs_c)
        R hm2_cont (hsteps2.codeLoaded hL)
    exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded,
      pollTryDecryptM3PlacedSpecTPTight,
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

/-- Placed Stage P3 specification (`dpClosureEntryM3Placed + 0x1778 → +0x34dc` or `s0.readReg64 .x30`)
over a 1-element `prevVecAt [enc]` on `lsProg_518 ext`. -/
def StageP3Prev1VRegsM3PlacedStmt [LibsignalPlacement]
    (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (ext : String → Option (State → State))
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
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    OverVerNe1e04CliAtPlacedBody A PrevEncOK ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 → PrevEncOK enc → st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
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
          stageP3DispatchOkMidPrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            ptCap ptPtr enc pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗ anyHeap) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
private theorem stageP3Gen_prev1_ver_ne_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (ext : String → Option (State → State))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hVerNeAt : OverVerNe1e04CliAtPlacedBody A PrevEncOK ext)
    (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap_nz : prevCap ≠ 0#64)
    (hEnc : PrevEncOK enc) (hst_ver4 : st.version = 4#32) (hver : st.version ≠ msgVer)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29_s : s.readReg64 .x29 = s.sp + 0xc70#64)
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1e04#64)
    (hrun1 : s1.status = .Running) (htr1 : s1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest) ∗
        overScratch s.sp ∗ anyHeap) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((genP3PostNePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)) ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  have hmsgVer_ne4 : msgVer ≠ 4#32 := fun h => hver (hst_ver4.trans h.symm)
  apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
  unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPrePrev1; rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
  have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun G₁ => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
  refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
  unfold genP3S5SpillRem; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wFront => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_
  have hver_ne := hVerNeAt
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc G₁ recG st
    hst_ver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
  refine SepWPp.bind_sepWPp_frame_raw hver_ne (by sep_focus)
    fun sf P_f hpcf hrunf ⟨⟨wd0, hent_f⟩, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent_f) (SepWPp.done hpcf hrunf ?_)
  refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
  unfold genP3S5PostFramePlaced genP3S5SpillRem
  have hwFront_repack :
      ((s.sp + 0x48#64) ↦₆₄ wFront.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ wFront.u50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wFront.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wFront.u7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wFront.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ⊢
      ∃∗ w : GenP3S5FrontRem,
        ((s.sp + 0x48#64) ↦₆₄ w.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((s.sp + 0x5c#64) ↦₃₂ w.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((s.sp + 0x98#64) ↦₆₄ w.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ w.ud0) :=
    Entails.sepExists_right ⟨wFront.u48, wFront.u50, wFront.u98, wd0, wFront.u5c, wFront.u7c⟩
      (Entails.refl _)
  exact entails_replace_sub hwFront_repack (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Placed Stage P3 (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`,
parameterized by `CloneGenVRegsPlacedStmt`. -/
theorem stageP3Gen_prev1_vregs_at_placed_ok_of_clone [LibsignalPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsPlacedStmt) :
    StageP3Prev1VRegsM3PlacedStmt A PrevEncOK := by
  intro ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hLogClosure hpanic
    hcc hscc hroot hVerNeAt s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hcro hpc hrun hsp_align hsp_root hx29_s htr hvregs hOk hErr hVerNe
  refine stageP3_clone_prev1_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hpanic hcc hscc s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur enc msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp)) ∗ F_frame)
    (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗
        A.pool) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrev1_placed s0 s coroPtr ctxPtr outPtr initErrsPtr
            prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    have hlog : (lsLogFilterAddr ↦₆₄ 0#64) = FromRecordCallees.lsLogOff := rfl
    unfold stageP3DispatchPrePrev1Placed; rw [hlog]
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prev1_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
        hLogClosure hpanic s0 s2 coroPtr outPtr initErrsPtr prevCap prevPtr hinit_ne e he_npan
        b_2c0 enc G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrev1Placed at herr
      have herr_post : stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ =>
          hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan
            (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
            hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState
        s0 s2 coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrev1Placed; rw [hlog, hstack_set]
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    exact stageP3Gen_prev1_ver_ne_branch_placed ext C K hVerNeAt
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
      recG st rem loc msgG msg F_frame Q
      hinit_ne hcap_nz hEnc hst_ver4 hver hsp_align hsp_root hx29_s
      hcro1 hpc1 hrun1 htr1 hvregs1 hVerNe

/-- Lifts `subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)` to
`subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec)`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem stageP3Gen_prev1_vregs_at_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop} :
    StageP3Prev1VRegsM3PlacedStmt A PrevEncOK :=
  stageP3Gen_prev1_vregs_at_placed_ok_of_clone cloneGen_vregs_placed_ok

theorem OverVerNe1e04CliAtPlacedBody.mono_prevEncOK [LibsignalPlacement]
    {A : RustAlloc} {P Q : List (BitVec 8) → Prop} {ext : String → Option (State → State)}
    (hpq : ∀ enc, P enc → Q enc)
    (h : OverVerNe1e04CliAtPlacedBody A Q ext) :
    OverVerNe1e04CliAtPlacedBody A P ext :=
  fun s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc =>
    h s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc (hpq enc hEnc)

/-- Discharges `OverVerNe1e04CliAtPlacedBody Record.A0 PrevEncOK ext` from callees and `HookSat`. -/
theorem overVerNe1e04CliAtPlacedBody_a0_of_hooks [LibsignalPlacement]
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → VerNe.OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl VerNe.pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec CryptoVerification.E2E.Record.A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec CryptoVerification.E2E.Record.A0)))
    (hshim_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
      noAllocShimSpec)
    (halloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
      (rustAllocSpec CryptoVerification.E2E.Record.A0))
    (hrealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
      (rustReallocSpec CryptoVerification.E2E.Record.A0))
    (hdealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustDeallocSpec CryptoVerification.E2E.Record.A0))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverVerNe1e04CliAtPlacedBody CryptoVerification.E2E.Record.A0 PrevEncOK ext :=
  OverVerNe1e04CliAtPlacedBody.mono_prevEncOK hEncImp
    (VerNe.overVerNe_1e04_cro_a0_placed_of_hooks ext hLogClosure hGrow hDropSS3
      hshim_sat halloc_sat hrealloc_sat hdealloc_sat
      hmc_sat hpanic_alloc hpanic_raw)

section StageP3ZeroCapTail

open ProofLib.ProgramReflection
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem bind_sepWP_lscro_frame_zero_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_step P_step_post F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_prev1_placed hcro hstep hP fun sm _ => hnext sm

private theorem pointsToBytesRO_decryptionFailed_zero_placed (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  have hsplit : decryptionFailedStr =
      [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
      ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8]) := by rfl_kernel
  rw [hsplit, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO_cons,
    pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  simp only [BitVec.reduceAppend]

theorem intro_lsro_decryptionFailed_zero_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by rfl_kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_zero_placed] at hro0
  have hro1 : s.mem ⊨ (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hro0
  exact SepWPp.drop_frame (P_drop := (lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8)
    (by ac_rfl) hwp R hro1 hL

private theorem p3_err_tail_prev_zero_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State)
    (coroPtr outPtr errTag prevStatesPtr w_370 w_378 w_380 w_388
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24 savedX25
      savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x359c#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧ s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧ s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧ s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [dpClosureEntryVerPlaced] at hpc; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨by sep_frame,
    by simp_all [arm64_norm], rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_common_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errTag prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = lsmpl.base 512)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryVerPlaced + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscl_nopanic_prev1 (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro hDropSS3 hpc hrun hsp_al hx30 (by dsimp only [dropSessionStructureLocal2Spec]) hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1_s => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hstep2 := p3_err_tail_prev_zero_wp ext s1 coroPtr outPtr errTag prevStatesPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
    hpc1 hrun1 hsp1_align (hx19_cs1.trans hx19) (hx22_cs1.trans hx22)
    (by rw [hx25_cs1, hx25, hsp1_s]) (hx26_cs1.trans hx26) (hx28_cs1.trans hx28)
  rw [hsp1_s] at hstep2
  refine bind_sepWP_lscro_frame_zero_placed hcro1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_36_err_fold s.sp (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf_s, htrf_1.trans (htr1_s.trans htr),
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
    hcrof, hvregs_f.trans hvregs_cs1⟩

set_option maxHeartbeats 800000 in
theorem p3_alloc_33b0_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryVerPlaced + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryVerPlaced + 0x33b4#64) := by
    dsimp only [dpClosureEntryVerPlaced] at hpc ⊢; wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp_all [arm64_norm]⟩
  refine bind_sepWP_lscro_frame_zero_placed hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, by decide, ⟨0, rfl⟩, by decide⟩
  refine call_raw_nopanic_prev1 (spec := rustAllocSpec A) (x := (17, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc hpc1 hrun1 hsp1_al hlr1 (by dsimp only [rustAllocSpec]; rw [hsp1]) hφ (emp_sepConj _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]; rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hoom_steps : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.trace = s2.trace) := by
      have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      dsimp only [lsHandleErrorSym, dpClosureEntryVerPlaced] at hpc2 ⊢; wp_steps
      exact SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
    refine bind_sepWP_lscro_frame_zero_placed hcro2 hoom_steps (emp_sepConj _).symm
      fun s3 hpc3 hrun3 _ htr3 => ?_
    have hext : (lsProg_518 ext).externAt? s3.pc = some Rust.panicked := by
      rw [hpc3]; exact (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
    exact SepWPp.panic hrun3 hext fun R hm =>
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq
        (by simp only [Rust.panicked, htr3, htr2, htr1, htr])) hm
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    exact SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

set_option maxHeartbeats 800000 in
theorem p3_alloc_2eac_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (F : SepProp) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eac#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eb0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      (P3P4.PanicOomProp s0) := by
  have hbl : SepWP (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x2eb0#64) := by
    dsimp only [dpClosureEntryM3Placed] at hpc ⊢; wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp_all [arm64_norm]⟩
  refine bind_sepWP_lscro_frame_zero_placed hcro hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hφ : (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk 17 1 :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, by decide, ⟨0, rfl⟩, by decide⟩
  refine call_raw_nopanic_prev1 (spec := rustAllocSpec A) (x := (17, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc hpc1 hrun1 hsp1_al hlr1 (by dsimp only [rustAllocSpec]; rw [hsp1]) hφ (emp_sepConj _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]; rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr2 => ?_
    have hoom_steps : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.trace = s2.trace) := by
      have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      dsimp only [lsHandleErrorSym, dpClosureEntryM3Placed] at hpc2 ⊢; wp_steps
      exact SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
    refine bind_sepWP_lscro_frame_zero_placed hcro2 hoom_steps (emp_sepConj _).symm
      fun s3 hpc3 hrun3 _ htr3 => ?_
    have hext : (lsProg_518 ext).externAt? s3.pc = some Rust.panicked := by
      rw [hpc3]; exact (ls_externAt?_of_mem (prog := lsProg_518 ext) (i := 518) (by decide)).trans hpanic
    exact SepWPp.panic hrun3 hext fun R hm =>
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq
        (by simp only [Rust.panicked, htr3, htr2, htr1, htr])) hm
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    exact SepWPp.pure_elim fun ⟨_, htr2⟩ =>
      SepWPp.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hcro2⟩

end StageP3ZeroCapTail

/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` Variants -/

/-- `[LibsignalFullPlacement]` version-mismatch exit body at `dpClosureEntryM3Placed + 0x1e04` taking
`LibsignalFrozen lsmpl s1.mem`. -/
abbrev OverVerNe1e04CliAtFrozenPlacedBody [LibsignalFullPlacement] (A : RustAlloc)
    (PrevEncOK : List (BitVec 8) → Prop) (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
    initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 →
    ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
    ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), PrevEncOK enc →
    ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
      st.version = 4#32 → rootStack ≤ s.sp.toNat →
      LibsignalFrozen lsmpl s1.mem →
      s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
      s1.status = .Running → s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
         ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
         sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
         prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
         memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp rootStack)
        (fun sf P_f =>
          (∃ wd0 : BitVec 64, P_f ⊢
              ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
              ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
              memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
              stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
                (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
        (P3P4.PanicOomProp s0)

/-- `[LibsignalFullPlacement]` Stage P3 specification (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`)
over a 1-element `prevVecAt [enc]`, discharging `.rodata` from `LibsignalFrozen`. -/
def StageP3Prev1VRegsM3FrozenPlacedStmt [LibsignalFullPlacement]
    (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (ext : String → Option (State → State))
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
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    OverVerNe1e04CliAtFrozenPlacedBody A PrevEncOK ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 → PrevEncOK enc → st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
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
          stageP3DispatchOkMidPrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            ptCap ptPtr enc pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp ∗ anyHeap) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
private theorem stageP3Gen_prev1_ver_ne_branch_full_placed [LibsignalFullPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (ext : String → Option (State → State))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A PrevEncOK ext)
    (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap_nz : prevCap ≠ 0#64)
    (hEnc : PrevEncOK enc) (hst_ver4 : st.version = 4#32) (hver : st.version ≠ msgVer)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29_s : s.readReg64 .x29 = s.sp + 0xc70#64)
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1e04#64)
    (hrun1 : s1.status = .Running) (htr1 : s1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest) ∗
        overScratch s.sp ∗ anyHeap) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((genP3PostNePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)) ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  have hmsgVer_ne4 : msgVer ≠ 4#32 := fun h => hver (hst_ver4.trans h.symm)
  apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
  unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPrePrev1; rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
  have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun G₁ => ?_
  refine P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ => ?_)
  refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
  unfold genP3S5SpillRem; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wFront => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_
  have hver_ne := hVerNeAt
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc G₁ recG st
    hst_ver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
  refine SepWPp.bind_sepWPp_frame_raw hver_ne (by sep_focus)
    fun sf P_f hpcf hrunf ⟨⟨wd0, hent_f⟩, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent_f) (SepWPp.done hpcf hrunf ?_)
  refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
  unfold genP3S5PostFramePlaced genP3S5SpillRem
  have hwFront_repack :
      ((s.sp + 0x48#64) ↦₆₄ wFront.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ wFront.u50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wFront.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wFront.u7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wFront.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ⊢
      ∃∗ w : GenP3S5FrontRem,
        ((s.sp + 0x48#64) ↦₆₄ w.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((s.sp + 0x5c#64) ↦₃₂ w.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((s.sp + 0x98#64) ↦₆₄ w.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ w.ud0) :=
    Entails.sepExists_right ⟨wFront.u48, wFront.u50, wFront.u98, wd0, wFront.u5c, wFront.u7c⟩
      (Entails.refl _)
  exact entails_replace_sub hwFront_repack (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3Gen_prev1_vregs_at_full_placed_ok_of_clone [LibsignalFullPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsPlacedStmt) :
    StageP3Prev1VRegsM3FrozenPlacedStmt A PrevEncOK := by
  intro ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hpanic
    hcc hscc hroot hVerNeAt s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hfr hpc hrun hsp_align hsp_root hx29_s htr hvregs hOk hErr hVerNe
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := lscro_of_frozen hfr
  refine stageP3_clone_prev1_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hpanic hcc hscc s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur enc msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem := libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre
    (P' := (genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp)) ∗ F_frame)
    (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗
        A.pool) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem := libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrev1_placed s0 s coroPtr ctxPtr outPtr initErrsPtr
            prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    have hlog : (lsLogFilterAddr ↦₆₄ 0#64) = FromRecordCallees.lsLogOff := rfl
    unfold stageP3DispatchPrePrev1Placed; rw [hlog]
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prev1_full_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
        hpanic s0 s2 coroPtr outPtr initErrsPtr prevCap prevPtr hinit_ne e he_npan
        b_2c0 enc G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrev1Placed at herr
      have herr_post : stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ =>
          hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan
            (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
            hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState
        s0 s2 coroPtr outPtr pt G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrev1Placed; rw [hlog, hstack_set]
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    exact stageP3Gen_prev1_ver_ne_branch_full_placed ext C K hVerNeAt
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
      recG st rem loc msgG msg F_frame Q
      hinit_ne hcap_nz hEnc hst_ver4 hver hsp_align hsp_root hx29_s
      hfr1 hpc1 hrun1 htr1 hvregs1 hVerNe

theorem stageP3Gen_prev1_vregs_at_full_placed_ok [LibsignalFullPlacement]
    {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop} :
    StageP3Prev1VRegsM3FrozenPlacedStmt A PrevEncOK :=
  stageP3Gen_prev1_vregs_at_full_placed_ok_of_clone cloneGen_vregs_placed_ok

theorem OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK [LibsignalFullPlacement]
    {A : RustAlloc} {P Q : List (BitVec 8) → Prop} {ext : String → Option (State → State)}
    (hpq : ∀ enc, P enc → Q enc)
    (h : OverVerNe1e04CliAtFrozenPlacedBody A Q ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A P ext :=
  fun s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc =>
    h s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc (hpq enc hEnc)

theorem overVerNe1e04CliAtFrozenPlacedBody_a0_of_hooks [LibsignalFullPlacement]
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → VerNe.OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec CryptoVerification.E2E.Record.A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec CryptoVerification.E2E.Record.A0)))
    (hshim_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
      noAllocShimSpec)
    (halloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
      (rustAllocSpec CryptoVerification.E2E.Record.A0))
    (hrealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
      (rustReallocSpec CryptoVerification.E2E.Record.A0))
    (hdealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustDeallocSpec CryptoVerification.E2E.Record.A0))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverVerNe1e04CliAtFrozenPlacedBody CryptoVerification.E2E.Record.A0 PrevEncOK ext :=
  OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK hEncImp
    (VerNe.overVerNe_1e04_frozen_a0_placed_of_hooks ext hGrow hDropSS3
      hshim_sat halloc_sat hrealloc_sat hdealloc_sat
      hmc_sat hpanic_alloc hpanic_raw)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end
