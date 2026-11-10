/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 2 Early `Err` Unwind (`0x0584 → 0x157c → 0x0350 → ret`)

Verifies `segB_err_ok` and `segB_err_ext_ok` when `get_identity_key_pair` returns `.error ()`,
skipping teardown of the empty `SessionRecord` and returning the `SpeOwned` error payload via `0x0350`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16

theorem sepWPp_of_sepWP_exit {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, hok | hoom⟩
  · exact ⟨sm, hsteps, Or.inl hok⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem memRegion_48_eq_words6 (r : BitVec 64) :
    memRegion r 48 =
      ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (r ↦₆₄ u0) ∗ ((r + 8#64) ↦₆₄ u1) ∗ ((r + 16#64) ↦₆₄ u2) ∗
        ((r + 24#64) ↦₆₄ u3) ∗ ((r + 32#64) ↦₆₄ u4) ∗ ((r + 40#64) ↦₆₄ u5) := by
  apply Entails.antisymm
  · rw [mr_split r (r + 8#64) 8 40 48 rfl rfl,
        mr_split (r + 8#64) (r + 16#64) 8 32 40 rfl (by bv_omega),
        mr_split (r + 16#64) (r + 24#64) 8 24 32 rfl (by bv_omega),
        mr_split (r + 24#64) (r + 32#64) 8 16 24 rfl (by bv_omega),
        mr_split (r + 32#64) (r + 40#64) 8 8 16 rfl (by bv_omega),
        memRegion_8_eq_exists r, memRegion_8_eq_exists (r + 8#64),
        memRegion_8_eq_exists (r + 16#64), memRegion_8_eq_exists (r + 24#64),
        memRegion_8_eq_exists (r + 32#64), memRegion_8_eq_exists (r + 40#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.refl _
  · refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u0 => ?_
    refine mr_fold r (r + 8#64) 8 40 48 (mr_of_u64 _ _) ?_ rfl rfl
    refine mr_fold (r + 8#64) (r + 16#64) 8 32 40 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    refine mr_fold (r + 16#64) (r + 24#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    refine mr_fold (r + 24#64) (r + 32#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    exact mr_fold (r + 32#64) (r + 40#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

theorem initSaved_eq_fsp {s0 s : State} (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    initSaved s0 =
      ((s.sp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s.sp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s.sp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s.sp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s.sp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s.sp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s.sp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s.sp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s.sp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s.sp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s.sp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s.sp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  have hb : s0.sp - 0x60#64 = s.sp + 7312#64 := by
    rw [cliInitiateFrame_eq] at hsp
    bv_omega
  unfold initSaved
  dsimp only
  simp only [hb, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]

/-- Witness `ApiError AddrVal Unit` value representing an identity-key-pair error return. -/
def initErrVal : Except (ApiError AddrVal Unit) Unit :=
  .error (.protocol .invalidProtobufEncoding)

theorem initErrVal_ne_panic : initErrVal ≠ .error .panic := by decide

theorem initErrVal_ne_store : initErrVal ≠ .error (.store ()) := by decide

theorem slotTrace_of_eq {s0 sf : State}
    (htr : sf.trace = s0.trace) (hfiles : sf.fs.files = s0.fs.files) :
    slotTrace s0 sf :=
  ⟨htr ▸ List.prefix_refl _, hfiles, congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem initResAt_err_of_speOwned (A : RustAlloc) (ret : BitVec 64) (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A ret k ⊢ initResAt A ret initErrVal :=
  Entails.sepExists_intro k

theorem calleeSavedPreserved_of_regs {s0 sf : State}
    (hx19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hx21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (hx22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hx23 : sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5))
    (hx24 : sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5))
    (hx25 : sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5))
    (hx26 : sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27 : sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hx28 : sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5))
    (hfp : sf.readReg64 .fp = s0.readReg64 .fp)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf :=
  ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩

set_option maxHeartbeats 1600000 in
/-- Early `Err` unwind from `0x0584` (`initProgExt`): skips drop on the empty `SessionRecord`,
stores the 6 `SpeOwned` words to `x.ret`, and returns via `0x0350`. -/
theorem segB_err_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    {k : RunDrop.SpeOwned} {w0 w1 w2 w3 w4 w5 : BitVec 64} {R_spe Plocals F_extra : SepProp}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0584)
    (htrace : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hkerr : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error ())
    (hx22 : s.readReg64 (.gpr 22#5) = 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = w0)
    (hx27 : s.readReg64 (.gpr 27#5) = w1)
    (hx25 : s.readReg64 (.gpr 25#5) = w2)
    (hx28 : s.readReg64 (.gpr 28#5) = w3)
    (hx24 : s.readReg64 (.gpr 24#5) = w4)
    (hx21 : s.readReg64 (.gpr 21#5) = w5)
    (hw0 : w0 ≠ (0#64 - 3#64))
    (hspe :
      ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A x.ret k)
    (hLocals :
      initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗ Plocals ⊢
        memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (memRegion x.ret 48 ∗
        initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗
        initSaved s0 ∗
        (R_spe ∗ Plocals ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
          stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ∗
          F_extra))
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    1412 12
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    5500 108
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    848 48
  clear hfn
  have hpc : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 1412#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask4096 : (((s.sp + 4096#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_4096 hsp_mask
  have hsp_mask7312 : (((s.sp + 7312#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_7312 hsp_mask
  have hx19 : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hw0_ne : w0 + 3#64 ≠ 0#64 := by bv_omega
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_false_of_ne hw0_ne
  have hw0_dec : decide (w0 + 3#64 = 0#64) = false := decide_eq_false hw0_ne
  have hm1_add : (0#64 - 1#64) + 1#64 = 0#64 := rfl
  have hm1_beq : ((0#64 - 1#64) + 1#64 == 0#64) = true := rfl
  have hm1_dec : decide ((0#64 - 1#64) + 1#64 = 0#64) = true := rfl
  apply sepWPp_of_sepWP_exit
  rw [← hctrl.sp]
  have hfr_fsp : initFreshRecAt s.sp =
      ((s.sp + 296#64) ↦₆₄ 0#64) ∗ ((s.sp + 304#64) ↦₆₄ 8#64) ∗
      ((s.sp + 312#64) ↦₆₄ 0#64) ∗ ((s.sp + 320#64) ↦₆₄ (0#64 - 1#64)) := rfl
  rw [memRegion_48_eq_words6 x.ret, initSaved_eq_fsp hctrl.sp, hfr_fsp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro u5
  apply SepWP.exists_left; intro u4
  apply SepWP.exists_left; intro u3
  apply SepWP.exists_left; intro u2
  apply SepWP.exists_left; intro u1
  apply SepWP.exists_left; intro u0
  dsimp only [initProgExt, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  wp_steps
  have hsp_raw : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl.sp
  have hsp : s.sp = s0.sp - 7408#64 := hctrl.sp
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply hpost
  refine ⟨?_, ?_, ?_⟩
  · simp only [arm64_norm, hsp]
  · apply calleeSavedPreserved_of_regs
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [calleeSavedVRegs, arm64_norm]
      exact hctrl.vregs
  · dsimp only [initSlotSpec, Spec.inImage]
    refine Entails.sepExists_right StoresGhost.opened ?_
    refine Entails.sepExists_right initErrVal ?_
    refine Entails.pure_right ⟨slotTrace_of_eq
      (by simp only [arm64_norm, htrace])
      (by simp only [arm64_norm]; exact hctrl.files0), by
        refine ⟨initErrVal_ne_panic, initErrVal_ne_store, ?_⟩
        rw [hS]
        exact initDef_eq_some_none_of_keyPair_err X P x.F x.peer.val x.me.val x.bundle
          x.coins hkerr⟩ ?_
    have hSavedFold :
        ((s.sp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s.sp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s.sp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s.sp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s.sp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s.sp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s.sp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s.sp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s.sp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s.sp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s.sp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s.sp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) = initSaved s0 :=
      (initSaved_eq_fsp hsp_raw).symm
    have hFreshFold :
        ((s.sp + 296#64) ↦₆₄ 0#64) ∗
        ((s.sp + 304#64) ↦₆₄ 8#64) ∗
        ((s.sp + 312#64) ↦₆₄ 0#64) ∗
        ((s.sp + 320#64) ↦₆₄ (0#64 - 1#64)) =
        initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) := by
      rw [← hsp_raw]; rfl
    have hRetEnt :
        ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
          ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        initResAt A x.ret initErrVal :=
      Entails.trans hspe (initResAt_err_of_speOwned A x.ret k)
    have hStkEnt :
        (initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗ Plocals) ∗
          initSaved s0 ∗
          stackAt (s.sp) (stk - cliInitiateFrame) ⊢
        stackAt s0.sp stk := by
      rw [hsp_raw]
      exact Entails.trans
        (sepConj_mono hLocals (Entails.refl _))
        (err_stack_fold s0 (stk_ge_frame hstk) hstk64)
    have hHeap : F_extra ⊢ anyHeap := entails_anyHeap F_extra
    have foc : ∀ {Full Sub Target F Goal : SepProp},
        (Full ⊢ Sub ∗ F) → (Sub ⊢ Target) → (Target ∗ F ⊢ Goal) → (Full ⊢ Goal) :=
      fun hfoc h hrest => Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)
    refine foc (by sep_frame) (Entails.of_eq hSavedFold) ?_
    refine foc (by sep_frame) (Entails.of_eq hFreshFold) ?_
    refine foc (by sep_frame) hRetEnt ?_
    refine foc (by sep_frame) hStkEnt ?_
    refine foc (by sep_frame) hHeap ?_
    sep_frame

/-- Early `Err` unwind from `0x0584` (`initProg`). -/
theorem segB_err_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    {k : RunDrop.SpeOwned} {w0 w1 w2 w3 w4 w5 : BitVec 64} {R_spe Plocals F_extra : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0584)
    (htrace : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hkerr : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error ())
    (hx22 : s.readReg64 (.gpr 22#5) = 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = w0)
    (hx27 : s.readReg64 (.gpr 27#5) = w1)
    (hx25 : s.readReg64 (.gpr 25#5) = w2)
    (hx28 : s.readReg64 (.gpr 28#5) = w3)
    (hx24 : s.readReg64 (.gpr 24#5) = w4)
    (hx21 : s.readReg64 (.gpr 21#5) = w5)
    (hw0 : w0 ≠ (0#64 - 3#64))
    (hspe :
      ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A x.ret k)
    (hLocals :
      initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗ Plocals ⊢
        memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (memRegion x.ret 48 ∗
        initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗
        initSaved s0 ∗
        (R_spe ∗ Plocals ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
          stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ∗
          F_extra))
      Q Qp (initOom s0) :=
  segB_err_ext_ok (ext := cliHookExterns W) himg hS hstk hstk64
    ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0,
      hctrl.inv, hctrl.vregs, hctrl.spAligned⟩
    htrace hx8 hkerr hx22 hx26 hx27 hx25 hx28 hx24 hx21 hw0 hspe hLocals hpost

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
