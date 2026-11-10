/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRoot
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame

/-!
# `signal_session::run` Placed Arm `R3a`: Whisper Arm Proof

Relocatable (`[LibsignalPlacement]`) proof of `run_hop_recvW_placed_ok` (`RunHopRecvWPlaced`) on
Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt?

private theorem r3a_seq [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm => CodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => hCI.of_keepsFrozen h0 hkf) hinv h

private theorem r3a_vregs_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 v rfl
private theorem r3a_vregs_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 1#5 v rfl
private theorem r3a_vregs_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 2#5 v rfl

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero r3a_vregs_0 r3a_vregs_1 r3a_vregs_2

private theorem r3a_sigTryFrom_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (Wire.tryFromPlacedSpec A)) :=
  E2E.Pqxdh.ResponderWire.ls_subroutine_ok_cro_of_block (callerProg := runProgPlaced H) (i := 579) (j := 85)
    (Wire.tryFrom_placed_ok_of_deps
      (RunProofs.PksmWire.tripleRatchetHooksWPlaced_of_codecHooks hh.codecHooks)
      (RunProofs.PksmWire.tryFromDepsPlaced_of_codecHooks hh.codecHooks))
    (by decide) (by decide) (by decide)

private theorem r3a_call [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks}
    {callee_pc ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee_pc
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = callee_pc) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
        Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') →
        False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
        (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem →
        sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
        SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hpre : s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    refine Satisfies.mono (Entails.trans (sepConj_mono_left hP) ?_) hm
    exact Entails.trans
      (Entails.of_eq (show (spec.pre x s ∗ F) ∗ R = spec.pre x s ∗ (F ∗ R) by ac_rfl))
      (sepConj_mono_left (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
        (sepConj_mono_right (Entails.trans (Entails.pure_right (hCI.toRoCl hinv) (Entails.refl emp))
          (Entails.of_eq (sepConj_emp _))))))
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · have hinv_m : CodeOk sm.mem := hCI.of_keepsFrozen hinv hsteps.keepsFrozen
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hsteps hinv_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost, hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r3a_call_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks}
    {callee_pc ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee_pc (withCodeOk CodeOk spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = callee_pc) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
        Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') →
        False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
        (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem →
        sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
        SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hpre : s.mem ⊨ (withCodeOk CodeOk spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withCodeOk]
    refine Satisfies.mono (Entails.trans (sepConj_mono_left hP) ?_) hm
    exact Entails.trans
      (Entails.of_eq (show (spec.pre x s ∗ F) ∗ R = spec.pre x s ∗ (F ∗ R) by ac_rfl))
      (sepConj_mono_left (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
        (sepConj_mono_right (Entails.trans (Entails.pure_right hinv (Entails.refl emp))
          (Entails.of_eq (sepConj_emp _))))))
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · have hinv_m : CodeOk sm.mem := hCI.of_keepsFrozen hinv hsteps.keepsFrozen
    dsimp only [withCodeOk] at hpost
    rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hsteps hinv_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost, hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · dsimp only [withCodeOk] at hpost
    exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r3a_cs_regs {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
    sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
    sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
    sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
    sf.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs sf = calleeSavedVRegs s := by
  unfold CalleeSavedPreserved at h; simp_all

private def r3a_hiGaps (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x240#64) 32 ∗ memRegion (fsp + 0x280#64) 160 ∗ memRegion (fsp + 0x350#64) 48 ∗
    memRegion (fsp + 0x390#64) 208 ∗ memRegion (fsp + 0x548#64) 7784 ∗ memRegion (fsp + 0x23e0#64) 1552
private def r3a_frameGaps (fsp : BitVec 64) : SepProp := memRegion fsp 0x208 ∗ r3a_hiGaps fsp

private theorem r3a_tail_split (fsp : BitVec 64) :
    memRegion (fsp + 0x220#64) 10192 = memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗
      memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp := by
  have hs : ∀ (a : BitVec 64) (m n : Nat), m + n ≤ 2 ^ 64 → memRegion a (m + n) = memRegion a m ∗ memRegion (a + BitVec.ofNat 64 m) n :=
    fun a m n h => ProofLib.memRegion_split a m n h
  rw [show (10192 : Nat) = 32 + 10160 from rfl, hs _ _ _ (by decide), show (10160 : Nat) = 32 + 10128 from rfl, hs _ _ _ (by decide),
    show (10128 : Nat) = 32 + 10096 from rfl, hs _ _ _ (by decide), show (10096 : Nat) = 160 + 9936 from rfl, hs _ _ _ (by decide),
    show (9936 : Nat) = 48 + 9888 from rfl, hs _ _ _ (by decide), show (9888 : Nat) = 48 + 9840 from rfl, hs _ _ _ (by decide),
    show (9840 : Nat) = 16 + 9824 from rfl, hs _ _ _ (by decide), show (9824 : Nat) = 208 + 9616 from rfl, hs _ _ _ (by decide),
    show (9616 : Nat) = 112 + 9504 from rfl, hs _ _ _ (by decide), show (9504 : Nat) = 120 + 9384 from rfl, hs _ _ _ (by decide),
    show (9384 : Nat) = 7784 + 1600 from rfl, hs _ _ _ (by decide), show (1600 : Nat) = 48 + 1552 from rfl, hs _ _ _ (by decide)]
  unfold r3a_hiGaps; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
private theorem r3a_frame_eq (fsp : BitVec 64) :
    runLocals fsp [] = memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
      memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp := by
  rw [runLocals_empty_eq, show (runLocalBytes : Nat) = 0x208 + 10216 from rfl, ProofLib.memRegion_split fsp 0x208 10216 (by decide),
    show (10216 : Nat) = 24 + 10192 from rfl, ProofLib.memRegion_split (fsp + 0x208#64) 24 10192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; rw [r3a_tail_split fsp]; unfold r3a_frameGaps; ac_rfl
private theorem r3a_frame_join_eq (A : RustAlloc) (fsp : BitVec 64) (out : Bytes) :
    runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) out)] = vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
      memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp := by
  simp only [runLocals, runLocalsFrom, Nat.sub_zero, BitVec.add_zero]
  rw [show runLocalBytes - (0x208 + 24) = 10192 from rfl, r3a_tail_split fsp]; unfold r3a_frameGaps; ac_rfl
private theorem r3a_frame_some_eq (fsp : BitVec 64) (meG : AddrGhost) :
    runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] = addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗
      memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp := by
  simp only [runLocals, runLocalsFrom, Nat.sub_zero, BitVec.add_zero]
  rw [show runLocalBytes - (0x1d0 + 16) = 40 + 10216 from rfl, ProofLib.memRegion_split (fsp + 0x1e0#64) 40 10216 (by decide),
    show (10216 : Nat) = 24 + 10192 from rfl, ProofLib.memRegion_split (fsp + 0x1e0#64 + 40#64) 24 10192 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; rw [r3a_tail_split fsp]; ac_rfl
private theorem r3a_memRegion_words : ∀ (n : Nat) (a : BitVec 64) {m : Memory} {R : SepProp},
    8 * n ≤ 2 ^ 64 → (m ⊨ memRegion a (8 * n) ∗ R) → ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ R)
  | 0, a, _, _, _, hm => ⟨[], rfl, by simpa only [Nat.mul_zero, ProofLib.memRegion_zero, words64At] using hm⟩
  | n + 1, a, _, R, hle, hm => by
    have hsplit : memRegion a (8 * (n + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * n) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]; exact ProofLib.memRegion_split a 8 (8 * n) (by omega)
    rw [hsplit, ProofLib.memRegion_eight a, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨w, hm⟩ := hm
    obtain ⟨ws, hlen, hws⟩ := r3a_memRegion_words n (a + 8#64) (by omega) (Eq.mp (congrArg (_ ⊨ ·) (by ac_rfl)) hm : _ ⊨ memRegion (a + 8#64) (8 * n) ∗ ((a ↦₆₄ w) ∗ R))
    exact ⟨w :: ws, by simp [hlen], by simpa only [words64At] using Eq.mp (congrArg (_ ⊨ ·) (by ac_rfl)) hws⟩
private theorem r3a_speWord_ne_tags {i : Nat} (_hi : i < 64) : speWord i + 3#64 ≠ 0#64 ∧ speWord i + 2#64 ≠ 0#64 := by
  unfold speWord; rw [show (asm64% speNicheBase : BitVec 64) = (1#64 <<< 63) from rfl]; constructor <;> bv_omega
private theorem r3a_cap_ne_tags {cap : BitVec 64} (_h : cap.toNat < 2 ^ 63) : cap + 3#64 ≠ 0#64 ∧ cap + 2#64 ≠ 0#64 := by constructor <;> bv_omega
private theorem r3a_strRefR (f : BitVec 64 → BitVec 64) (lit : List (BitVec 8)) : Reloc f 16 (fun b => strRefAt (f b) lit) :=
  Reloc.sepEx fun p => Reloc.sep (Reloc.pt64 f p) ((Reloc.pt64 (fun b => f b + 8#64) (BitVec.ofNat 64 lit.length)).frameR (p ↦ᵣ lit))
private theorem r3a_vecU8R (A : RustAlloc) (f : BitVec 64 → BitVec 64) (bs : List (BitVec 8)) : Reloc f 24 (fun b => vecU8 A (f b) bs) :=
  Reloc.sepEx fun cap => Reloc.sepEx fun ptr => Reloc.vecU8AtR A f cap ptr bs

private theorem r3a_word_tail_reloc {w0 : BitVec 64} {T P : BitVec 64 → SepProp}
    (hP : ∀ a, P a = (a ↦₆₄ w0) ∗ T a) (hT : Reloc (fun b => b + 8#64) 40 T)
    (htags : w0 + 3#64 ≠ 0#64 ∧ w0 + 2#64 ≠ 0#64) {src : BitVec 64} {m : Memory} {R : SepProp}
    (hm : m ⊨ P src ∗ R) :
    ∃ (u0 u1 u2 u3 u4 u5 : BitVec 64) (H : SepProp),
      u0 + 3#64 ≠ 0#64 ∧ u0 + 2#64 ≠ 0#64 ∧
      (m ⊨ words64At src [u0, u1, u2, u3, u4, u5] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64, words64At dst [u0, u1, u2, u3, u4, u5] ∗ H ⊢ P dst) := by
  obtain ⟨G, hG⟩ := hT; rw [hP src] at hm
  have hm1 : m ⊨ RelocBytes (fun b => b + 8#64) 40 G src ∗ ((src ↦₆₄ w0) ∗ R) :=
    Satisfies.mono (sepConj_mono_left (hG src).1) (Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm)
  unfold RelocBytes at hm1; rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨bs, hm1⟩ := hm1; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨hbs, hm1⟩
  obtain ⟨ws, hws_len, rfl⟩ := exists_unpack64List 5 (by omega : bs.length = 8 * 5)
  rcases ws with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, _ | ⟨u4, _ | ⟨u5, _ | _⟩⟩⟩⟩⟩ <;> try (simp at hws_len; done)
  refine ⟨w0, u1, u2, u3, u4, u5, G (unpack64List [u1, u2, u3, u4, u5]), htags.1, htags.2, ?_, ?_⟩
  · have heq : (((src + 8#64) ↦ₛ unpack64List [u1, u2, u3, u4, u5]) ∗
        (G (unpack64List [u1, u2, u3, u4, u5]) ∗ ((src ↦₆₄ w0) ∗ R))) =
        (words64At src [w0, u1, u2, u3, u4, u5] ∗ G (unpack64List [u1, u2, u3, u4, u5]) ∗ R) := by
      rw [← words64At_eq_pointsToBytes (src + 8#64)]; simp only [words64At]; ac_rfl
    rwa [← heq]
  · intro dst; rw [hP dst]
    have hpack : words64At dst [w0, u1, u2, u3, u4, u5] ∗ G (unpack64List [u1, u2, u3, u4, u5]) =
        (dst ↦₆₄ w0) ∗ (((dst + 8#64) ↦ₛ unpack64List [u1, u2, u3, u4, u5]) ∗ G (unpack64List [u1, u2, u3, u4, u5])) := by
      rw [← words64At_eq_pointsToBytes (dst + 8#64)]; simp only [words64At]; ac_rfl
    rw [hpack]; refine sepConj_mono_right (Entails.trans ?_ (hG dst).2)
    unfold RelocBytes; exact Entails.sepExists_right _ (Entails.pure_right hbs (Entails.refl _))

private theorem r3a_speOwnedAt_relocate (A : RustAlloc) (src : BitVec 64) (k : RunDrop.SpeOwned)
    {m : Memory} {R : SepProp} (hm : m ⊨ RunDrop.speOwnedAt A src k ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      w0 + 3#64 ≠ 0#64 ∧ w0 + 2#64 ≠ 0#64 ∧
      (m ⊨ words64At src [w0, w1, w2, w3, w4, w5] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64, words64At dst [w0, w1, w2, w3, w4, w5] ∗ H ⊢ RunDrop.speOwnedAt A dst k) := by
  cases k with
  | badKemKeyType =>
    exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (i := 31) (by decide)) hm
  | badKemKeyLength =>
    exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (i := 33) (by decide)) hm
  | plain i hi =>
    exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (by unfold RunDrop.PlainSpeTag RunDrop.plainSpeTags at hi; simp at hi; omega)) hm
  | withString i hi =>
    exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.sepEx fun bs => r3a_vecU8R A (fun b => b + 8#64) bs) (Reloc.region (fun b => b + 0x20#64) 16)) (r3a_speWord_ne_tags (by unfold RunDrop.StrSpeTag RunDrop.strSpeTags at hi; simp at hi; omega)) hm
  | untrustedIdentity addr =>
    have hclone : Reloc (fun b => b + 8#64) 32 (fun b => addrCloneAt A (b + 8#64) addr) := by
      unfold addrCloneAt
      exact Reloc.sep (r3a_vecU8R A (fun b => b + 8#64) addr.name) (Reloc.sep (Reloc.pt8 (fun b => b + 8#64 + 0x18#64) addr.device) (Reloc.region (fun b => b + 8#64 + 0x19#64) 7))
    exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep hclone (Reloc.region (fun b => b + 0x28#64) 8)) (r3a_speWord_ne_tags (i := speUntrustedIdentity) (by decide)) hm
  | sessionNotFound addr op =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, vecU8] at hm
    rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
    obtain ⟨cap, hm⟩ := hm
    rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
    obtain ⟨ptr, hm⟩ := hm
    have hsplit : ∀ b : BitVec 64, ((vecU8At A b cap ptr addr.name ∗ (b + 0x18#64) ↦₈ addr.device ∗ memRegion (b + 0x19#64) 7) ∗ strRefAt (b + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op)) = ⌜addr.name.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ ((b ↦₆₄ cap) ∗ (Reloc.vecU8Tail A b cap ptr addr.name ∗ ((b + 0x18#64) ↦₈ addr.device) ∗ memRegion (b + 0x19#64) 7 ∗ strRefAt (b + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op))) := fun b => by rw [Reloc.vecU8At_split_cap]; ac_rfl
    rw [hsplit src, sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨hbounds, hm_body⟩
    have htail : Reloc (fun b => b + 8#64) 40 (fun b => Reloc.vecU8Tail A b cap ptr addr.name ∗ ((b + 0x18#64) ↦₈ addr.device) ∗ memRegion (b + 0x19#64) 7 ∗ strRefAt (b + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op)) := Reloc.sep (Reloc.vecU8TailR A (fun b => b) cap ptr addr.name) (Reloc.sep (Reloc.pt8 (fun b => b + 0x18#64) addr.device) (Reloc.sep (Reloc.region (fun b => b + 0x19#64) 7) (r3a_strRefR (fun b => b + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op))))
    obtain ⟨w0, w1, w2, w3, w4, w5, H, h3, h2, hmsrc, hmdst⟩ := r3a_word_tail_reloc (fun _ => rfl) htail (r3a_cap_ne_tags hbounds.2.1) hm_body
    refine ⟨w0, w1, w2, w3, w4, w5, H, h3, h2, hmsrc, fun dst => ?_⟩
    refine Entails.trans (hmdst dst) ?_
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, vecU8]
    refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_intro ptr))))
    rw [hsplit dst]; exact Entails.pure_right hbounds (Entails.refl _)
  | proto fnName e =>
    cases e with
    | invalidState =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.sepEx fun bs => r3a_vecU8R A (fun b => b + 8#64) bs) (r3a_strRefR (fun b => b + 0x20#64) fnName)) (r3a_speWord_ne_tags (i := 1) (by decide)) hm
    | ciphertextMessageTooShort n =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt64 (fun b => b + 8#64) (BitVec.ofNat 64 n)) (Reloc.region (fun b => b + 16#64) 32)) (r3a_speWord_ne_tags (i := 3) (by decide)) hm
    | legacyCiphertextVersion v =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt8 (fun b => b + 8#64) v) (Reloc.region (fun b => b + 9#64) 39)) (r3a_speWord_ne_tags (i := 4) (by decide)) hm
    | unrecognizedCiphertextVersion v =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt8 (fun b => b + 8#64) v) (Reloc.region (fun b => b + 9#64) 39)) (r3a_speWord_ne_tags (i := 5) (by decide)) hm
    | invalidProtobufEncoding =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (i := 2) (by decide)) hm
    | noKeyTypeIdentifier =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (i := 7) (by decide)) hm
    | badKeyType t =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt8 (fun b => b + 8#64) t) (Reloc.region (fun b => b + 9#64) 39)) (r3a_speWord_ne_tags (i := 8) (by decide)) hm
    | badKeyLength n =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt64 (fun b => b + 8#64) (BitVec.ofNat 64 n)) (Reloc.region (fun b => b + 16#64) 32)) (r3a_speWord_ne_tags (i := 9) (by decide)) hm
    | invalidKeyAgreement =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.region (fun b => b + 8#64) 40) (r3a_speWord_ne_tags (i := 10) (by decide)) hm
    | invalidSessionStructure r =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (r3a_strRefR (fun b => b + 8#64) (invalidSessionStructureStr r)) (Reloc.region (fun b => b + 24#64) 24)) (r3a_speWord_ne_tags (i := 20) (by decide)) hm
    | duplicatedMessage i c =>
      exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.pt32 (fun b => b + 8#64) i) (Reloc.sep (Reloc.pt32 (fun b => b + 12#64) c) (Reloc.region (fun b => b + 16#64) 32))) (r3a_speWord_ne_tags (i := 23) (by decide)) hm
    | invalidMessage t r =>
      have h := r3a_speWord_ne_tags (i := 24) (by decide)
      cases r with
      | tooFarInFuture =>
        exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (r3a_vecU8R A (fun b => b + 8#64) tooFarInFutureStr) (Reloc.sep (Reloc.pt8 (fun b => b + 32#64) (msgTypeByte t)) (Reloc.region (fun b => b + 33#64) 15))) h hm
      | macFailed =>
        exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (r3a_vecU8R A (fun b => b + 8#64) macFailedStr) (Reloc.sep (Reloc.pt8 (fun b => b + 32#64) (msgTypeByte t)) (Reloc.region (fun b => b + 33#64) 15))) h hm
      | pqRatchet =>
        exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.sepEx fun bs => r3a_vecU8R A (fun b => b + 8#64) bs) (Reloc.sep (Reloc.pt8 (fun b => b + 32#64) (msgTypeByte t)) (Reloc.region (fun b => b + 33#64) 15))) h hm
      | badCiphertext =>
        exact r3a_word_tail_reloc (fun _ => rfl) (Reloc.sep (Reloc.sepEx fun bs => r3a_vecU8R A (fun b => b + 8#64) bs) (Reloc.sep (Reloc.pt8 (fun b => b + 32#64) (msgTypeByte t)) (Reloc.region (fun b => b + 33#64) 15))) h hm
      | decryptionFailed =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt] at hm
        have hf : m ⊨ ⌜False⌝ ∗ ((src ↦₆₄ speWord 24) ∗ ((src + asm64% speInvalidMessageTypeOff) ↦₈ msgTypeByte t) ∗ memRegion (src + asm64% (speInvalidMessageTypeOff + 1)) (asm% (speSize - (speInvalidMessageTypeOff + 1))) ∗ R) := Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
        rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
    | panic => exact False.elim (not_satisfies_false_sepConj hm)

private theorem r3a_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hm⟩ := hm; exact h x R hm hL

private theorem r3a_sepWPp_pure_left {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s F Q Qp oom) : SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact h hm.1 R hm.2 hL

private theorem r3a_sepWPp_bind {prog : Program} {ret : BitVec 64} {s : State} {A0 F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ R, (s.mem ⊨ A0 ∗ (F ∗ R)) → ∃ A1, (s.mem ⊨ A1 ∗ (F ∗ R)) ∧ SepWPp prog ret s (A1 ∗ F) Q Qp oom) :
    SepWPp prog ret s (A0 ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc] at hm
  obtain ⟨_, hm1, hwp⟩ := h R hm; rw [← sepConj_assoc] at hm1; exact hwp R hm1 hL

private theorem r3a_tw (a : BitVec 64) (ws : List (BitVec 64)) : Tails.words64At a ws = words64At a ws := by
  induction ws generalizing a with
  | nil => rfl
  | cons _ _ ih => simp only [Tails.words64At, words64At, ih]

private theorem r3a_open_words (n : Nat) (a : BitVec 64) {m : Memory} {Q : SepProp}
    (hm : m ⊨ memRegion a (8 * n) ∗ Q) (hle : 8 * n ≤ 2 ^ 64 := by decide) :
    ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ Q) := r3a_memRegion_words n a hle hm

private theorem r3a_words_mem_aux : ∀ (ws : List (BitVec 64)) (a : BitVec 64),
    ws.length ≤ 1024 → words64At a ws ⊢ memRegion a (8 * ws.length)
  | [], a, _ => by
    simpa only [List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero, words64At] using Entails.refl emp
  | w :: ws, a, hle => by
    rw [List.length_cons] at hle
    have h8 : 8 + 8 * ws.length ≤ 2 ^ 64 := Nat.le_trans (by omega : 8 + 8 * ws.length ≤ 16384) (by decide : 16384 ≤ 2 ^ 64)
    have hsplit : memRegion a (8 * (w :: ws).length) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * ws.length) := by
      rw [List.length_cons, show 8 * (ws.length + 1) = 8 + 8 * ws.length by omega]
      exact ProofLib.memRegion_split a 8 (8 * ws.length) h8
    rw [hsplit]
    exact sepConj_mono (pointsTo64_entails_memRegion a w) (r3a_words_mem_aux ws (a + 8#64) (by omega))

private theorem r3a_words_to_memRegion (ws : List (BitVec 64)) (a : BitVec 64) (n : Nat)
    (hn : 8 * ws.length = n := by rfl) (hle : ws.length ≤ 1024 := by simp) :
    words64At a ws ⊢ memRegion a n := hn ▸ r3a_words_mem_aux ws a hle

private theorem r3a_rejoin_1d0 (fsp w0 w1 : BitVec 64) :
    words64At (fsp + 0x1d0#64) [w0, w1] ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ⊢
      memRegion fsp 0x208 := by
  refine Entails.trans (sepConj_mono_left (r3a_words_to_memRegion [w0, w1] (fsp + 0x1d0#64) 16)) ?_
  have h1 : memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1d0#64) 16 = memRegion fsp 0x1e0 :=
    (ProofLib.memRegion_split fsp 0x1d0 16 (by decide)).symm
  have h2 : memRegion fsp 0x1e0 ∗ memRegion (fsp + 0x1e0#64) 40 = memRegion fsp 0x208 :=
    (ProofLib.memRegion_split fsp 0x1e0 40 (by decide)).symm
  rw [← h2, ← h1]; exact Entails.of_eq (by ac_rfl)

private theorem r3a_word_to_devPad (a w : BitVec 64) {dev : BitVec 8} (hdev : w.setWidth 8 = dev) :
    (a ↦₆₄ w) ⊢ (a ↦₈ dev) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes]; simp only [unpack64]
  have hb0 : w.extractLsb' 0 8 = dev := by
    subst hdev; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [hb0, pointsToBytes_cons]; exact sepConj_mono_right (pointsToBytes_entails_memRegion (a + 1#64) _)

private theorem r3a_addrUpper_relocate (src : BitVec 64) (g : AddrGhost) {m : Memory} {R : SepProp}
    (hm : m ⊨ addrUpperAt src g ∗ R) :
    ∃ (u1 : BitVec 64) (H : SepProp),
      (m ⊨ words64At src [BitVec.ofNat 64 g.name.bytes.length, u1] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64, words64At dst [BitVec.ofNat 64 g.name.bytes.length, u1] ∗ H ⊢ addrUpperAt dst g) := by
  obtain ⟨G, hG⟩ : Reloc (fun b => b + 8#64) 8 (fun b => ((b + 8#64) ↦₈ g.device) ∗ memRegion (b + 9#64) 7) :=
    Reloc.sep (Reloc.pt8 (fun b => b + 8#64) g.device) (Reloc.region (fun b => b + 9#64) 7)
  unfold addrUpperAt at hm
  have hm1 := Satisfies.mono (sepConj_mono_left (hG src).1)
    (Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm :
      m ⊨ (((src + 8#64) ↦₈ g.device) ∗ memRegion (src + 9#64) 7) ∗ (((src ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗ R))
  unfold RelocBytes at hm1; rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨bs, hm1⟩ := hm1; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨hbs, hm1⟩
  obtain ⟨ws, hws_len, rfl⟩ := exists_unpack64List 1 (by omega : bs.length = 8 * 1)
  rcases ws with _ | ⟨u1, _ | _⟩ <;> try (simp at hws_len; done)
  refine ⟨u1, G (unpack64List [u1]), ?_, ?_⟩
  · have heq : (((src + 8#64) ↦ₛ unpack64List [u1]) ∗ (G (unpack64List [u1]) ∗ ((src ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ R))) =
        (words64At src [BitVec.ofNat 64 g.name.bytes.length, u1] ∗ G (unpack64List [u1]) ∗ R) := by
      rw [← words64At_eq_pointsToBytes (src + 8#64)]; simp only [words64At]; ac_rfl
    rwa [← heq]
  · intro dst; unfold addrUpperAt
    have hpack : words64At dst [BitVec.ofNat 64 g.name.bytes.length, u1] ∗ G (unpack64List [u1]) =
        (dst ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ (((dst + 8#64) ↦ₛ unpack64List [u1]) ∗ G (unpack64List [u1])) := by
      rw [← words64At_eq_pointsToBytes (dst + 8#64)]; simp only [words64At]; ac_rfl
    rw [hpack]; refine sepConj_mono_right (Entails.trans ?_ (hG dst).2)
    unfold RelocBytes; exact Entails.sepExists_right _ (Entails.pure_right hbs (Entails.refl _))

private theorem r3a_addrNameHeap_cap_lt (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap; refine Entails.pure_left fun h => ?_
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

private theorem r3a_addrNameHeap_to_owned (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  unfold addrNameHeap ownedBytes; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  exact Entails.pure_right ⟨rfl, hle, hlt, hne⟩ (Entails.refl _)

private theorem r3a_owned_to_addrNameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) (dev : BitVec 8) :
    ownedBytes A cap ptr len bs ⊢ ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ addrNameHeap A ⟨⟨cap, ptr, bs⟩, dev⟩ := by
  unfold ownedBytes addrNameHeap; refine Entails.pure_left fun ⟨hlen, hle, hlt, hne⟩ => ?_
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private theorem r3a_pack_peer (A : RustAlloc) (a : BitVec 64) (peerV : AddrV)
    (w1 w2 w3 w4 : BitVec 64) (hdev : w4.setWidth 8 = peerV.device) :
    words64At a [w1, w2, w3, w4] ∗ ownedBytes A w1 w2 w3 peerV.name ⊢
      protocolAddressAt A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩ a := by
  refine Entails.trans (sepConj_mono_right (r3a_owned_to_addrNameHeap A w1 w2 w3 peerV.name peerV.device)) ?_
  rw [sepConj_comm, sepConj_assoc]; apply Entails.pure_left; rintro rfl
  rw [protocolAddressAt_eq_parts A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩ a]
  have hd24 : ((a + 24#64) ↦₆₄ w4) ⊢ ((a + 24#64) ↦₈ peerV.device) ∗ memRegion (a + 25#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r3a_word_to_devPad (a + 24#64) w4 hdev
  dsimp only [addrUpperAt, words64At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.trans
    (Entails.of_eq (show _ = ((a + 24#64) ↦₆₄ w4) ∗ ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 peerV.name.length) ∗ addrNameHeap A ⟨⟨w1, w2, peerV.name⟩, peerV.device⟩) by ac_rfl))
    (Entails.trans (sepConj_mono_left hd24) (Entails.of_eq (by ac_rfl)))


private theorem r3a_vecU8_open (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢ ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ V : SepProp,
      ⌜cap.toNat < 2 ^ 63 ∧ (∀ dst : BitVec 64, words64At dst [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V ⊢ vecU8 A dst bs)⌝ ∗
      words64At a [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V := by
  unfold vecU8
  apply Entails.sepExists_mono; intro cap; apply Entails.sepExists_mono; intro ptr
  let V : SepProp := ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
    if cap = 0 then emp else memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗ ptr ↦ₛ bs ∗ A.live ptr cap.toNat 1
  have hpure : V ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ V := by
    dsimp only [V]; refine Entails.pure_left fun h => ?_
    exact Entails.pure_right h.2.2 (Entails.pure_right h (Entails.refl _))
  have hclose : ∀ dst : BitVec 64, words64At dst [cap, ptr, BitVec.ofNat 64 bs.length] ∗ V ⊢ vecU8 A dst bs := by
    intro dst; unfold vecU8
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    dsimp only [vecU8At, vecAt, vecHeader, V, words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
  refine Entails.sepExists_right V ?_
  have heq : vecU8At A a cap ptr bs = V ∗ words64At a [cap, ptr, BitVec.ofNat 64 bs.length] := by
    dsimp only [vecU8At, vecAt, vecHeader, V, words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; ac_rfl
  rw [heq]; refine Entails.trans (sepConj_mono_left hpure) ?_; rw [sepConj_assoc]
  exact Entails.pure_left fun hlt => Entails.pure_right ⟨hlt, hclose⟩ (Entails.of_eq (by ac_rfl))

private theorem r3a_slotOut_ok {ans : SlotAns Bytes} {g' : StoresGhost} {out : Bytes} {s sf : State} (h : slotOut ans g' (.ok out) s sf) :
    ans = some (some (g', out)) ∧ ∀ pw ∈ g'.writes, cliWrOk pw.1 := h.2.2
private theorem r3a_slotOut_err {g : RunCall} {ans : SlotAns Bytes} {g' : StoresGhost} {err : ApiError AddrVal Unit} {s sf : State}
    (ha : g.a = finish ans id) (h : slotOut ans g' (.error err) s sf) : err ≠ .store () ∧ g.a = some none :=
  ⟨RunProofs.slotOut_err_ne_store h, by rw [ha, h.2.2]; rfl⟩
private theorem r3a_hist_of_slotTrace {i : Inputs} {s0 s sf : State} (htr0 : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) (hst : slotTrace s sf) : s0.trace <+: sf.trace ∧ RunHistOk i s0 sf :=
  ⟨htr0.trans hst.1, hst.2.1.trans hfs, hst.2.2.trans hout⟩
private theorem r3a_files_eq [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {s sf : State}
    (hh : RunHooksPlaced A H) (hsteps : Steps (runProgPlaced H) s sf) (htr : sf.trace = s.trace) : sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps (htr.trans (List.append_nil _).symm) NoFsEv.nil
private theorem r3a_reg {r : Reg} {v : BitVec 64} {s s1 : State} (h0 : s.readReg64 r = v)
    (h1 : s1.readReg64 r = s.readReg64 r := by first | rfl | simp only [arm64_norm]) : s1.readReg64 r = v := h1.trans h0
private theorem r3a_res_split (res : BitVec 64) : memRegion res runResSize = (∃∗ w : BitVec 64, res ↦₆₄ w) ∗ memRegion (res + 8#64) (runResSize - 8) := by
  conv_lhs => rw [show runResSize = 8 + (runResSize - 8) from rfl]
  rw [ProofLib.memRegion_split res 8 (runResSize - 8) (by decide), ProofLib.memRegion_eight]
private theorem r3a_hist_step [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {i : Inputs} {s0 sm sf : State}
    (hh : RunHooksPlaced A H) (hsteps : Steps (runProgPlaced H) sm sf) (htr : sf.trace = sm.trace) (hh0 : RunHistOk i s0 sm) : RunHistOk i s0 sf :=
  ⟨(r3a_files_eq hh hsteps htr).trans hh0.1, htr ▸ hh0.2⟩
private theorem r3a_inRun_step [LibsignalPlacement] {CodeOk : Memory → Prop} {s0 s sf : State} {k k' : Nat} (h : InRunPlaced CodeOk s0 s k)
    (hpc : sf.pc = runPcPlaced k') (hrun : sf.status = .Running) (hsp : sf.sp = s.sp) (hfp : sf.readReg64 .fp = s.readReg64 .fp)
    (hinv : CodeOk sf.mem) (hv : calleeSavedVRegs sf = calleeSavedVRegs s) : InRunPlaced CodeOk s0 sf k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩
private theorem r3a_step_state [LibsignalPlacement] {CodeOk : Memory → Prop} {s s1 : State} (_ : CodeOk s1.mem)
    (htr : s1.trace = s.trace := by first | rfl | simp only [arm64_norm])
    (hfs : s1.fs.files = s.fs.files := by first | rfl | simp only [arm64_norm])
    (hsp : s1.sp = s.sp := by first | rfl | simp only [arm64_norm]) :
    s1.trace = s.trace ∧ s1.fs.files = s.fs.files ∧ s1.sp = s.sp := ⟨htr, hfs, hsp⟩
private theorem r3a_hist_eq {i : Inputs} {s0 s s' : State} (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files) (h : RunHistOk i s0 s) :
    RunHistOk i s0 s' := ⟨hfs.trans h.1, htr ▸ h.2⟩
private def r3a_restFrame (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp
private theorem r3a_locals_empty_rest (fsp : BitVec 64) :
    runLocals fsp [] = memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗
      memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp := by
  rw [r3a_frame_eq fsp]; unfold r3a_restFrame; ac_rfl
private theorem r3a_locals_join_rest (A : RustAlloc) (fsp : BitVec 64) (out : Bytes) :
    runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) out)] = vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x220#64) 32 ∗
      memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp := by
  rw [r3a_frame_join_eq A fsp out]; unfold r3a_restFrame; ac_rfl
private theorem r3a_addrSlots_to_memRegion (a cap ptr : BitVec 64) (g : AddrGhost) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ addrUpperAt (a + 16#64) g ⊢ memRegion a 32 := by
  have h1 : memRegion a 8 ∗ memRegion (a + 8#64) 8 = memRegion a 16 := (ProofLib.memRegion_split a 8 8 (by decide)).symm
  have h2 : memRegion a 16 ∗ memRegion (a + 16#64) 16 = memRegion a 32 := (ProofLib.memRegion_split a 16 16 (by decide)).symm
  rw [← h2, ← h1, ← sepConj_assoc]
  exact sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)) (addrUpperAt_entails_memRegion _ _)
private theorem r3a_protoAddr_free_peer (A : RustAlloc) (a : BitVec 64) (g : AddrGhost) :
    protocolAddressAt A g a ⊢ (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrUpperAt (a + 16#64) g ∗
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  rw [protocolAddressAt_eq_parts A g a]; exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (r3a_addrNameHeap_to_owned A g)))
private theorem r3a_protoAddr_free_me (A : RustAlloc) (a : BitVec 64) (g : AddrGhost) :
    protocolAddressAt A g a ⊢ memRegion a 32 ∗ ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  refine Entails.trans (r3a_protoAddr_free_peer A a g) ?_
  refine Entails.trans (Entails.of_eq (show _ = ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrUpperAt (a + 16#64) g) ∗
    ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes by ac_rfl)) ?_
  exact sepConj_mono_left (r3a_addrSlots_to_memRegion a g.name.cap g.name.ptr g)


private theorem r3a_call_dealloc [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {s0 s : State} {sub retOff : Nat} {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64) (hcap : cap ≠ 0) (hinv : CodeOk s.mem) (hpc : s.pc = lsρ lsRustDeallocSymCli) (hrun : s.status = .Running) (hsp_al : s.spAligned = true) (hlr : s.readReg64 Reg.lr = runPcPlaced retOff) (hsp : s.sp = runFsp s0) (hfp : s.readReg64 .fp = s0.sp - 0x60#64) (hv : calleeSavedVRegs s = calleeSavedVRegs s0) (hal0 : s0.spAligned = true) (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap) (hx2 : s.readReg64 .x2 = 1#64) (hk : ∀ sf : State, InRunPlaced CodeOk s0 sf retOff → CalleeSavedPreserved s sf → sf.trace = s.trace → sf.fs.files = s.fs.files → SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf (A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (ownedBytes A cap ptr len bs ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hda := dealloc_lscro_of_cli (callerProg := runProgPlaced H) (i := 579) hh.alloc
  refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A hcap)) ?_; rw [sepConj_assoc, sepConj_assoc]
  refine r3a_sepWPp_pure_left (F := A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) fun hlay => ?_
  have hsp_split := stackAt_split_ge (runFsp s0) hext hsub64; rw [hsp_split]
  refine r3a_call (ptr, cap.toNat, 1) hda hinv hpc hrun hsp_al hlr (F := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F) ?_ (hnext := fun sf hsteps hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]; rw [hsp]; simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, by simp [hx1], by simp [hx2], hlay⟩ (Entails.of_eq (by ac_rfl))
  · dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]; simp only [sepConj_assoc]
    refine SepWPp.pure_left fun htr_f => ?_
    have hfs_f : sf.fs.files = s.fs.files := r3a_files_eq hh hsteps htr_f
    have hcs := r3a_cs_regs hcsm
    have hin : InRunPlaced CodeOk s0 sf retOff := ⟨hpcm, hrunm, hspm.trans hsp, hcs.2.2.2.2.2.1.trans hfp, hinv_f, hcs.2.2.2.2.2.2.trans hv, hal0⟩
    refine sepWPp_weaken_pre ?_ (hk sf hin hcsm htr_f hfs_f); rw [hsp]
    have hmerge : A.pool ∗ (stackAt (runFsp s0) extHookStack ∗ (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F)) = A.pool ∗ (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ stackAt (runFsp s0) extHookStack) ∗ F := by ac_rfl
    rw [hmerge, hsp_split.symm]; exact Entails.refl _
set_option maxHeartbeats 1600000 in
private theorem r3a_tail_peer_reject [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 4104) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine sepWPp_weaken_pre (P' := ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool ∗ stackAt fsp sub ∗ tailF) (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A (fsp + 0x220#64) peerG)) (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 4104 := hs.pc; change s.pc = (blkPl_579).base + 4104#64 at hpc
  have hrun : s.status = .Running := hs.run; have hsp_al : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose : memRegion (fsp + 0x220#64) 32 ∗ A.pool ∗ stackAt fsp sub ∗ tailF ⊢ rejectMem A g g' .postDispatch s0 resStack := by
    dsimp +zetaDelta only [rejectMem]; rw [r3a_locals_empty_rest (runFsp s0)]; exact Entails.of_eq (by ac_rfl)
  by_cases hcap : peerG.name.cap = 0
  · refine sepWPp_weaken_pre (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A _ _ _)) ?_; rw [emp_sepConj]
    apply r3a_seq (mid := runPcPlaced 0x2c7c) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]
    rw [hcap] at h32 ⊢; wp_steps
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]); intro hinv'
    obtain ⟨htr', hfs', _⟩ := r3a_step_state (s := s) hinv'
    exact sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (sepConj_mono_left h32) hclose)) (hrej _ g' .postDispatch ⟨r3a_inRun_step hs (by simp only [runPcPlaced_eq, RejectKind.pcOff, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv' (by simp only [arm64_norm]), r3a_reg hx19, (fun h => nomatch h), htr' ▸ htr, r3a_hist_eq htr' hfs' hhist, hans⟩)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_weaken_pre (Entails.of_eq (show _ = ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ (ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool ∗ stackAt fsp sub ∗ tailF) by ac_rfl)) ?_
    apply r3a_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv_da
    refine sepWPp_weaken_pre (P' := ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ (memRegion (fsp + 0x220#64) 32 ∗ tailF)) (Entails.trans (Entails.of_eq (show _ = (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG) ∗ (ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ tailF) by ac_rfl)) (Entails.trans (sepConj_mono_left h32) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)))) ?_
    refine r3a_call_dealloc (ptr := peerG.name.ptr) hh hext hsub64 hcap hinv_da (retOff := 0x2c7c) (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hsp_al) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm; have htr_tot : sf.trace = s.trace := htr_f.trans (by simp only [arm64_norm]); have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (by simp only [arm64_norm])
    exact sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hclose) (hrej sf g' .postDispatch ⟨hin_f, hcs.1.trans (r3a_reg hx19), (fun h => nomatch h), htr_tot ▸ htr, r3a_hist_eq htr_tot hfs_tot hhist, hans⟩)


set_option maxHeartbeats 1600000 in
private theorem r3a_tail_me_reject [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 4076) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (_hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tailF : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ anyHeap
  refine sepWPp_weaken_pre (P' := (∃∗ w : BitVec 64, g.res ↦₆₄ w) ∗ (ownedBytes A meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ tailF)) (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A (fsp + 0x260#64) meG)) (by rw [r3a_res_split g.res]; exact Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))) ?_
  refine r3a_sepWPp_exists_left fun _ => ?_
  have hpc : s.pc = runPcPlaced 4076 := hs.pc; change s.pc = (blkPl_579).base + 4076#64 at hpc
  have hrun : s.status = .Running := hs.run; have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hclose : (g.res ↦₆₄ -1#64) ∗ A.pool ∗ stackAt fsp sub ∗ tailF ⊢ protocolAddressAt A peerG (fsp + 0x220#64) ∗ runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool ∗ anyHeap := by
    dsimp +zetaDelta only [runResAt]; exact Entails.of_eq (by ac_rfl)
  by_cases hcap : meG.name.cap = 0
  · refine sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_left (hcap ▸ ownedBytes_zero_entails_emp A _ _ _))) ?_; rw [emp_sepConj]
    apply r3a_seq (mid := runPcPlaced 4104) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]
    rw [hcap] at hx21; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv'
    obtain ⟨htr', hfs', _⟩ := r3a_step_state (s := s) hinv'
    exact sepWPp_weaken_pre hclose (r3a_tail_peer_reject (g' := g') (peerG := peerG) hh hext hsub64 (r3a_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv' (by simp only [arm64_norm])) (r3a_reg hx19) (htr' ▸ htr) (r3a_hist_eq htr' hfs' hhist) hans hrej)
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply r3a_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv_da
    refine sepWPp_weaken_pre (Entails.of_eq (show _ = ownedBytes A meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ ((g.res ↦₆₄ -1#64) ∗ tailF) by ac_rfl)) ?_
    refine r3a_call_dealloc (ptr := meG.name.ptr) hh hext hsub64 hcap hinv_da (retOff := 4104) (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hsp_al) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm; have htr_tot : sf.trace = s.trace := htr_f.trans (by simp only [arm64_norm]); have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (by simp only [arm64_norm])
    exact sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hclose) (r3a_tail_peer_reject (g' := g') (peerG := peerG) hh hext hsub64 hin_f (hcs.1.trans (r3a_reg hx19)) (htr_tot ▸ htr) (r3a_hist_eq htr_tot hfs_tot hhist) hans hrej)
private theorem r3a_drop_spe_call [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {k : RunDrop.SpeOwned} {speAddr : BitVec 64} {sub : Nat} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop} (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (h32 : 32 + extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64) (hinv : CodeOk s.mem) (hpc : s.pc = (blkPl_553).base) (hrun : s.status = .Running) (hsp_al : s.spAligned = true) (hlr : s.readReg64 Reg.lr = runPcPlaced 4076) (hsp : s.sp = runFsp s0) (hfp : s.readReg64 .fp = s0.sp - 0x60#64) (hv : calleeSavedVRegs s = calleeSavedVRegs s0) (hal0 : s0.spAligned = true) (hx0 : s.readReg64 .x0 = speAddr) (hk : ∀ sf : State, Steps (runProgPlaced H) s sf → InRunPlaced CodeOk s0 sf 4076 → CalleeSavedPreserved s sf → sf.trace = s.trace → SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf (memRegion speAddr 48 ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (RunDrop.speOwnedAt A speAddr k ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hd := hdrop sub h32 hsub64
  refine r3a_call ⟨speAddr, k⟩ hd hinv hpc hrun hsp_al hlr (F := F) ?_ (hnext := fun sf hsteps hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]; rw [hsp]; simp only [sepConj_assoc]; exact Entails.pure_right hx0 (Entails.of_eq (by ac_rfl))
  · dsimp only [RunDrop.dropSpeOwnedSpec]; simp only [sepConj_assoc]
    refine SepWPp.pure_left fun htr_f => ?_
    have hcs := r3a_cs_regs hcsm; rw [hsp]
    exact hk sf hsteps ⟨hpcm, hrunm, hspm.trans hsp, hcs.2.2.2.2.2.1.trans hfp, hinv_f, hcs.2.2.2.2.2.2.trans hv, hal0⟩ hcsm htr_f


set_option maxHeartbeats 1600000 in
private theorem r3a_accept_peer [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG : AddrGhost} {out : Bytes} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 3552) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some (some (namedWrites g'.writes, out))) (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ vecU8 A (runFsp s0 + 0x208#64) out ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine sepWPp_weaken_pre (P' := ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool ∗ stackAt fsp sub ∗ okTail) (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_peer A (fsp + 0x220#64) peerG)) (by rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3552 := hs.pc; change s.pc = (blkPl_579).base + 3552#64 at hpc
  have hrun : s.status = .Running := hs.run; have hsp_al : s.spAligned = true := hs.spAligned_cur
  have h32 : ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG ⊢ memRegion (fsp + 0x220#64) 32 := by
    rw [hs.sp]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r3a_addrSlots_to_memRegion (fsp + 0x220#64) peerG.name.cap peerG.name.ptr peerG
  have hclose_join : memRegion (fsp + 0x220#64) 32 ∗ A.pool ∗ stackAt fsp sub ∗ okTail ⊢ joinMem A g g' out s0 resStack := by
    dsimp +zetaDelta only [joinMem]; rw [r3a_locals_join_rest A (runFsp s0) out]; exact Entails.of_eq (by ac_rfl)
  by_cases hpcap : peerG.name.cap = 0
  · refine sepWPp_weaken_pre (sepConj_mono_left (hpcap ▸ ownedBytes_zero_entails_emp A _ _ _)) ?_; rw [emp_sepConj]
    apply r3a_seq (mid := runPcPlaced 0xf8c) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]
    rw [hpcap] at h32 ⊢; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv_j
    obtain ⟨htr_j, hfs_j, hsp_j⟩ := r3a_step_state (s := s) hinv_j
    exact sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (sepConj_mono_left h32) hclose_join)) (hjoin _ g' out ⟨r3a_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]) hsp_j (by simp only [arm64_norm]) hinv_j (by simp only [arm64_norm]), r3a_reg hx19, r3a_reg hx20, htr_j ▸ htr, r3a_hist_eq htr_j hfs_j hhist, hans, hwr⟩)
  · have hpbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpcap
    refine sepWPp_weaken_pre (Entails.of_eq (show _ = ((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ (ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ addrUpperAt (fsp + 0x230#64) peerG ∗ A.pool ∗ stackAt fsp sub ∗ okTail) by ac_rfl)) ?_
    apply r3a_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]); intro hinv_da
    refine sepWPp_weaken_pre (P' := ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ (memRegion (fsp + 0x220#64) 32 ∗ okTail)) (Entails.trans (Entails.of_eq (show _ = (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗ addrUpperAt (fsp + 0x230#64) peerG) ∗ (ownedBytes A peerG.name.cap peerG.name.ptr (BitVec.ofNat 64 peerG.name.bytes.length) peerG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ okTail) by ac_rfl)) (Entails.trans (sepConj_mono_left h32) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)))) ?_
    refine r3a_call_dealloc (ptr := peerG.name.ptr) hh hext hsub64 hpcap hinv_da (retOff := 0xf8c) (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hs.spAligned_cur) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm; have htr_tot : sf.trace = s.trace := htr_f.trans (by simp only [arm64_norm]); have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (by simp only [arm64_norm])
    exact sepWPp_weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hclose_join) (hjoin sf g' out ⟨hin_f, hcs.1.trans (r3a_reg hx19), hcs.2.1.trans (r3a_reg hx20), htr_tot ▸ htr, r3a_hist_eq htr_tot hfs_tot hhist, hans, hwr⟩)
set_option maxHeartbeats 1600000 in
private theorem r3a_accept_me [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 3532) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some (some (namedWrites g'.writes, out))) (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ vecU8 A (runFsp s0 + 0x208#64) out ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ anyHeap) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let okTail : SepProp := protocolAddressAt A peerG (fsp + 0x220#64) ∗ vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap
  refine sepWPp_weaken_pre (P' := ownedBytes A meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ okTail) (Entails.trans (sepConj_mono_left (r3a_protoAddr_free_me A (fsp + 0x260#64) meG)) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))) ?_
  have hpc : s.pc = runPcPlaced 3532 := hs.pc; change s.pc = (blkPl_579).base + 3532#64 at hpc; have hrun : s.status = .Running := hs.run
  have hclose_peer : A.pool ∗ stackAt fsp sub ∗ okTail ⊢ protocolAddressAt A peerG (fsp + 0x220#64) ∗ A.pool ∗ stackAt fsp sub ∗ vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x260#64) 32 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap := Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)
  by_cases hmcap : meG.name.cap = 0
  · refine sepWPp_weaken_pre (sepConj_mono_left (hmcap ▸ ownedBytes_zero_entails_emp A _ _ _)) ?_; rw [emp_sepConj]
    apply r3a_seq (mid := runPcPlaced 3552) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]
    rw [hmcap] at hx21; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv'
    obtain ⟨htr', hfs', hsp'⟩ := r3a_step_state (s := s) hinv'
    exact sepWPp_weaken_pre hclose_peer (r3a_accept_peer (g' := g') (peerG := peerG) (out := out) hh hext hsub64 (r3a_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]) hsp' (by simp only [arm64_norm]) hinv' (by simp only [arm64_norm])) (r3a_reg hx19) (r3a_reg hx20) (htr' ▸ htr) (r3a_hist_eq htr' hfs' hhist) hans hwr hjoin)
  · have hmbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hmcap
    apply r3a_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]); intro hinv_da
    refine sepWPp_weaken_pre (P' := ownedBytes A meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes ∗ A.pool ∗ stackAt fsp sub ∗ okTail) (Entails.refl _) ?_
    refine r3a_call_dealloc (ptr := meG.name.ptr) hh hext hsub64 hmcap hinv_da (retOff := 3552) (by simp only [lsRustDeallocSymCli, lsρ, arm64_norm, *]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hs.spAligned_cur) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) fun sf hin_f hcsm htr_f hfs_f => ?_
    have hcs := r3a_cs_regs hcsm; have htr_tot : sf.trace = s.trace := htr_f.trans (by simp only [arm64_norm]); have hfs_tot : sf.fs.files = s.fs.files := hfs_f.trans (by simp only [arm64_norm])
    exact sepWPp_weaken_pre hclose_peer (r3a_accept_peer (g' := g') (peerG := peerG) (out := out) hh hext hsub64 hin_f (hcs.1.trans (r3a_reg hx19)) (hcs.2.1.trans (r3a_reg hx20)) (htr_tot ▸ htr) (r3a_hist_eq htr_tot hfs_tot hhist) hans hwr hjoin)


set_option maxHeartbeats 1600000 in
private theorem r3a_accept_tail [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {out : Bytes} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 3476) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some (some (namedWrites g'.writes, out))) (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (apiDecResultAt A (runFsp s0 + 0x320#64) (.ok out) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let joinBase : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_frameGaps fsp ∗ anyHeap
  dsimp only [apiDecResultAt, vecResultAt, r3a_restFrame]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWPp_weaken_pre (P' := (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ V : SepProp, ⌜cap.toNat < 2 ^ 63 ∧ (∀ dst : BitVec 64, words64At dst [cap, ptr, BitVec.ofNat 64 out.length] ∗ V ⊢ vecU8 A dst out)⌝ ∗ words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗ V) ∗ (memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16 ∗ ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ memRegion (fsp + 0x340#64) 16 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ stackAt fsp sub ∗ A.pool ∗ joinBase)) (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (r3a_vecU8_open A (runFsp s0 + 0x328#64) out)))) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))) ?_
  refine r3a_sepWPp_exists_left fun cap => r3a_sepWPp_exists_left fun ptr => r3a_sepWPp_exists_left fun V => ?_
  rw [sepConj_assoc, sepConj_assoc]; refine r3a_sepWPp_pure_left fun ⟨_hcap_lt, hvec_close⟩ => ?_
  let keepF : SepProp := words64At (fsp + 0x328#64) [cap, ptr, BitVec.ofNat 64 out.length] ∗ ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗ V ∗ memRegion (fsp + 0x340#64) 16 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ stackAt fsp sub ∗ A.pool ∗ joinBase
  refine r3a_sepWPp_bind (A0 := memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x380#64) 16) (F := keepF) ?_ |> sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
  intro R hm; rw [sepConj_assoc] at hm
  obtain ⟨ws208, hlen208, hm⟩ := r3a_open_words 3 (fsp + 0x208#64) hm
  rcases ws208 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | _⟩⟩⟩ <;> try (simp at hlen208; done)
  obtain ⟨ws380, hlen380, hm⟩ := r3a_open_words 2 (fsp + 0x380#64) (Q := words64At (fsp + 0x208#64) [d0, d1, d2] ∗ (keepF ∗ R)) (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws380 with _ | ⟨u0, _ | ⟨u1, _ | _⟩⟩ <;> try (simp at hlen380; done)
  refine ⟨words64At (fsp + 0x208#64) [d0, d1, d2] ∗ words64At (fsp + 0x380#64) [u0, u1], Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 3476 := hs.pc; change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run; have _hsp_al : s.spAligned = true := hs.spAligned_cur
  have hneq1 : (cap + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hneq2 : (cap == -1#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hstepF : (words64At (fsp + 0x208#64) [d0, d1, d2] ∗ words64At (fsp + 0x380#64) [u0, u1]) ∗ keepF = (((s.sp + 0x320#64) ↦₆₄ -2#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗ ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ ((s.sp + 0x380#64) ↦₆₄ u0) ∗ ((s.sp + 0x388#64) ↦₆₄ u1) ∗ ((s.sp + 0x208#64) ↦₆₄ d0) ∗ ((s.sp + 0x210#64) ↦₆₄ d1) ∗ ((s.sp + 0x218#64) ↦₆₄ d2)) ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ stackAt fsp sub ∗ A.pool ∗ joinBase) := by
    dsimp only [keepF, okTagVec, words64At]; rw [hs.sp]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; ac_rfl
  rw [hstepF]
  apply r3a_seq (mid := runPcPlaced 3532) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv1
  obtain ⟨htr1, hfs1, hsp1⟩ := r3a_step_state (s := s) hinv1
  have hpack_slots : (((s.sp + 0x320#64) ↦₆₄ -2#64) ∗ ((s.sp + 0x328#64) ↦₆₄ cap) ∗ ((s.sp + 0x330#64) ↦₆₄ ptr) ∗ ((s.sp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ ((s.sp + 0x380#64) ↦₆₄ ptr) ∗ ((s.sp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ ((s.sp + 0x208#64) ↦₆₄ cap) ∗ ((s.sp + 0x210#64) ↦₆₄ ptr) ∗ ((s.sp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length)) ∗ (V ∗ memRegion (fsp + 0x340#64) 16 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ stackAt fsp sub ∗ A.pool ∗ joinBase) ⊢ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ A.pool ∗ stackAt fsp sub ∗ vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ anyHeap := by
    rw [hs.sp]
    have hv208 : ((fsp + 0x208#64) ↦₆₄ cap) ∗ ((fsp + 0x210#64) ↦₆₄ ptr) ∗ ((fsp + 0x218#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ V ⊢ vecU8 A (fsp + 0x208#64) out := by
      simpa only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] using hvec_close (fsp + 0x208#64)
    have hm320 : ((fsp + 0x320#64) ↦₆₄ -2#64) ∗ ((fsp + 0x328#64) ↦₆₄ cap) ∗ ((fsp + 0x330#64) ↦₆₄ ptr) ∗ ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗ memRegion (fsp + 0x340#64) 16 ⊢ memRegion (fsp + 0x320#64) 48 := by
      have hw4 := r3a_words_to_memRegion [-2#64, cap, ptr, BitVec.ofNat 64 out.length] (fsp + 0x320#64) 32
      dsimp only [words64At] at hw4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hw4
      have hsp48 : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x340#64) 16 = memRegion (fsp + 0x320#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (ProofLib.memRegion_split (fsp + 0x320#64) 32 16 (by decide)).symm
      rw [← hsp48]; exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hw4)
    have hm380 : ((fsp + 0x380#64) ↦₆₄ ptr) ∗ ((fsp + 0x388#64) ↦₆₄ BitVec.ofNat 64 out.length) ⊢ memRegion (fsp + 0x380#64) 16 := by
      simpa only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] using r3a_words_to_memRegion [ptr, BitVec.ofNat 64 out.length] (fsp + 0x380#64) 16
    dsimp +zetaDelta only [r3a_restFrame] at hv208 hm320 hm380 ⊢
    exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)) (Entails.trans (sepConj_mono hv208 (sepConj_mono hm320 (sepConj_mono hm380 (Entails.refl (protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ joinBase))))) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)))
  exact sepWPp_weaken_pre hpack_slots (r3a_accept_me (g' := g') (peerG := peerG) (meG := meG) (out := out) hh hext hsub64 (r3a_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, hrun]) hsp1 (by simp only [arm64_norm]) hinv1 (by simp only [arm64_norm])) (r3a_reg hx19) (r3a_reg hx20) (r3a_reg hx21) (r3a_reg hx28) (htr1 ▸ htr) (r3a_hist_eq htr1 hfs1 hhist) hans hwr hjoin)

private theorem r3a_bounds [LibsignalPlacement] {A : RustAlloc} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) : runFrame ≤ resStack ∧ resStack - runFrame ≤ 2 ^ 63 ∧ resStack - runFrame ≤ 2 ^ 64 ∧ smallRootStack ≤ resStack - runFrame ∧ 32 + extHookStack ≤ resStack - runFrame ∧ extHookStack ≤ resStack - runFrame ∧ needs.decryptSignal ≤ resStack - runFrame := by
  obtain ⟨hrf, hs63, hs64, _, _, _, _, _, _, _, _, _, hsm, _, h32, _, hext, _, hdec, _, _, _⟩ := runNeed_bounds_placed hres hres64
  exact ⟨hrf, hs63, hs64, hsm, h32, hext, hdec⟩

private theorem r3a_callRecv_open (A : RustAlloc) (a : BitVec 64) (peerV : AddrV) : callAt A a (.recv peerV) ⊢ ∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗ words64At a [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name := by
  unfold callAt callHeap addrWords; dsimp only; apply Entails.sepExists_mono; intro w
  have hp : ⌜w.w0 = 9223372036854775811#64⌝ ∗ (ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ ⌜w.w4.setWidth 8 = peerV.device⌝) ⊢ ⌜w.w4.setWidth 8 = peerV.device⌝ ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name := by
    refine Entails.pure_left fun _ => ?_; rw [sepConj_comm]; exact Entails.refl _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hp))))))) ?_
  dsimp only [words64At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem r3a_after_decrypt_err [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost} {err : ApiError AddrVal Unit} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hext : extHookStack ≤ resStack - runFrame) (h32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 3476) (herr : err ≠ .store ()) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (memRegion (runFsp s0 + 0x4d0#64) 120 ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ (decResAt A (runFsp s0 + 0x320#64) (.error err) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ storesAt A g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ r3a_restFrame (runFsp s0) ∗ anyHeap)) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hm120 : memRegion (fsp + 0x4d0#64) 120 = memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 72 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using ProofLib.memRegion_split (fsp + 0x4d0#64) 48 72 (by decide)
  let errBase : SepProp := memRegion (fsp + 0x500#64) 72 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ storesAt A g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ r3a_restFrame fsp ∗ anyHeap
  refine sepWPp_weaken_pre (P' := (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x320#64) k) ∗ (memRegion (fsp + 0x4d0#64) 48 ∗ A.pool ∗ stackAt fsp sub ∗ errBase)) (by dsimp +zetaDelta only at hm120 ⊢; rw [hm120]; exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left (RunProofs.decResAt_err_owned A (runFsp s0 + 0x320#64) err herr))) (r3a_sepWPp_exists_left fun k => ?_)
  let errKeep : SepProp := A.pool ∗ stackAt fsp sub ∗ errBase
  refine r3a_sepWPp_bind (A0 := RunDrop.speOwnedAt A (fsp + 0x320#64) k ∗ memRegion (fsp + 0x4d0#64) 48) (F := errKeep) ?_ |> sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
  intro R hm; rw [sepConj_assoc] at hm
  obtain ⟨u0, u1, u2, u3, u4, u5, H_spe, hu3, hu2, hm, hspe_close⟩ := r3a_speOwnedAt_relocate A (fsp + 0x320#64) k hm
  obtain ⟨ws4d0, hlen4d0, hm⟩ := r3a_open_words 6 (fsp + 0x4d0#64) (Q := words64At (fsp + 0x320#64) [u0, u1, u2, u3, u4, u5] ∗ (H_spe ∗ (errKeep ∗ R))) (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws4d0 with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen4d0; done)
  refine ⟨words64At (fsp + 0x320#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (fsp + 0x4d0#64) [v0, v1, v2, v3, v4, v5] ∗ H_spe, Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 3476 := hs.pc; change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur; rw [← hs.sp] at hx26
  have hb3 : (u0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hb2 : (u0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  rw [show (words64At (fsp + 0x320#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (fsp + 0x4d0#64) [v0, v1, v2, v3, v4, v5] ∗ H_spe) ∗ errKeep = words64At (s.sp + 0x320#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (s.sp + 0x4d0#64) [v0, v1, v2, v3, v4, v5] ∗ (H_spe ∗ errKeep) by dsimp +zetaDelta only; rw [hs.sp]; ac_rfl]
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
  apply r3a_seq (mid := (blkPl_553).base) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun]); intro hinv1
  rw [hs.sp] at hx26; obtain ⟨htr_10, hfs_10, _⟩ := r3a_step_state (s := s) hinv1
  refine sepWPp_weaken_pre (P' := RunDrop.speOwnedAt A (fsp + 0x4d0#64) k ∗ A.pool ∗ stackAt fsp sub ∗ (memRegion (fsp + 0x320#64) 48 ∗ errBase)) ?_ ?_
  · rw [hs.sp]; have hspe := hspe_close (fsp + 0x4d0#64); simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] at hspe
    have hm320 := r3a_words_to_memRegion [u0, u1, u2, u3, u4, u5] (fsp + 0x320#64) 48; simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hm320
    dsimp +zetaDelta only at hspe hm320 ⊢
    exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)) (Entails.trans (sepConj_mono hspe (sepConj_mono hm320 (Entails.refl (A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ errBase)))) (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)))
  refine r3a_drop_spe_call (k := k) hdrop h32 hsub64 hinv1 (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hal) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]; try rw [hs.sp]; try bv_omega) fun s2 hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2; have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr_10) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 := r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr_10 hfs_10 hhist)
  refine sepWPp_weaken_pre ?_ (r3a_tail_me_reject (g' := g') (peerG := peerG) (meG := meG) hh hext hsub64 hin2 (hcs2.1.trans (r3a_reg hx19)) (hcs2.2.1.trans (r3a_reg hx20)) (hcs2.2.2.1.trans (r3a_reg hx21)) (hcs2.2.2.2.2.1.trans (r3a_reg hx28)) htr2_tot hhist2 hans hrej)
  dsimp +zetaDelta only at hm120 ⊢
  have hrej120 : memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗ stackAt (runFsp s0) (resStack - runFrame) = memRegion (runFsp s0 + 0x4d0#64) 120 ∗ stackAt (runFsp s0) (resStack - runFrame) := by rw [← sepConj_assoc, ← hm120]
  exact Entails.trans (Entails.of_eq (show _ = (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗ (protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ A.pool ∗ anyHeap) by ac_rfl)) (by rw [hrej120]; exact Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_try_err [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {e : SignalProtocolError} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A) (hext : extHookStack ≤ resStack - runFrame) (h32 : 32 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 2032) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res) (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr) (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (signalMessageResultAt A [] (runFsp s0 + 0x4d0#64) (.error e) ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ (protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ anyHeap)) Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tryErrRest : SepProp := memRegion (fsp + 0x508#64) 64 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ r3a_frameGaps fsp ∗ anyHeap
  let tryErrKeep : SepProp := A.pool ∗ stackAt fsp sub ∗ ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ tryErrRest
  refine sepWPp_weaken_pre (P' := (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x4d8#64) k) ∗ (memRegion (fsp + 0x23b0#64) 48 ∗ tryErrKeep)) (Entails.trans (sepConj_mono_left (RunProofs.msgResultAt_err_owned A [] (runFsp s0 + 0x4d0#64) e)) (by dsimp +zetaDelta only [r3a_restFrame]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))) (r3a_sepWPp_exists_left fun k => ?_)
  refine r3a_sepWPp_bind (A0 := RunDrop.speOwnedAt A (fsp + 0x4d8#64) k ∗ memRegion (fsp + 0x23b0#64) 48) (F := tryErrKeep) ?_ |> sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
  intro R hm; rw [sepConj_assoc] at hm
  obtain ⟨u0, u1, u2, u3, u4, u5, H_spe, _, _, hm, hspe_close⟩ := r3a_speOwnedAt_relocate A (fsp + 0x4d8#64) k hm
  obtain ⟨ws23b0, hlen23b0, hm⟩ := r3a_open_words 6 (fsp + 0x23b0#64) (Q := words64At (fsp + 0x4d8#64) [u0, u1, u2, u3, u4, u5] ∗ (H_spe ∗ (tryErrKeep ∗ R))) (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws23b0 with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen23b0; done)
  refine ⟨words64At (fsp + 0x4d8#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_spe, Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 2032 := hs.pc; change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur; rw [← hs.sp] at hx26
  rw [show (words64At (fsp + 0x4d8#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_spe) ∗ tryErrKeep = ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ words64At (s.sp + 0x4d8#64) [u0, u1, u2, u3, u4, u5] ∗ words64At (s.sp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ (H_spe ∗ A.pool ∗ stackAt fsp sub ∗ tryErrRest) by dsimp +zetaDelta only; rw [hs.sp]; ac_rfl]
  simp only [words64At, errTag, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
  apply r3a_seq (mid := (blkPl_553).base) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun]); intro hinv1
  rw [hs.sp] at hx26; obtain ⟨htr_10, hfs_10, _⟩ := r3a_step_state (s := s) hinv1
  refine sepWPp_weaken_pre (P' := RunDrop.speOwnedAt A (fsp + 0x23b0#64) k ∗ A.pool ∗ stackAt fsp sub ∗ (memRegion (fsp + 0x4d0#64) 120 ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ r3a_frameGaps fsp ∗ anyHeap)) ?_ ?_
  · rw [hs.sp]; have hspe := hspe_close (fsp + 0x23b0#64); simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] at hspe
    have hm4d0 : ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ words64At (fsp + 0x4d8#64) [u0, u1, u2, u3, u4, u5] ∗ memRegion (fsp + 0x508#64) 64 ⊢ memRegion (fsp + 0x4d0#64) 120 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (r3a_words_to_memRegion [u0, u1, u2, u3, u4, u5] (fsp + 0x4d8#64) 48))) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using RunProofs.sret120_rejoin (fsp + 0x4d0#64) errTag
    simp only [words64At, errTag, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hm4d0; dsimp +zetaDelta only at hspe hm4d0 ⊢
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (sepConj_mono hspe (sepConj_mono hm4d0 (Entails.refl (A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗ r3a_frameGaps (runFsp s0) ∗ anyHeap)))) (Entails.of_eq (by ac_rfl)))
  refine r3a_drop_spe_call (k := k) hdrop h32 hsub64 hinv1 (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hal) (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (by simpa only [arm64_norm] using hs.sp) (r3a_reg hs.fp) (by simpa only [arm64_norm] using hs.vregs) hs.spAligned (by simp only [arm64_norm]; try rw [hs.sp]; try bv_omega) fun s2 hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2; have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr_10) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 := r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr_10 hfs_10 hhist)
  exact sepWPp_weaken_pre (by dsimp +zetaDelta only [r3a_restFrame]; exact Entails.of_eq (by ac_rfl)) (r3a_tail_me_reject (g' := StoresGhost.opened) (peerG := peerG) (meG := meG) hh hext hsub64 hin2 (hcs2.1.trans (r3a_reg hx19)) (hcs2.2.1.trans (r3a_reg hx20)) (hcs2.2.2.1.trans (r3a_reg hx21)) (hcs2.2.2.2.2.1.trans (r3a_reg hx28)) htr2_tot hhist2 hans hrej)


set_option maxHeartbeats 1600000 in
private theorem r3a_after_decrypt_drop [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage} {ans : SlotAns Bytes} {res : Except (ApiError AddrVal Unit) Bytes}
    {s0 s1 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (h32 : 32 + extHookStack ≤ resStack - runFrame) (hext : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3468) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (_htr_s1 : s0.trace <+: s1.trace) (hga : g.a = finish ans id) (hslot2 : slotOut ans g' res s1 s) (htr2_tot : s0.trace <+: s.trace)
    (hhist2 : RunHistOk g.i s0 s) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (storesAt A g.stores g' ∗ decResAt A (runFsp s0 + 0x320#64) res ∗ signalMessageAt A msgG (runFsp s0 + 0x4d0#64) m ∗
        protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        (FromRecordCallees.lsLogOff ∗ anyHeap ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
        (r3a_restFrame (runFsp s0) ∗ (memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24)))
      Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  have hpc : s.pc = runPcPlaced 3468 := hs.pc; change s.pc = (blkPl_579).base + 3468#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur
  apply r3a_seq (mid := (blkPl_554).base) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun]); intro hinv3
  obtain ⟨htr3, hfs3, hsp3⟩ := r3a_step_state (s := s) hinv3
  have hdsm_ok := dropSignalMessage_placed_ok (callerProg := runProgPlaced H) (i := 579) hh sub h32 hsub64
  let dropKeep : SepProp := storesAt A g.stores g' ∗ decResAt A (fsp + 0x320#64) res ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ r3a_restFrame fsp ∗ callKeep ∗ anyHeap
  refine r3a_call (s0 := s0) ⟨fsp + 0x4d0#64, msgG, m⟩ hdsm_ok hinv3 (by simp only [arm64_norm, *]; try rfl) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hal)
    (show _ = runPcPlaced 3476 by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega) (F := dropKeep) ?_ (hnext := fun s4 hsteps4 hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
  · dsimp only [dropSignalMessageSpec]
    refine Entails.trans (Entails.of_eq (show _ = (FromRecordCallees.lsLogOff ∗ anyHeap) ∗ (signalMessageAt A msgG (fsp + 0x4d0#64) m ∗ A.pool ∗ stackAt fsp sub ∗ storesAt A g.stores g' ∗ decResAt A (fsp + 0x320#64) res ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ r3a_restFrame fsp ∗ callKeep) by dsimp +zetaDelta only; ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (entails_anyHeap _)) ?_; simp only [sepConj_assoc]
    refine Entails.pure_right ?_ (Entails.of_eq (by rw [hsp3, hs.sp]; try dsimp +zetaDelta only; try ac_rfl))
    simp only [arm64_norm]; rw [hs.sp]
  · dsimp only [dropSignalMessageSpec]; simp only [sepConj_assoc]; refine SepWPp.pure_left fun htr4 => ?_
    have hcs4 := r3a_cs_regs hcsm4; rw [hsp3, hs.sp]
    have hin4 : InRunPlaced CodeOk s0 s4 3476 := ⟨hpcm4, hrun4, hsp4.trans (hsp3.trans hs.sp), hcs4.2.2.2.2.2.1.trans (r3a_reg hs.fp), hinv4, hcs4.2.2.2.2.2.2.trans (by simpa only [arm64_norm] using hs.vregs), hs.spAligned⟩
    have hx19_4 := hcs4.1.trans (r3a_reg hx19); have hx20_4 := hcs4.2.1.trans (r3a_reg hx20)
    have hx21_4 := hcs4.2.2.1.trans (r3a_reg hx21); have hx26_4 := hcs4.2.2.2.1.trans (r3a_reg hx26); have hx28_4 := hcs4.2.2.2.2.1.trans (r3a_reg hx28)
    have htr4_tot : s0.trace <+: s4.trace := (htr4.trans htr3) ▸ htr2_tot
    have hhist4 : RunHistOk g.i s0 s4 := r3a_hist_step hh hsteps4 htr4 (r3a_hist_eq htr3 hfs3 hhist2)
    cases res with
    | ok out =>
      obtain ⟨hans_ok, hwr⟩ := r3a_slotOut_ok hslot2
      have hans4 : g.a = some (some (namedWrites g'.writes, out)) := by rw [hga, hans_ok]; rfl
      exact sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; rw [decResAt_ok]; ac_rfl))
        (r3a_accept_tail (g' := g') (peerG := peerG) (meG := meG) (out := out) hh hext hsub64 hin4 hx19_4 hx20_4 hx21_4 hx28_4 htr4_tot hhist4 hans4 hwr hjoin)
    | error err =>
      obtain ⟨herr, hans_err⟩ := r3a_slotOut_err hga hslot2
      exact sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
        (r3a_after_decrypt_err (g' := g') (peerG := peerG) (meG := meG) hh hdrop hext h32 hsub64 hin4 herr hx19_4 hx20_4 hx21_4 hx26_4 hx28_4 htr4_tot hhist4 hans_err hrej)

set_option maxHeartbeats 1600000 in
private theorem r3a_after_try_ok [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {slots : RunSlots}
    {g : RunCall} {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hc : RunCalleesPlaced A H B slots) (hslot_eq : slots.decryptSignal = mkSlot (decSigSlotSpecPlacedOf CodeOk A S) needs.decryptSignal) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hrf : runFrame ≤ resStack) (hdec : needs.decryptSignal ≤ resStack - runFrame) (hsub63 : resStack - runFrame ≤ 2 ^ 63) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hspb : resStack ≤ s0.sp.toNat) (h32 : 32 + extHookStack ≤ resStack - runFrame) (hext : extHookStack ≤ resStack - runFrame)
    (hs : InRunPlaced CodeOk s0 s 2032) (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64) (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (hcoins : (MainHops.coinsOf g.i).length < 2 ^ 63) (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hfok : S.filesOk (runFiles g.i) peerG.val meG.val) (hga : g.a = finish (S.decryptSignal (runFiles g.i) peerG.val meG.val m (MainHops.coinsOf g.i)) id)
    (htr : s0.trace <+: s.trace) (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (signalMessageAt A msgG (runFsp s0 + 0x4d0#64) m ∗ storesAt A g.stores StoresGhost.opened ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ (memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24))
      Q Qp (runOom s0) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  let decCtx : DecSigGhost := {
    peer := peerG, peerA := fsp + 0x220#64, me := meG, meA := fsp + 0x260#64,
    stores := g.stores, ret := fsp + 0x320#64, coinsP := g.coins, F := runFiles g.i,
    coins := MainHops.coinsOf g.i, msgA := fsp + 0x4d0#64, msgG := msgG, msg := m }
  let preF : SepProp := storesAt A g.stores StoresGhost.opened ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt fsp sub ∗ memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ r3a_frameGaps fsp ∗ callKeep
  dsimp only [r3a_restFrame]
  refine r3a_sepWPp_bind (A0 := signalMessageAt A msgG (fsp + 0x4d0#64) m ∗ memRegion (fsp + 0x460#64) 112 ∗
    memRegion (fsp + 0x23b0#64) 48) (F := preF) ?_ |>
    sepWPp_weaken_pre (by dsimp +zetaDelta only; exact Entails.of_eq (by ac_rfl))
  intro R hm; rw [sepConj_assoc, sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H_sm, hw0, _, hm, hsm_close⟩ :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.signalMessageAt_relocate A msgG (fsp + 0x4d0#64) m hm
  rw [r3a_tw] at hm; simp only [r3a_tw] at hsm_close
  obtain ⟨ws460, hlen460, hm⟩ := r3a_open_words 14 (fsp + 0x460#64)
    (Q := words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      (H_sm ∗ (memRegion (fsp + 0x23b0#64) 48 ∗ (preF ∗ R)))) (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws460 with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | ⟨g7, _ | ⟨g8, _ |
    ⟨g9, _ | ⟨g10, _ | ⟨g11, _ | ⟨g12, _ | ⟨g13, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen460; done)
  obtain ⟨ws23b0, hlen23b0, hm⟩ := r3a_open_words 6 (fsp + 0x23b0#64)
    (Q := words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      (words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗ (H_sm ∗ (preF ∗ R))))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws23b0 with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen23b0; done)
  refine ⟨words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
    words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
    words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_sm, Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm, ?_⟩
  have hpc : s.pc = runPcPlaced 2032 := hs.pc; change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26; have hb0 : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  rw [show (words64At (fsp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
    words64At (fsp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
    words64At (fsp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ H_sm) ∗ preF =
    words64At (s.sp + 0x4d0#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
    words64At (s.sp + 0x460#64) [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ∗
    words64At (s.sp + 0x23b0#64) [v0, v1, v2, v3, v4, v5] ∗ (H_sm ∗ preF) by dsimp +zetaDelta only; rw [hs.sp]; ac_rfl]
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
  apply r3a_seq (mid := lsmpl.base 463) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try rfl) (by simp only [arm64_norm, hrun]); intro hinv1
  rw [hs.sp] at hx26; obtain ⟨htr1, hfs1, hsp1⟩ := r3a_step_state (s := s) hinv1
  have htr_s1 : s0.trace <+: _ := htr1 ▸ htr
  have hdec_ok : subroutine_ok (runProgPlaced H) (lsmpl.base 463) (decSigSlotSpecPlacedOf CodeOk A S sub) := by
    have hdec' : slots.decryptSignal.need ≤ sub := by rw [hslot_eq]; exact hdec
    have h := hc.decryptSignal sub hdec' hsub63
    rwa [hslot_eq] at h
  refine sepWPp_weaken_pre (P' := signalMessageAt A msgG (fsp + 0x4d0#64) m ∗
    (r3a_restFrame fsp ∗ storesAt A g.stores StoresGhost.opened ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗
      protocolAddressAt A meG (fsp + 0x260#64) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt fsp sub ∗
      memRegion (fsp + 0x320#64) 48 ∗ callKeep)) ?_ ?_
  · rw [hs.sp]; have hsm := hsm_close (fsp + 0x4d0#64)
    simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] at hsm
    have hm460 := r3a_words_to_memRegion [w7, w8, w9, w10, w11, w12, w13, w14, w1, w2, w3, w4, w5, w6] (fsp + 0x460#64) 112
    simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hm460
    have hm23b0 := r3a_words_to_memRegion [w1, w2, w3, w4, w5, w6] (fsp + 0x23b0#64) 48
    simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hm23b0
    dsimp +zetaDelta only [r3a_restFrame] at hsm hm460 hm23b0 ⊢
    exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
      (Entails.trans (sepConj_mono hsm (sepConj_mono hm460 (sepConj_mono hm23b0
        (Entails.refl (memRegion (runFsp s0 + 0x380#64) 16 ∗ r3a_frameGaps (runFsp s0) ∗
          storesAt A g.stores StoresGhost.opened ∗ protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗
          protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ callKeep)))))
        (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)))
  refine r3a_call_codeOk (s0 := s0) decCtx hdec_ok hinv1 (by simp only [arm64_norm, *]; try rfl) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]; exact hal) (show _ = runPcPlaced 3468 by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega)
    (F := r3a_restFrame fsp ∗ callKeep) ?_
    (hpanic := fun sf _ _ hp => by
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp.1 with hnone | hoom
      · exact hpanic sf _ (Or.inl (by rw [hga]; dsimp only [decCtx] at hnone; rw [hnone]; rfl))
      · exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_s1 hoom)))
    (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (hnext := fun s2 _ hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [slotFramePlaced, decCtx]; simp only [sepConj_assoc]
    refine Entails.pure_right ?_ (Entails.pure_right hcoins (Entails.of_eq (by rw [hsp1, hs.sp]; try dsimp +zetaDelta only; try ac_rfl)))
    have hsp_sub : sub ≤ s.sp.toNat := by
      rw [hs.sp, runFsp, BitVec.toNat_sub_of_le (by change 0x2a50 ≤ s0.sp.toNat; change 0x2a50 ≤ resStack at hrf; omega)]
      change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
    exact ⟨by simp only [arm64_norm, *]; try rw [hs.sp], by simp only [arm64_norm, *]; try rw [hs.sp],
      by simp only [arm64_norm, *]; try rw [hs.sp], by simp only [arm64_norm, *],
      by simp only [sessVtPlaced, lsρ, cliSessionVtSym, arm64_norm], by simp only [arm64_norm, *],
      by simp only [idVtPlaced, lsρ, cliIdentityVtSym, arm64_norm], by simp only [arm64_norm, *]; try rw [hs.sp],
      hfs1.trans hfs, hfok, by rw [hsp1]; exact hsp_sub⟩
  · have hcs2 := r3a_cs_regs hcsm2
    have hin2 : InRunPlaced CodeOk s0 s2 3468 := ⟨hpcm2, hrun2, hsp2.trans (hsp1.trans hs.sp),
      hcs2.2.2.2.2.2.1.trans (r3a_reg hs.fp), hinv2,
      hcs2.2.2.2.2.2.2.trans (by simpa only [arm64_norm] using hs.vregs), hs.spAligned⟩
    dsimp only [decCtx]; refine r3a_sepWPp_exists_left fun g' => r3a_sepWPp_exists_left fun res => ?_
    simp only [sepConj_assoc]; refine r3a_sepWPp_pure_left fun ⟨hstr2, hslot2⟩ => ?_
    have ⟨htr2_tot, hhist2⟩ := r3a_hist_of_slotTrace htr_s1 (hfs1.trans hfs) (htr1 ▸ hout) hstr2
    rw [hsp1, hs.sp]
    exact sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
      (r3a_after_decrypt_drop (g' := g') (peerG := peerG) (meG := meG) (msgG := msgG) (m := m) hh hdrop h32 hext
        hsub64 hin2 (hcs2.1.trans (r3a_reg hx19)) (hcs2.2.1.trans (r3a_reg hx20))
        (hcs2.2.2.1.trans (r3a_reg hx21)) (hcs2.2.2.2.1.trans (r3a_reg hx26))
        (hcs2.2.2.2.2.1.trans (r3a_reg hx28)) htr_s1 hga hslot2 htr2_tot hhist2 hrej hjoin)

set_option maxHeartbeats 1600000 in
private theorem r3a_some_pre_try [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (peerV : AddrV) (rest : Bytes)
    (s0 : State) (resStack : Nat) (meV : AddrV) (meG : AddrGhost) (w : CallW) (u1 : BitVec 64) (H_me : SepProp)
    (hme_bytes : meG.name.bytes = meV.name) (hsm : smallRootStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hcall56 : words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ⊢ memRegion g.call 56)
    (hpeer : words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name ⊢ protocolAddressAt A ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩ (runFsp s0 + 0x220#64))
    (hme_close : ∀ dst : BitVec 64, words64At dst [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ H_me ⊢ addrUpperAt dst meG)
    (h1d0 : words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ⊢ memRegion (runFsp s0) 0x208) :
    let fsp := runFsp s0; let sub := resStack - runFrame; let peerG : AddrGhost := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩
    let someTail : SepProp := memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ∗ memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp ∗ stackAt fsp sub ∗ A.pool
    let tryKeep : SepProp := (g.inp ↦₈ 2#8) ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗
      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp
    (g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6) ∗
      ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1) ∗ ((fsp + 0x220#64) ↦₆₄ w.w1) ∗ ((fsp + 0x228#64) ↦₆₄ w.w2) ∗ ((fsp + 0x230#64) ↦₆₄ w.w3) ∗ ((fsp + 0x238#64) ↦₆₄ w.w4) ∗
      ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗ ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meV.name.length) ∗ ((fsp + 0x278#64) ↦₆₄ u1) ∗ (g.inp ↦₈ 2#8) ∗
      H_me ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A meG ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ someTail ⊢
    ((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (fsp + 0x4d0#64) 120 ∗ FromRecordCallees.lsLogOff ∗ stackAt fsp smallRootStack ∗ A.pool ∗ (memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep) := by
  intro fsp sub peerG someTail tryKeep; have hsp_sm := stackAt_split_ge fsp hsm hsub64
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hcall56 hpeer h1d0 ⊢
  have hme_up := hme_close (fsp + 0x270#64); simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc] at hme_up
  have hme_pack : ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗ (((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x278#64) ↦₆₄ u1) ∗ H_me) ∗ addrNameHeap A meG ⊢ protocolAddressAt A meG (fsp + 0x260#64) := by
    rw [protocolAddressAt_eq_parts A meG (fsp + 0x260#64)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hme_up))
  dsimp +zetaDelta only [r3a_restFrame, r3a_frameGaps] at hcall56 hpeer hme_pack h1d0 hsp_sm ⊢
  rw [hme_bytes] at hme_pack; rw [hsp_sm]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono hcall56 (sepConj_mono hpeer (sepConj_mono hme_pack (sepConj_mono h1d0
      (Entails.refl (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ runSaved s0 ∗ r3a_hiGaps (runFsp s0) ∗
        memRegion g.res runResSize ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x380#64) 16 ∗
        memRegion (runFsp s0 + 0x460#64) 112 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - smallRootStack) ∗
        (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ stackAt (runFsp s0) smallRootStack ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ storesAt A g.stores StoresGhost.opened))))))
      (Entails.of_eq (by ac_rfl)))

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_none [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {rest : Bytes} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced CodeOk S g s0) (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hcall : g.c = .recv peerV) (hstdin : g.i.stdin = 2#8 :: rest) (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (dispatchMemPlaced A g .none s0 resStack) Q Qp (runOom s0) := by
  obtain ⟨_, _, hsub64, _, _, hext, _⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame; have hs : InRunPlaced CodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc; change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23; have hx25 := hd.x25
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by rw [hd.x24, hinp_eq]; rfl
  have hrest32 : rest.length < 2 ^ 32 := by simpa [hstdin] using he.rel.2.1.2.2.1 peerV (hcall ▸ he.parse)
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hans0 : g.a = some none := hd.reject_of_me_none he; have hx21 : s.readReg64 (.gpr 21#5) = -1#64 := hd.meRegs
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩; have hres_split := r3a_res_split g.res
  let noneTail : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗ storesAt A g.stores StoresGhost.opened ∗
    ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗ r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool
  refine sepWPp_weaken_pre (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
    words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name) ∗
    ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (fsp + 0x220#64) 32 ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
    rw [hinp_eq, pointsToBytes_cons, hcall, hres_split, emp_sepConj, r3a_locals_empty_rest (runFsp s0)]
    refine Entails.trans (Entails.of_eq (show _ = callAt A g.call (.recv peerV) ∗
      (coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) ∗
      ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (runFsp s0 + 0x220#64) 32 ∗ (g.inp ↦₈ 2#8) ∗
        (memRegion (g.res + 8#64) (runResSize - 8) ∗ storesAt A g.stores StoresGhost.opened ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
          runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono (r3a_callRecv_open A g.call peerV) (sepConj_mono_left (entails_anyHeap _))) (Entails.of_eq (by ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_; rw [sepConj_assoc, sepConj_assoc]; refine r3a_sepWPp_pure_left fun hw4 => ?_
  refine sepWPp_weaken_pre (P' := (∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ (memRegion (fsp + 0x220#64) 32 ∗
    words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗
    (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap)) (Entails.of_eq (by ac_rfl)) (r3a_sepWPp_exists_left fun w_res => ?_)
  refine r3a_sepWPp_bind (A0 := memRegion (fsp + 0x220#64) 32)
    (F := (g.res ↦₆₄ w_res) ∗ words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ?_ |>
    sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
  intro R hm; obtain ⟨ws220, hlen220, hm⟩ := r3a_memRegion_words 4 (fsp + 0x220#64) (by decide) hm
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  refine ⟨words64At (fsp + 0x220#64) [p0, p1, p2, p3], hm, ?_⟩
  rw [show words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗ ((g.res ↦₆₄ w_res) ∗ words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
    ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) =
    (g.res ↦₆₄ w_res) ∗ words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗
    (g.inp ↦₈ 2#8) ∗ (ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ noneTail ∗ anyHeap) by rw [hs.sp]; ac_rfl]
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
  apply r3a_seq (mid := runPcPlaced 4104) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); rw [runPcPlaced_eq]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun]); intro hinv1
  obtain ⟨htr1, hfs1, _⟩ := r3a_step_state (s := s) hinv1
  refine sepWPp_weaken_pre ?_ (r3a_tail_peer_reject (g' := StoresGhost.opened) (peerG := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩)
    hh hext hsub64 (r3a_inRun_step hs (by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1 (by simp only [arm64_norm]))
    (r3a_reg hx19) (htr1 ▸ hd.trace) (r3a_hist_eq htr1 hfs1 hhist0) hans0 hrej)
  rw [hs.sp]; have hpeer := r3a_pack_peer A (fsp + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hpeer
  have hcall56 := r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hcall56
  dsimp +zetaDelta only [runResAt]; rw [← hinp_merge]
  exact Entails.trans (Entails.of_eq (by try dsimp +zetaDelta only; try ac_rfl))
    (Entails.trans (sepConj_mono hpeer (sepConj_mono hcall56 (Entails.refl ((g.res ↦₆₄ -1#64) ∗
      memRegion (g.res + 8#64) (runResSize - 8) ∗ storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦₈ 2#8) ∗
      ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗
      memRegion (runFsp s0 + 0x260#64) 32 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
      memRegion (runFsp s0 + 0x4d0#64) 120 ∗ r3a_restFrame (runFsp s0) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap))))
      (Entails.of_eq (by try dsimp +zetaDelta only; try ac_rfl)))

set_option maxHeartbeats 1600000 in
private theorem r3a_recvW_some [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {slots : RunSlots} {g : RunCall} {peerV : AddrV} {rest : Bytes}
    {meV : AddrV} {meG : AddrGhost} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hc : RunCalleesPlaced A H B slots)
    (hslot_eq : slots.decryptSignal = mkSlot (decSigSlotSpecPlacedOf CodeOk A S) needs.decryptSignal)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat) (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV) (hstdin : g.i.stdin = 2#8 :: rest) (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp)
    (hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (dispatchMemPlaced A g (.some meV meG) s0 resStack) Q Qp (runOom s0) := by
  have htry := r3a_sigTryFrom_ok hh
  have hlog : logOff Wire.tryFromPlacedImg = FromRecordCallees.lsLogOff := Wire.logOff_tryFromPlacedImg
  obtain ⟨hrf, hsub63, hsub64, hsm, h32, hext, hdec⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame; have hs : InRunPlaced CodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc; change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run; have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23; have hx25 := hd.x25; have hx26 := hd.x26
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by rw [hd.x24, hinp_eq]; rfl
  obtain ⟨hx21, hx28, hme_bytes, _, hme_dev⟩ := hd.meRegs
  obtain ⟨hrest32, hcoins, hfs, hfok, hga⟩ := hd.recvW_facts he hcall hstdin
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  have hme_val : meG.val = addrValOf meV := by unfold AddrGhost.val addrValOf; rw [hme_bytes, hme_dev]
  have hx1_bv : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by rw [BitVec.ofNat_add]; bv_omega
  let someTail : SepProp := memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
    runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 40 ∗ memRegion (fsp + 0x208#64) 24 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
    memRegion (fsp + 0x4d0#64) 120 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ r3a_hiGaps fsp ∗ stackAt fsp sub ∗ A.pool
  refine sepWPp_weaken_pre (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
    words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name) ∗
    (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A meG ∗ (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
      addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗ someTail)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced, dispatchMeHeap, dispatchCells]
    rw [hinp_eq, pointsToBytes_cons, hcall, r3a_frame_some_eq (runFsp s0) meG]
    refine Entails.trans (Entails.of_eq (show _ = callAt A g.call (.recv peerV) ∗ addrNameHeap A meG ∗
      ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ addrUpperAt (runFsp s0 + 0x1d0#64) meG ∗ memRegion (runFsp s0 + 0x220#64) 32 ∗
        memRegion (runFsp s0 + 0x260#64) 32 ∗ (memRegion g.res runResSize ∗ storesAt A g.stores StoresGhost.opened ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
          runSaved s0 ∗ memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
          memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗ r3a_hiGaps (runFsp s0) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono (r3a_callRecv_open A g.call peerV) (sepConj_mono_left (r3a_addrNameHeap_cap_lt A meG))) (Entails.of_eq (by ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_; rw [sepConj_assoc, sepConj_assoc]; refine r3a_sepWPp_pure_left fun hw4 => ?_
  refine sepWPp_weaken_pre (P' := ⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ (words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
    ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A meG ∗ (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
    addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32 ∗ someTail))
    (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl)) (r3a_sepWPp_pure_left fun _hme_lt => ?_)
  have hme_ne : (meG.name.cap + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; bv_omega
  let peerG : AddrGhost := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩
  let someKeep : SepProp := words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗
    addrNameHeap A meG ∗ (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ someTail
  refine r3a_sepWPp_bind (A0 := addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x260#64) 32)
    (F := someKeep) ?_ |> sepWPp_weaken_pre (Entails.of_eq (by dsimp +zetaDelta only; ac_rfl))
  intro R hm; rw [sepConj_assoc, sepConj_assoc] at hm
  obtain ⟨u1, H_me, hm, hme_close⟩ := r3a_addrUpper_relocate (fsp + 0x1d0#64) meG hm
  obtain ⟨ws220, hlen220, hm⟩ := r3a_open_words 4 (fsp + 0x220#64)
    (Q := words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ (H_me ∗ (memRegion (fsp + 0x260#64) 32 ∗ (someKeep ∗ R))))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  obtain ⟨ws260, hlen260, hm⟩ := r3a_open_words 4 (fsp + 0x260#64)
    (Q := words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ (words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗ (H_me ∗ (someKeep ∗ R))))
    (Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm)
  rcases ws260 with _ | ⟨q0, _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen260; done)
  refine ⟨words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
    words64At (fsp + 0x260#64) [q0, q1, q2, q3] ∗ H_me, Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm, ?_⟩
  rw [show (words64At (fsp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗ words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
    words64At (fsp + 0x260#64) [q0, q1, q2, q3] ∗ H_me) ∗ someKeep =
    words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗ words64At (s.sp + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
    words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗ words64At (s.sp + 0x260#64) [q0, q1, q2, q3] ∗ (g.inp ↦₈ 2#8) ∗
    (H_me ∗ ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A meG ∗ ((g.inp + 1#64) ↦ₛ rest) ∗ someTail) by
    dsimp +zetaDelta only; rw [hs.sp]; ac_rfl]
  simp only [words64At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
  apply r3a_seq (mid := lsmpl.base 85) hs.inv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try rfl) (by simp only [arm64_norm, hrun]); intro hinv1
  obtain ⟨htr1, hfs1, hsp1⟩ := r3a_step_state (s := s) hinv1
  have htr_s1 : s0.trace <+: _ := htr1 ▸ hd.trace; have hsp_sm := stackAt_split_ge fsp hsm hsub64
  let tryKeep : SepProp := (g.inp ↦₈ 2#8) ∗ protocolAddressAt A meG (fsp + 0x260#64) ∗ protocolAddressAt A peerG (fsp + 0x220#64) ∗
    storesAt A g.stores StoresGhost.opened ∗ coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗ r3a_restFrame fsp
  refine sepWPp_weaken_pre (P' := ((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (fsp + 0x4d0#64) 120 ∗ FromRecordCallees.lsLogOff ∗
    stackAt fsp smallRootStack ∗ A.pool ∗ (memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep)) ?_ ?_
  · rw [hs.sp]
    exact r3a_some_pre_try A g peerV rest s0 resStack meV meG w u1 H_me hme_bytes hsm hsub64
      (r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56)
      (r3a_pack_peer A (fsp + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4) hme_close
      (r3a_rejoin_1d0 fsp (BitVec.ofNat 64 meG.name.bytes.length) u1)
  refine r3a_call (s0 := s0) ⟨g.inp + 1#64, rest, fsp + 0x4d0#64⟩ htry hinv1 (by simp only [arm64_norm, *]; try rfl)
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]; exact hal)
    (show _ = runPcPlaced 2032 by simp only [runPcPlaced_eq, arm64_norm, *]; try bv_omega)
    (F := memRegion (fsp - BitVec.ofNat 64 sub) (sub - smallRootStack) ∗ tryKeep) ?_
    (hpanic := fun sf _ _ hp => by
      dsimp only [Wire.tryFromPlacedSpec] at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_s1 hp.1.1)))
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
  · dsimp only [Wire.tryFromPlacedSpec]; rw [hlog]; simp only [sepConj_assoc]
    refine Entails.pure_right ?_ (Entails.of_eq (by rw [hsp1, hs.sp]))
    exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega, hrest32, by simp only [arm64_norm, *]; try rw [hs.sp]⟩
  · have hcs2 := r3a_cs_regs hcsm2; have hsp2_fsp : s2.sp = fsp := hsp2.trans (hsp1.trans hs.sp)
    have hin2 : InRunPlaced CodeOk s0 s2 2032 := ⟨hpcm2, hrun2, hsp2_fsp,
      hcs2.2.2.2.2.2.1.trans (r3a_reg hs.fp), hinv2,
      hcs2.2.2.2.2.2.2.trans (by simpa only [arm64_norm] using hs.vregs), hs.spAligned⟩
    have hx19_2 := hcs2.1.trans (r3a_reg hx19); have hx20_2 := hcs2.2.1.trans (r3a_reg hx20)
    have hx21_2 := hcs2.2.2.1.trans (r3a_reg hx21); have hx26_2 := hcs2.2.2.2.1.trans (r3a_reg hx26)
    have hx28_2 := hcs2.2.2.2.2.1.trans (r3a_reg hx28)
    dsimp only [Wire.tryFromPlacedSpec]; rw [hlog]; simp only [sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_; rw [hsp1, hs.sp]
    have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ hd.trace
    have hfs2 : s2.fs.files = runFiles g.i := (r3a_files_eq hh hsteps2 htr2).trans (hfs1.trans hfs)
    have hout2 : ProcessOutcome.traceStreamBytes .stdout s2.trace = [] := (htr2.trans htr1) ▸ hd.stdout
    rcases hm_res : SignalMessage.tryFrom protoSignalCodec rest with e | m
    · have hans2 : g.a = some none := by rw [hga, hm_res]
      refine sepWPp_weaken_pre ?_ (r3a_recvW_try_err (peerG := peerG) (meG := meG) (e := e) hh hdrop hext h32 hsub64 hin2
        hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 htr2_tot ⟨hfs2, hout2⟩ hans2 hrej)
      dsimp +zetaDelta only at hsp_sm ⊢
      refine Entails.trans (Entails.of_eq (show _ = ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest)) ∗
        (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - smallRootStack) ∗ stackAt (runFsp s0) smallRootStack) ∗
        (coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff) ∗
        (signalMessageResultAt A [] (runFsp s0 + 0x4d0#64) (.error e) ∗ A.pool ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ storesAt A g.stores StoresGhost.opened ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0)) by ac_rfl)) ?_
      rw [hinp_merge, hsp_sm.symm]
      exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (entails_anyHeap _)))) (Entails.of_eq (by ac_rfl))
    · dsimp only [signalMessageResultAt]; refine r3a_sepWPp_exists_left fun msgG => ?_
      rw [hm_res] at hga
      have hfok' : S.filesOk (runFiles g.i) peerG.val meG.val := by rw [hme_val]; exact hfok
      have hga' : g.a = finish (S.decryptSignal (runFiles g.i) peerG.val meG.val m (MainHops.coinsOf g.i)) id := by rw [hme_val]; exact hga
      refine sepWPp_weaken_pre ?_ (r3a_after_try_ok (peerG := peerG) (meG := meG) (msgG := msgG) (m := m) hh hc hslot_eq hdrop hrf hdec
        hsub63 hsub64 hspb h32 hext hin2 hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 hcoins hfs2 hout2 hfok' hga' htr2_tot hpanic hrej hjoin)
      dsimp +zetaDelta only at hsp_sm ⊢
      refine Entails.trans (Entails.of_eq (show _ = ((g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest)) ∗
        (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - smallRootStack) ∗ stackAt (runFsp s0) smallRootStack) ∗
        (signalMessageAt A msgG (runFsp s0 + 0x4d0#64) m ∗ storesAt A g.stores StoresGhost.opened ∗
          protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗ protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
          coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
          A.pool ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗ r3a_restFrame (runFsp s0) ∗ memRegion g.res runResSize ∗
          memRegion g.call 56 ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24) by ac_rfl)) ?_
      rw [hinp_merge, hsp_sm.symm]; exact Entails.of_eq (by ac_rfl)

theorem run_hop_recvW_of_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A S needs))
    (hslot_eq : slots.decryptSignal = mkSlot (decSigSlotSpecPlacedOf CodeOk A S) needs.decryptSignal) :
    RunHopRecvWPlacedOf CodeOk A H B S slots resStack := by
  intro g s0 s me peerV rest Q Qp hh hc hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
  rw [hneed_eq] at hres
  cases me with
  | none => exact r3a_recvW_none hh hres hres64 he hd hcall hstdin hrej
  | some _ _ => exact r3a_recvW_some hh hc hslot_eq hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin

theorem run_hop_recvW_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {resStack : Nat} :
    RunHopRecvWPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  run_hop_recvW_of_codeOk
    (CodeOk := LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
    (slots := slotsOfPlaced A S needs) (needs := needs) rfl rfl

theorem run_hop_recvW_frozen_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem}
    {needs : RunNeeds} {resStack : Nat} :
    RunHopRecvWPlacedOf (LibsignalFrozen lsmpl)
      A H B S (slotsOfSigFrozenPlaced A S needs) resStack :=
  run_hop_recvW_of_codeOk
    (CodeOk := LibsignalFrozen lsmpl)
    (slots := slotsOfSigFrozenPlaced A S needs) (needs := needs) rfl rfl

end CryptoVerification.SignalSession.Cli.RunCompose
