/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.EncResBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.Helpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.Disproof.Basic

/-!
# `signal_session::run` Placed Arm `R2` Helpers

Relocatable (`[LibsignalPlacement]`) framing, call, deallocation, and layout helpers for Arm `R2`
(`RunHopSendPlaced`) on Block `579` (`runProgPlaced H`).
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
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt?

abbrev r2p_CodeOk [LibsignalPlacement] : Memory → Prop :=
  LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl

theorem r2p_vregs_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 v rfl
theorem r2p_vregs_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 1#5 v rfl
theorem r2p_vregs_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 2#5 v rfl

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

theorem r2p_call [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {callee_pc ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee_pc
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : r2p_CodeOk s.mem) (hpc : s.pc = callee_pc) (hrun : s.status = .Running)
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
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → r2p_CodeOk sf.mem →
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
        (sepConj_mono_right (Entails.trans (Entails.pure_right hinv (Entails.refl emp))
          (Entails.of_eq (sepConj_emp _))))))
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · have hinv_m : r2p_CodeOk sm.mem := hinv.of_keepsFrozen hsteps.keepsFrozen
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

theorem r2p_cs_regs {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
    sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
    sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
    sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
    sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
    sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
    sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
    sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
    sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
    sf.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs sf = calleeSavedVRegs s := by
  unfold CalleeSavedPreserved at h; simp_all

theorem r2p_inRun_mk [LibsignalPlacement] {s0 s sf : State} {k k' : Nat}
    (hs : InRunPlaced r2p_CodeOk s0 s k) (hpc : sf.pc = runPcPlaced k')
    (hrun : sf.status = .Running) (hsp : sf.sp = s.sp)
    (hfp : sf.readReg64 .fp = s.readReg64 .fp)
    (hinv : r2p_CodeOk sf.mem)
    (hv : calleeSavedVRegs sf = calleeSavedVRegs s) :
    InRunPlaced r2p_CodeOk s0 sf k' :=
  ⟨hpc, hrun, hsp.trans hs.sp, hfp.trans hs.fp, hinv, hv.trans hs.vregs, hs.spAligned⟩

theorem r2p_files_of_trace_eq [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s sf : State} (hh : RunHooksPlaced A H)
    (hsteps : Steps (runProgPlaced H) s sf) (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps (htr.trans (List.append_nil _).symm) NoFsEv.nil

theorem r2p_histOk_of_trace_files {i : Inputs} {s0 s sf : State}
    (h : RunHistOk i s0 s) (htr : sf.trace = s.trace) (hfs : sf.fs.files = s.fs.files) :
    RunHistOk i s0 sf :=
  ⟨hfs.trans h.1, htr ▸ h.2⟩

theorem r2p_histOk_of_slotTrace {i : Inputs} {s0 s sf : State}
    (h : RunHistOk i s0 s) (hst : slotTrace s sf) :
    RunHistOk i s0 sf :=
  ⟨hst.2.1.trans h.1, hst.2.2.trans h.2⟩

theorem r2p_call_dealloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {i : Inputs} {s0 sRef s : State} {refOff nextOff sub : Nat} {ptr sz : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (href : InRunPlaced r2p_CodeOk s0 sRef refOff)
    (hinv : r2p_CodeOk s.mem) (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hsp : s.sp = sRef.sp)
    (hfp : s.readReg64 .fp = sRef.readReg64 .fp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs sRef)
    (hlr : s.readReg64 .lr = runPcPlaced nextOff)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = sz)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hpos : 0 < sz.toNat) (hlt : sz.toNat < 2 ^ 63)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf nextOff →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hda := dealloc_lscro_of_cli (callerProg := runProgPlaced H) (i := 579) hh.alloc
  have hlay : LayoutOk sz.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  have hsp_eq : s.sp = runFsp s0 := hsp.trans href.sp
  have hsp_al : s.spAligned = true := by
    have hr := href.spAligned_cur
    simpa only [State.spAligned, hsp] using hr
  have hsp_split := stackAt_split_ge (runFsp s0) hextNeed hsub64
  rw [hsp_split]
  refine r2p_call (ptr, sz.toNat, 1) hda hinv hpc hrun hsp_al hlr
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F) ?_
    (hnext := fun sf hsteps hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]
    rw [hsp_eq]; simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, by simp [hx1], by simp [hx2], hlay⟩
      (Entails.of_eq (by ac_rfl))
  · dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun htr_f => ?_
    have hfs_f := r2p_files_of_trace_eq hh hsteps htr_f
    have hcs := r2p_cs_regs hcsm
    have hin_f : InRunPlaced r2p_CodeOk s0 sf nextOff :=
      r2p_inRun_mk href hpcm hrunm (hspm.trans hsp)
        (hcs.2.2.2.2.2.2.2.2.2.2.1.trans hfp) hinv_f
        (hcs.2.2.2.2.2.2.2.2.2.2.2.trans hv)
    have htr_sf : s0.trace <+: sf.trace := htr_f ▸ htr
    have hhist_sf : RunHistOk i s0 sf := r2p_histOk_of_trace_files hhist htr_f hfs_f
    refine sepWPp_weaken_pre ?_ (hnext sf htr_f hin_f hcsm htr_sf hhist_sf)
    rw [hsp_eq]
    have hmerge :
        A.pool ∗ (stackAt (runFsp s0) extHookStack ∗
          (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F)) =
        A.pool ∗ (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗
          stackAt (runFsp s0) extHookStack) ∗ F := by ac_rfl
    rw [hmerge, hsp_split.symm]; exact Entails.refl _

theorem r2p_peel [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {ret : BitVec 64}
    {s0 s : State} {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp (runProgPlaced H) ret s (P x ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s ((∃∗ x : α, P x) ∗ F) Q Qp (runOom s0) := by
  intro R hm hL; rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hm⟩ := hm; exact h x R hm hL

theorem r2p_peel_pure [LibsignalPlacement] {φ : Prop} {H : LibsignalHooks} {ret : BitVec 64}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp (runProgPlaced H) ret s F Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s (⌜φ⌝ ∗ F) Q Qp (runOom s0) :=
  SepWPp.pure_left h

def r2_pack8 : List (BitVec 8) → BitVec 64
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0
  | _ => 0#64

theorem r2_unpack64_pack8 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (r2_pack8 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at h
  unfold r2_pack8 unpack64
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
         by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem r2_pointsToBytes8_eq_word (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ r2_pack8 bs) := by
  rw [pointsTo64_eq_pointsToBytes, r2_unpack64_pack8 bs h]

theorem r2_pointsToBytes32_eq_words4 (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ r2_pack8 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ r2_pack8 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ r2_pack8 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ r2_pack8 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      r2_pointsToBytes8_eq_word a (bs.take 8) h0,
      r2_pointsToBytes8_eq_word _ ((bs.drop 8).take 8) h1,
      r2_pointsToBytes8_eq_word _ ((bs.drop 16).take 8) h2,
      r2_pointsToBytes8_eq_word _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by
    bv_omega
  rw [ha24, ha16, ha8]

theorem r2_u32_pair_eq_word (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ r2_pack8 (unpack32 lo ++ unpack32 hi)) := by
  have hl : (unpack32 lo).length = 4 := rfl
  have hl8 : (unpack32 lo ++ unpack32 hi).length = 8 := rfl
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  have hcat := pointsToBytes_append a (unpack32 lo) (unpack32 hi)
  rw [hl] at hcat
  rw [← hcat, r2_pointsToBytes8_eq_word a _ hl8]

theorem r2_memRegion4_eq_exists_u32 (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4) (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun m => ⟨fun _ => ⟨m.read32 a, rfl⟩, fun _ => trivial⟩

theorem r2_word64_to_u8_pad7 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.setWidth 8) ∗ memRegion (a + 1#64) 7 := by
  have hunp : unpack64 w = w.setWidth 8 :: (unpack64 w).tail := by
    unfold unpack64
    simp only [List.tail_cons]
    congr 1
  have htl : ((unpack64 w).tail).length = 7 := rfl
  rw [pointsTo64_eq_pointsToBytes, hunp, pointsToBytes_cons]
  exact sepConj_mono_right (htl ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)

theorem r2_u8_pad7_reloc {F : BitVec 64 → SepProp} (b0 : BitVec 8)
    (hF : ∀ a, F a = (a ↦₈ b0) ∗ memRegion (a + 1#64) 7) (src : BitVec 64) :
    F src ⊢ ∃∗ w : BitVec 64, ⌜∀ dst, (dst ↦₆₄ w) ⊢ F dst⌝ ∗ (src ↦₆₄ w) := by
  have heq : ∀ a, F a = ∃∗ w : BitVec 64, ⌜w.setWidth 8 = b0⌝ ∗ (a ↦₆₄ w) := by
    intro a
    rw [hF a]
    refine IsBlock.eq
      (IsBlock.sepConj (IsBlock.pointsTo8 a b0) (IsBlock.memRegion (a + 1#64) 7) rfl (by decide))
      (IsBlock.sepExists fun w => IsBlock.pure_sepConj fun _ => IsBlock.pointsTo64 a w)
      fun m => ⟨fun ⟨hb, _⟩ => ⟨m.read64 a, ?_, rfl⟩, fun ⟨w, hw, hm64⟩ => ⟨?_, trivial⟩⟩
    · rw [← hb]
      unfold Memory.read64 Memory.read8
      simp only [BitVec.add_zero]
      bv_bits
    · rw [← hw, ← hm64]
      unfold Memory.read64 Memory.read8
      simp only [BitVec.add_zero]
      bv_bits
  rw [heq src]
  apply Entails.sepExists_mono; intro w
  apply Entails.pure_left; intro hw
  refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
  rw [heq dst]
  exact Entails.sepExists_right w (Entails.pure_right hw (Entails.refl _))

theorem r2_addrUpperAt_reloc (src : BitVec 64) (g : AddrGhost) :
    addrUpperAt src g ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst g⌝ ∗
          (src ↦₆₄ u0) ∗ ((src + 8#64) ↦₆₄ u1) := by
  unfold addrUpperAt
  have h1 := r2_u8_pad7_reloc g.device (fun a => rfl) (src + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  refine Entails.trans (sepConj_mono_right h1) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u1
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hu1
  refine Entails.sepExists_right (BitVec.ofNat 64 g.name.bytes.length)
    (Entails.sepExists_right u1 ?_)
  refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
  have hu1' := hu1 (dst + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu1'
  exact sepConj_mono_right hu1'

theorem r2_callAt_send_unpack (A : RustAlloc) (callPtr : BitVec 64) (peerV : AddrV) :
    callAt A callPtr (.send peerV) ⊢
      ∃∗ peerG : AddrGhost, ∃∗ w : CallW,
        ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = w.w1 ∧ peerG.name.ptr = w.w2 ∧
          w.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ w.w4.setWidth 8 = peerG.device⌝ ∗
        ((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
          ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
          ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ∗
        addrNameHeap A peerG := by
  unfold callAt callHeap addrWords ownedBytes
  apply Entails.sepExists_elim; intro w
  let peerG : AddrGhost :=
    { name := { cap := w.w1, ptr := w.w2, bytes := peerV.name }, device := peerV.device }
  refine Entails.sepExists_right peerG (Entails.sepExists_right w ?_)
  have hassoc1 :
      (callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
        ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
        ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6) ∗
        ⌜w.w0 = 0x8000000000000002#64⌝ ∗
        ((⌜w.w3 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w1.toNat ∧
            w.w1.toNat < 2 ^ 63 ∧ w.w2 ≠ 0⌝ ∗
          if w.w1 = 0 then emp
          else A.live w.w2 w.w1.toNat 1 ∗ (w.w2 ↦ₛ peerV.name) ∗
            memRegion (w.w2 + BitVec.ofNat 64 peerV.name.length)
              (w.w1.toNat - peerV.name.length)) ∗
          ⌜w.w4.setWidth 8 = peerV.device⌝) =
      ⌜w.w0 = 0x8000000000000002#64⌝ ∗
      ⌜w.w3 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w1.toNat ∧
        w.w1.toNat < 2 ^ 63 ∧ w.w2 ≠ 0⌝ ∗
      ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
      (((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
          ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
          ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ∗
        if w.w1 = 0 then emp
        else A.live w.w2 w.w1.toNat 1 ∗ (w.w2 ↦ₛ peerV.name) ∗
          memRegion (w.w2 + BitVec.ofNat 64 peerV.name.length)
            (w.w1.toNat - peerV.name.length)) := by
    ac_rfl
  rw [hassoc1]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; rintro ⟨hw3, hle, hlt, hne⟩
  apply Entails.pure_left; intro hw4
  refine Entails.pure_right ⟨rfl, rfl, rfl, hw3, hw4⟩ ?_
  unfold addrNameHeap
  dsimp only [peerG]
  exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem r2_callWords_to_memRegion56 (callPtr : BitVec 64) (w : CallW) :
    ((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
      ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
      ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ⊢
      memRegion callPtr 56 := by
  rw [ProofLib.memRegion_split callPtr 8 48 (by decide),
      ProofLib.memRegion_split (callPtr + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split _ 8 32 (by decide),
      ProofLib.memRegion_split _ 8 24 (by decide),
      ProofLib.memRegion_split _ 8 16 (by decide),
      ProofLib.memRegion_split _ 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))

theorem r2_peerWords_pack (A : RustAlloc) (a : BitVec 64) (peerG : AddrGhost) (w : CallW)
    (hw1 : peerG.name.cap = w.w1) (hw2 : peerG.name.ptr = w.w2)
    (hw3 : w.w3 = BitVec.ofNat 64 peerG.name.bytes.length)
    (hw4 : w.w4.setWidth 8 = peerG.device) :
    (a ↦₆₄ w.w1) ∗ ((a + 8#64) ↦₆₄ w.w2) ∗ ((a + 16#64) ↦₆₄ w.w3) ∗
      ((a + 24#64) ↦₆₄ w.w4) ∗ addrNameHeap A peerG ⊢
      protocolAddressAt A peerG a := by
  rw [protocolAddressAt_eq_parts A peerG a, hw1, hw2, hw3,
      ← sepConj_assoc ((a + 16#64) ↦₆₄ _)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
  unfold addrUpperAt
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  have ha25 : a + 16#64 + 9#64 = a + 25#64 := by bv_omega
  rw [ha24, ha25]
  refine sepConj_mono_right ?_
  have hpad := r2_word64_to_u8_pad7 (a + 24#64) w.w4
  have ha1 : a + 24#64 + 1#64 = a + 25#64 := by bv_omega
  rw [hw4, ha1] at hpad
  exact hpad

theorem r2_addrNameHeap_cap_lt (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem r2_addrNameHeap_eq_ownedBytes (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g =
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  unfold addrNameHeap ownedBytes
  have hp :
      (g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0) =
      (BitVec.ofNat 64 g.name.bytes.length = BitVec.ofNat 64 g.name.bytes.length ∧
        g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0) :=
    propext ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  conv => lhs; rw [hp]

theorem r2_protocolAddress_to_mem32_heap (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢ memRegion a 32 ∗ addrNameHeap A g := by
  rw [protocolAddressAt_eq_parts A g a, ← sepConj_assoc (a ↦₆₄ g.name.cap)]
  have h16 : (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ⊢ memRegion a 16 := by
    rw [ProofLib.memRegion_split a 8 8 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  refine Entails.trans
    (sepConj_mono h16 (sepConj_mono_left (addrUpperAt_entails_memRegion (a + 16#64) g))) ?_
  rw [← sepConj_assoc, ProofLib.memRegion_split a 16 16 (by decide)]
  exact Entails.refl _

structure r2_SlotWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  w15 : BitVec 64
  w16 : BitVec 64
  w17 : BitVec 64
  w18 : BitVec 64
  w19 : BitVec 64
  w20 : BitVec 64
  w21 : BitVec 64
  w22 : BitVec 64
  w23 : BitVec 64
  w24 : BitVec 64
  w25 : BitVec 64
  w26 : BitVec 64
  w27 : BitVec 64
  w28 : BitVec 64
  w29 : BitVec 64
  w30 : BitVec 64

def r2_words31 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
  ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗
  ((a + 56#64) ↦₆₄ w.w7) ∗ ((a + 64#64) ↦₆₄ w.w8) ∗ ((a + 72#64) ↦₆₄ w.w9) ∗
  ((a + 80#64) ↦₆₄ w.w10) ∗ ((a + 88#64) ↦₆₄ w.w11) ∗ ((a + 96#64) ↦₆₄ w.w12) ∗
  ((a + 104#64) ↦₆₄ w.w13) ∗ ((a + 112#64) ↦₆₄ w.w14) ∗ ((a + 120#64) ↦₆₄ w.w15) ∗
  ((a + 128#64) ↦₆₄ w.w16) ∗ ((a + 136#64) ↦₆₄ w.w17) ∗ ((a + 144#64) ↦₆₄ w.w18) ∗
  ((a + 152#64) ↦₆₄ w.w19) ∗ ((a + 160#64) ↦₆₄ w.w20) ∗ ((a + 168#64) ↦₆₄ w.w21) ∗
  ((a + 176#64) ↦₆₄ w.w22) ∗ ((a + 184#64) ↦₆₄ w.w23) ∗ ((a + 192#64) ↦₆₄ w.w24) ∗
  ((a + 200#64) ↦₆₄ w.w25) ∗ ((a + 208#64) ↦₆₄ w.w26) ∗ ((a + 216#64) ↦₆₄ w.w27) ∗
  ((a + 224#64) ↦₆₄ w.w28) ∗ ((a + 232#64) ↦₆₄ w.w29) ∗ ((a + 240#64) ↦₆₄ w.w30)

theorem r2_memRegion248_open (a : BitVec 64) :
    memRegion a 248 ⊢ ∃∗ w : r2_SlotWords, r2_words31 a w := by
  have heq : memRegion a 248 = cells a 31 := ProofLib.memRegion_cells a 31 (by decide)
  rw [heq]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6; apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w8; apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w10; apply Entails.sepExists_elim; intro w11
  apply Entails.sepExists_elim; intro w12; apply Entails.sepExists_elim; intro w13
  apply Entails.sepExists_elim; intro w14; apply Entails.sepExists_elim; intro w15
  apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w17
  apply Entails.sepExists_elim; intro w18; apply Entails.sepExists_elim; intro w19
  apply Entails.sepExists_elim; intro w20; apply Entails.sepExists_elim; intro w21
  apply Entails.sepExists_elim; intro w22; apply Entails.sepExists_elim; intro w23
  apply Entails.sepExists_elim; intro w24; apply Entails.sepExists_elim; intro w25
  apply Entails.sepExists_elim; intro w26; apply Entails.sepExists_elim; intro w27
  apply Entails.sepExists_elim; intro w28; apply Entails.sepExists_elim; intro w29
  apply Entails.sepExists_elim; intro w30
  exact Entails.sepExists_right
    ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
     w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
    (Entails.refl _)

theorem r2_words31_to_memRegion248 (a : BitVec 64) (w : r2_SlotWords) :
    r2_words31 a w ⊢ memRegion a 248 := by
  have heq : memRegion a 248 = cells a 31 := ProofLib.memRegion_cells a 31 (by decide)
  rw [heq]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  exact Entails.sepExists_right w.w0 (Entails.sepExists_right w.w1 (Entails.sepExists_right w.w2
    (Entails.sepExists_right w.w3 (Entails.sepExists_right w.w4 (Entails.sepExists_right w.w5
    (Entails.sepExists_right w.w6 (Entails.sepExists_right w.w7 (Entails.sepExists_right w.w8
    (Entails.sepExists_right w.w9 (Entails.sepExists_right w.w10 (Entails.sepExists_right w.w11
    (Entails.sepExists_right w.w12 (Entails.sepExists_right w.w13 (Entails.sepExists_right w.w14
    (Entails.sepExists_right w.w15 (Entails.sepExists_right w.w16 (Entails.sepExists_right w.w17
    (Entails.sepExists_right w.w18 (Entails.sepExists_right w.w19 (Entails.sepExists_right w.w20
    (Entails.sepExists_right w.w21 (Entails.sepExists_right w.w22 (Entails.sepExists_right w.w23
    (Entails.sepExists_right w.w24 (Entails.sepExists_right w.w25 (Entails.sepExists_right w.w26
    (Entails.sepExists_right w.w27 (Entails.sepExists_right w.w28 (Entails.sepExists_right w.w29
      (Entails.sepExists_right w.w30 (Entails.refl _)))))))))))))))))))))))))))))))

def r2_boxLive (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if bs = [] then emp else A.live ptr bs.length 1

theorem r2_boxU8At_eq (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
        (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs := by
  unfold boxU8At r2_boxLive
  have ha : a + asm64% boxSliceLenOff = a + 8#64 := rfl
  rw [ha]
  cases bs with
  | nil => simp only [↓reduceIte, pointsToBytes_nil]; ac_rfl
  | cons b tl =>
    have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
    simp only [hne, ↓reduceIte]; ac_rfl

theorem r2_boxLive_to_sliceDeallocX (A : RustAlloc) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs ⊢
      DropPreKeyMsgHelpers.sliceDeallocX A ptr (BitVec.ofNat 64 bs.length) := by
  unfold r2_boxLive DropPreKeyMsgHelpers.sliceDeallocX
  cases bs with
  | nil =>
    simp only [List.length_nil, ↓reduceIte, pointsToBytes_nil, emp_sepConj, beq_self_eq_true]
    exact Entails.refl emp
  | cons b tl =>
    have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
    have hpos : 0 < (b :: tl).length := List.length_pos_of_ne_nil hne
    have h64 : (b :: tl).length < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 (b :: tl).length).toNat = (b :: tl).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    have hbeq : (BitVec.ofNat 64 (b :: tl).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr fun h => by rw [h] at hto; simp at hto
    simp only [hne, hbeq, Bool.false_eq_true, ↓reduceIte, hto]
    refine Entails.pure_right ⟨hpos, hlen⟩ ?_
    rw [sepConj_comm]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: tl))

theorem r2_u32_pad4_eq (a : BitVec 64) (lo : BitVec 32) :
    ((a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4) =
      ∃∗ hi : BitVec 32, a ↦₆₄ r2_pack8 (unpack32 lo ++ unpack32 hi) := by
  rw [r2_memRegion4_eq_exists_u32 (a + 4#64), sepExists_sepConj_right]
  simp only [r2_u32_pair_eq_word]

theorem r2_open_signalMessage (A : RustAlloc) (r : BitVec 64)
    (g : SignalMessageGhost) (m : SignalMessage) :
    (r ↦₆₄ ctSignalTag) ∗ signalMessageAt A g (r + 8#64) m ∗ memRegion (r + 0x80#64) 120 ⊢
      ∃∗ ws : r2_SlotWords, ∃∗ adPtr : BitVec 64, ∃∗ adLen : BitVec 64,
        ⌜ws.w0 = ctSignalTag ∧ ws.w1 = g.pqCap ∧ ws.w2 = g.pqPtr ∧
          ws.w4 = g.ctPtr ∧ ws.w5 = BitVec.ofNat 64 m.ciphertext.length ∧
          ws.w6 = g.serPtr ∧ ws.w7 = BitVec.ofNat 64 m.serialized.length ∧
          ws.w12 = adPtr ∧ ws.w13 = adLen ∧
          m.serialized.length < 2 ^ 40 ∧ g.serPtr ≠ 0⌝ ∗
        r2_words31 r ws ∗
        (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
        DropPreKeyMsgHelpers.sliceDeallocX A g.ctPtr (BitVec.ofNat 64 m.ciphertext.length) ∗
        DropPreKeyMsgHelpers.sliceDeallocX A g.pqPtr g.pqCap ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A adPtr adLen := by
  unfold signalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hsm
  have hpq := DropPreKeyMsgHelpers.vecU8At_entails_sliceDeallocX A (r + 8#64) g.pqCap g.pqPtr m.pqRatchet
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpq
  have hct := DropPreKeyMsgHelpers.boxU8At_entails_sliceDeallocX A (r + 32#64) g.ctPtr m.ciphertext
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hct
  have had := DropPreKeyMsgHelpers.optBoxU8At_entails_optSliceDeallocX A (r + 96#64) g.addrPtr m.addresses
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at had
  have hsrk : ((r + 64#64) ↦ₛ m.senderRatchetKey.bytes.toList) ⊢ cells (r + 64#64) 4 := by
    rw [← ProofLib.memRegion_cells (r + 64#64) 4 (by decide)]
    exact DropPreKeyMsgHelpers.pkBytes_entails_memRegion32 (r + 64#64) m.senderRatchetKey
  have htail :
      ((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
        ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7 ∗
        memRegion (r + 128#64) 120 ⊢
      cells (r + 112#64) 17 := by
    rw [← ProofLib.memRegion_cells (r + 112#64) 17 (by decide)]
    have ht := DropPreKeyMsgHelpers.trailer16_entails_memRegion16 (r + 112#64)
      m.counter m.previousCounter m.messageVersion
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ht
    have hgrp_t :
        ((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
          ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7 ∗
          memRegion (r + 128#64) 120 =
        (((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
          ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7) ∗
          memRegion (r + 128#64) 120 := by ac_rfl
    rw [hgrp_t, show (8 * 17 : Nat) = 136 from rfl,
        ProofLib.memRegion_split' (b := r + 112#64) (n := 16) (k := 120)
          (b' := r + 128#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left ht
  rw [r2_boxU8At_eq A (r + 48#64) g.serPtr m.serialized]
  refine Entails.trans (sepConj_mono_right (sepConj_mono hpq (sepConj_mono hct
    (sepConj_mono_right (sepConj_mono hsrk (sepConj_mono had htail)))))) ?_
  rw [ProofLib.memRegion_eight (r + 24#64)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9; apply Entails.sepExists_elim; intro w10
  apply Entails.sepExists_elim; intro w11; apply Entails.sepExists_elim; intro adPtr
  apply Entails.sepExists_elim; intro adLen; apply Entails.sepExists_elim; intro w14
  apply Entails.sepExists_elim; intro w15; apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w17; apply Entails.sepExists_elim; intro w18
  apply Entails.sepExists_elim; intro w19; apply Entails.sepExists_elim; intro w20
  apply Entails.sepExists_elim; intro w21; apply Entails.sepExists_elim; intro w22
  apply Entails.sepExists_elim; intro w23; apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w25; apply Entails.sepExists_elim; intro w26
  apply Entails.sepExists_elim; intro w27; apply Entails.sepExists_elim; intro w28
  apply Entails.sepExists_elim; intro w29; apply Entails.sepExists_elim; intro w30
  let ws : r2_SlotWords :=
    ⟨ctSignalTag, g.pqCap, g.pqPtr, w3, g.ctPtr, BitVec.ofNat 64 m.ciphertext.length,
     g.serPtr, BitVec.ofNat 64 m.serialized.length, w8, w9, w10, w11, adPtr, adLen,
     w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
  refine Entails.trans (Q :=
        ⌜g.ctPtr ≠ 0⌝ ∗ ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          (r2_words31 r ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
            DropPreKeyMsgHelpers.sliceDeallocX A g.ctPtr (BitVec.ofNat 64 m.ciphertext.length) ∗
            DropPreKeyMsgHelpers.sliceDeallocX A g.pqPtr g.pqCap ∗
            DropPreKeyMsgHelpers.optSliceDeallocX A adPtr adLen))
      (by unfold r2_words31; dsimp only [ws]; exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; rintro ⟨hser_ne, _⟩
  refine Entails.sepExists_right ws
    (Entails.sepExists_right adPtr (Entails.sepExists_right adLen ?_))
  exact Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsm.2.1, hser_ne⟩
    (Entails.refl _)

def r2_words15 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
  ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗
  ((a + 56#64) ↦₆₄ w.w7) ∗ ((a + 64#64) ↦₆₄ w.w8) ∗ ((a + 72#64) ↦₆₄ w.w9) ∗
  ((a + 80#64) ↦₆₄ w.w10) ∗ ((a + 88#64) ↦₆₄ w.w11) ∗ ((a + 96#64) ↦₆₄ w.w12) ∗
  ((a + 104#64) ↦₆₄ w.w13) ∗ ((a + 112#64) ↦₆₄ w.w14)

def r2_words3 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w15) ∗ ((a + 8#64) ↦₆₄ w.w16) ∗ ((a + 16#64) ↦₆₄ w.w17)

def r2_words13 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w18) ∗ ((a + 8#64) ↦₆₄ w.w19) ∗ ((a + 16#64) ↦₆₄ w.w20) ∗ ((a + 24#64) ↦₆₄ w.w21) ∗
  ((a + 32#64) ↦₆₄ w.w22) ∗ ((a + 40#64) ↦₆₄ w.w23) ∗ ((a + 48#64) ↦₆₄ w.w24) ∗
  ((a + 56#64) ↦₆₄ w.w25) ∗ ((a + 64#64) ↦₆₄ w.w26) ∗ ((a + 72#64) ↦₆₄ w.w27) ∗
  ((a + 80#64) ↦₆₄ w.w28) ∗ ((a + 88#64) ↦₆₄ w.w29) ∗ ((a + 96#64) ↦₆₄ w.w30)

theorem r2_words31_split (a : BitVec 64) (w : r2_SlotWords) :
    r2_words31 a w =
      r2_words15 a w ∗ r2_words3 (a + 120#64) w ∗ r2_words13 (a + 144#64) w := by
  unfold r2_words31 r2_words15 r2_words3 r2_words13
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem r2_optBox_reloc (A : RustAlloc) (src ptr : BitVec 64)
    (optBs : Option (List (BitVec 8))) :
    optBoxU8At A src ptr optBs ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ dst, (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ H ⊢ optBoxU8At A dst ptr optBs⌝ ∗
          (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ H := by
  cases optBs with
  | none =>
    dsimp only [optBoxU8At]
    rw [ProofLib.memRegion_eight (src + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1 (Entails.sepExists_right emp ?_))
    rw [sepConj_emp]
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [sepConj_emp]
    exact sepConj_mono_right (pointsTo64_entails_memRegion (dst + 8#64) w1)
  | some bs =>
    dsimp only [optBoxU8At]
    rw [r2_boxU8At_eq A src ptr bs]
    apply Entails.pure_left; intro hp
    refine Entails.sepExists_right ptr
      (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
        (Entails.sepExists_right ((ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs) ?_))
    refine Entails.pure_right (fun dst => ?_) (Entails.of_eq (by ac_rfl))
    rw [r2_boxU8At_eq A dst ptr bs]
    exact Entails.pure_right hp (Entails.of_eq (by ac_rfl))

theorem r2_optU32_reloc (src : BitVec 64) (o : Option (BitVec 32)) :
    optU32At src o ⊢
      ∃∗ w : BitVec 64, ⌜∀ dst, (dst ↦₆₄ w) ⊢ optU32At dst o⌝ ∗ (src ↦₆₄ w) := by
  cases o with
  | none =>
    dsimp only [optU32At]
    rw [r2_u32_pad4_eq src 0#32]
    apply Entails.sepExists_elim; intro hi
    refine Entails.sepExists_right (r2_pack8 (unpack32 0#32 ++ unpack32 hi)) ?_
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [r2_u32_pad4_eq dst 0#32]
    exact Entails.sepExists_right hi (Entails.refl _)
  | some v =>
    dsimp only [optU32At]
    rw [r2_u32_pair_eq_word src 1#32 v]
    refine Entails.sepExists_right (r2_pack8 (unpack32 1#32 ++ unpack32 v)) ?_
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [r2_u32_pair_eq_word dst 1#32 v]
    exact Entails.refl _

theorem r2_optKyber_reloc (A : RustAlloc) (src ptr : BitVec 64)
    (optK : Option KyberPayload) :
    optKyberAt A src ptr optK ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ dst,
          (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗ H ⊢
            optKyberAt A dst ptr optK⌝ ∗
        (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗ H := by
  cases optK with
  | none =>
    dsimp only [optKyberAt]
    rw [ProofLib.memRegion_split (src + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight (src + 8#64), ProofLib.memRegion_eight _]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right emp ?_)))
    simp only [sepConj_emp]
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [ProofLib.memRegion_split (dst + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion _ w1) (pointsTo64_entails_memRegion _ w2))
  | some k =>
    dsimp only [optKyberAt]
    have ha20 : src + 0x10#64 + 4#64 = src + 0x14#64 := by bv_omega
    rw [← ha20, r2_u32_pad4_eq (src + 0x10#64) k.preKeyId,
        r2_boxU8At_eq A src ptr k.ciphertext]
    simp only [sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi
    apply Entails.pure_left; intro hp
    let w2 := r2_pack8 (unpack32 k.preKeyId ++ unpack32 hi)
    let Hk := (ptr ↦ₛ k.ciphertext) ∗ r2_boxLive A ptr k.ciphertext
    refine Entails.sepExists_right ptr
      (Entails.sepExists_right (BitVec.ofNat 64 k.ciphertext.length)
        (Entails.sepExists_right w2 (Entails.sepExists_right Hk ?_)))
    refine Entails.pure_right (fun dst => ?_) (Entails.of_eq (by dsimp only [Hk, w2]; ac_rfl))
    have hd20 : dst + 0x10#64 + 4#64 = dst + 0x14#64 := by bv_omega
    rw [← hd20, r2_u32_pad4_eq (dst + 0x10#64) k.preKeyId,
        r2_boxU8At_eq A dst ptr k.ciphertext]
    have hhi :
        ((dst + 16#64) ↦₆₄ w2) ⊢
          ∃∗ hi' : BitVec 32, (dst + 0x10#64) ↦₆₄ r2_pack8 (unpack32 k.preKeyId ++ unpack32 hi') :=
      Entails.sepExists_right hi (Entails.refl _)
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhi))) ?_
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
    dsimp only [Hk, w2]; ac_rfl

theorem r2_pk32_eq_words4 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ r2_pack8 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ r2_pack8 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ r2_pack8 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ r2_pack8 (bs.drop 24))) :=
  r2_pointsToBytes32_eq_words4 a bs h

def r2_pqHeap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem r2_vecU8At_eq_pqHeap (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        r2_pqHeap A cap ptr bs := rfl

theorem r2_sigMsg_reloc (A : RustAlloc) (src : BitVec 64)
    (g : SignalMessageGhost) (m : SignalMessage) :
    signalMessageAt A g src m ⊢
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ H : SepProp,
        ⌜g.pqCap.toNat < 2 ^ 63 ∧
          ∀ dst,
            ((dst ↦₆₄ g.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.pqPtr) ∗
              ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
              ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗
              ((dst + 40#64) ↦₆₄ w5) ∗ ((dst + 48#64) ↦₆₄ w6) ∗
              ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
              ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10) ∗
              ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗
              ((dst + 104#64) ↦₆₄ w13) ∗ ((dst + 112#64) ↦₆₄ w14)) ∗ H ⊢
              signalMessageAt A g dst m⌝ ∗
        (((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
          ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗
          ((src + 40#64) ↦₆₄ w5) ∗ ((src + 48#64) ↦₆₄ w6) ∗
          ((src + 56#64) ↦₆₄ w7) ∗ ((src + 64#64) ↦₆₄ w8) ∗
          ((src + 72#64) ↦₆₄ w9) ∗ ((src + 80#64) ↦₆₄ w10) ∗
          ((src + 88#64) ↦₆₄ w11) ∗ ((src + 96#64) ↦₆₄ w12) ∗
          ((src + 104#64) ↦₆₄ w13) ∗ ((src + 112#64) ↦₆₄ w14)) ∗ H) := by
  unfold signalMessageAt
  apply Entails.pure_left; intro hdes
  have hsrk_len : m.senderRatchetKey.bytes.toList.length = 32 := by simp
  have hpq_lt :
      r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ⊢
        ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗ r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet := by
    unfold r2_pqHeap
    apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  rw [r2_vecU8At_eq_pqHeap A src g.pqCap g.pqPtr m.pqRatchet]
  try simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc_prev :
      ((src + 104#64) ↦₃₂ m.counter) ∗ ((src + 108#64) ↦₃₂ m.previousCounter) =
        ((src + 104#64) ↦₆₄ r2_pack8 (unpack32 m.counter ++ unpack32 m.previousCounter)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (src + 104#64) m.counter m.previousCounter
  have hv_pad :=
    r2_u8_pad7_reloc m.messageVersion (fun _ => rfl) (src + 112#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_pad
  have had_rel := r2_optBox_reloc A (src + 88#64) g.addrPtr m.addresses
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at had_rel
  rw [r2_boxU8At_eq A (src + 24#64) g.ctPtr m.ciphertext,
      r2_boxU8At_eq A (src + 40#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (src + 56#64) m.senderRatchetKey.bytes.toList hsrk_len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (Q :=
      optBoxU8At A (src + 88#64) g.addrPtr m.addresses ∗
        (((src + 112#64) ↦₈ m.messageVersion) ∗ memRegion (src + 113#64) 7) ∗
        r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
        (((src + 104#64) ↦₃₂ m.counter) ∗ ((src + 108#64) ↦₃₂ m.previousCounter)) ∗
        (⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗
          ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
            ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
            ((src + 24#64) ↦₆₄ g.ctPtr) ∗
            ((src + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
            ((src + 40#64) ↦₆₄ g.serPtr) ∗
            ((src + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
            ((src + 56#64) ↦₆₄ r2_pack8 (m.senderRatchetKey.bytes.toList.take 8)) ∗
            ((src + 64#64) ↦₆₄ r2_pack8 ((m.senderRatchetKey.bytes.toList.drop 8).take 8)) ∗
            ((src + 72#64) ↦₆₄ r2_pack8 ((m.senderRatchetKey.bytes.toList.drop 16).take 8)) ∗
            ((src + 80#64) ↦₆₄ r2_pack8 (m.senderRatchetKey.bytes.toList.drop 24))) ∗
          ((g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext ∗
            (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized)))
    (by ac_rfl)) ?_
  rw [hc_prev]
  refine Entails.trans
    (sepConj_mono had_rel (sepConj_mono hv_pad (sepConj_mono_left hpq_lt))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w11
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w12
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro Had
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w14
  let srk := m.senderRatchetKey.bytes.toList
  let w7 := r2_pack8 (srk.take 8)
  let w8 := r2_pack8 ((srk.drop 8).take 8)
  let w9 := r2_pack8 ((srk.drop 16).take 8)
  let w10 := r2_pack8 (srk.drop 24)
  let w13 := r2_pack8 (unpack32 m.counter ++ unpack32 m.previousCounter)
  let Htot : SepProp :=
    r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
      (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext ∗
      (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗ Had
  refine Entails.trans (Q :=
      ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
        ⌜∀ dst, ((dst ↦₆₄ w11) ∗ ((dst + 8#64) ↦₆₄ w12) ∗ Had) ⊢
          optBoxU8At A dst g.addrPtr m.addresses⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w14) ⊢ (dst ↦₈ m.messageVersion) ∗ memRegion (dst + 1#64) 7⌝ ∗
        ⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
        (((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
          ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          ((src + 24#64) ↦₆₄ g.ctPtr) ∗
          ((src + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          ((src + 40#64) ↦₆₄ g.serPtr) ∗
          ((src + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          ((src + 56#64) ↦₆₄ w7) ∗ ((src + 64#64) ↦₆₄ w8) ∗
          ((src + 72#64) ↦₆₄ w9) ∗ ((src + 80#64) ↦₆₄ w10) ∗
          ((src + 88#64) ↦₆₄ w11) ∗ ((src + 96#64) ↦₆₄ w12) ∗
          ((src + 104#64) ↦₆₄ w13) ∗ ((src + 112#64) ↦₆₄ w14)) ∗ Htot))
    (by dsimp only [Htot, srk, w7, w8, w9, w10, w13]; exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; intro hpq_cap
  apply Entails.pure_left; intro hclose_ad
  apply Entails.pure_left; intro hclose_ver
  apply Entails.pure_left; intro hct_p
  apply Entails.pure_left; intro hser_p
  refine Entails.sepExists_right g.ctPtr (Entails.sepExists_right
    (BitVec.ofNat 64 m.ciphertext.length) (Entails.sepExists_right g.serPtr
    (Entails.sepExists_right (BitVec.ofNat 64 m.serialized.length)
    (Entails.sepExists_right w7 (Entails.sepExists_right w8
    (Entails.sepExists_right w9 (Entails.sepExists_right w10
    (Entails.sepExists_right w11 (Entails.sepExists_right w12
    (Entails.sepExists_right w13 (Entails.sepExists_right w14
    (Entails.sepExists_right Htot ?_))))))))))))
  refine Entails.pure_right ⟨hpq_cap, fun dst => ?_⟩ (Entails.refl _)
  rw [r2_vecU8At_eq_pqHeap A dst g.pqCap g.pqPtr m.pqRatchet]
  try simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hdc_prev :
      ((dst + 104#64) ↦₃₂ m.counter) ∗ ((dst + 108#64) ↦₃₂ m.previousCounter) =
        ((dst + 104#64) ↦₆₄ w13) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (dst + 104#64) m.counter m.previousCounter
  rw [r2_boxU8At_eq A (dst + 24#64) g.ctPtr m.ciphertext,
      r2_boxU8At_eq A (dst + 40#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (dst + 56#64) srk hsrk_len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hd_ver : ((dst + 112#64) ↦₆₄ w14) ⊢
      ((dst + 112#64) ↦₈ m.messageVersion) ∗ memRegion (dst + 113#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ver (dst + 112#64)
  have hd_ad :
      ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗ Had ⊢
        optBoxU8At A (dst + 88#64) g.addrPtr m.addresses := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ad (dst + 88#64)
  have hd_ct :
      (((dst + 24#64) ↦₆₄ g.ctPtr) ∗ ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext) ⊢
        ⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗ ((dst + 24#64) ↦₆₄ g.ctPtr) ∗
          ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext :=
    Entails.pure_right hct_p (Entails.refl _)
  have hd_ser :
      (((dst + 40#64) ↦₆₄ g.serPtr) ∗ ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ⊢
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗ ((dst + 40#64) ↦₆₄ g.serPtr) ∗
          ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized :=
    Entails.pure_right hser_p (Entails.refl _)
  refine Entails.trans (Entails.of_eq (Q :=
      (((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗ Had) ∗ ((dst + 112#64) ↦₆₄ w14) ∗
        (((dst + 24#64) ↦₆₄ g.ctPtr) ∗ ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext) ∗
        (((dst + 40#64) ↦₆₄ g.serPtr) ∗ ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ∗
        (((dst + 104#64) ↦₆₄ w13) ∗
          ((dst ↦₆₄ g.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.pqPtr) ∗
            ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length)) ∗
          r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
          ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
          ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10)))
    (by dsimp only [Htot]; ac_rfl)) ?_
  rw [← hdc_prev]
  refine Entails.trans
    (sepConj_mono hd_ad (sepConj_mono hd_ver (sepConj_mono hd_ct (sepConj_mono_left hd_ser)))) ?_
  exact Entails.pure_right hdes (Entails.of_eq (by ac_rfl))

theorem r2_open_preKeyMessage (A : RustAlloc) (r : BitVec 64)
    (g : PreKeyMsgGhost) (m : PreKeySignalMessage) :
    preKeyMsgAt A g r m ⊢
      ∃∗ ws : r2_SlotWords, ∃∗ H : SepProp,
        ⌜ws.w0.toNat < 2 ^ 63 ∧
          ws.w16 = g.serPtr ∧ ws.w17 = BitVec.ofNat 64 m.serialized.length ∧
          g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63 ∧
          (∀ dst : BitVec 64,
            r2_words31 dst ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ H ⊢
              preKeyMsgAt A g dst m)⌝ ∗
        r2_words31 r ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ H := by
  unfold preKeyMsgAt
  have h15 := r2_sigMsg_reloc A r g.msg m.message
  have hu32 := r2_optU32_reloc (r + 0x78#64) m.preKeyId
  have hkyb := r2_optKyber_reloc A (r + 0x90#64) g.kyberPtr m.kyberPayload
  have hbk_len : m.baseKey.bytes.toList.length = 32 := by simp
  have hik_len : m.identityKey.publicKey.bytes.toList.length = 32 := by simp
  have hreg_spk :
      ((r + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((r + 0xec#64) ↦₃₂ m.signedPreKeyId) =
        ((r + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (r + 232#64) m.registrationId m.signedPreKeyId
  have hver := r2_u8_pad7_reloc m.messageVersion (fun _ => rfl) (r + 0xf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkyb hver
  rw [r2_boxU8At_eq A (r + 0x80#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (r + 0xa8#64) m.baseKey.bytes.toList hbk_len,
      r2_pk32_eq_words4 (r + 0xc8#64) m.identityKey.publicKey.bytes.toList hik_len]
  refine Entails.trans (Entails.of_eq (Q :=
      signalMessageAt A g.msg r m.message ∗
        optU32At (r + 0x78#64) m.preKeyId ∗
        optKyberAt A (r + 144#64) g.kyberPtr m.kyberPayload ∗
        (((r + 240#64) ↦₈ m.messageVersion) ∗ memRegion (r + 241#64) 7) ∗
        (((r + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((r + 0xec#64) ↦₃₂ m.signedPreKeyId)) ∗
        (⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((r + 128#64) ↦₆₄ g.serPtr) ∗
          ((r + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
          ((r + 168#64) ↦₆₄ r2_pack8 (m.baseKey.bytes.toList.take 8)) ∗
          ((r + 176#64) ↦₆₄ r2_pack8 ((m.baseKey.bytes.toList.drop 8).take 8)) ∗
          ((r + 184#64) ↦₆₄ r2_pack8 ((m.baseKey.bytes.toList.drop 16).take 8)) ∗
          ((r + 192#64) ↦₆₄ r2_pack8 (m.baseKey.bytes.toList.drop 24)) ∗
          ((r + 200#64) ↦₆₄ r2_pack8 (m.identityKey.publicKey.bytes.toList.take 8)) ∗
          ((r + 208#64) ↦₆₄ r2_pack8 ((m.identityKey.publicKey.bytes.toList.drop 8).take 8)) ∗
          ((r + 216#64) ↦₆₄ r2_pack8 ((m.identityKey.publicKey.bytes.toList.drop 16).take 8)) ∗
          ((r + 224#64) ↦₆₄ r2_pack8 (m.identityKey.publicKey.bytes.toList.drop 24))))
    (by (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); ac_rfl)) ?_
  rw [hreg_spk]
  refine Entails.trans
    (sepConj_mono h15 (sepConj_mono hu32 (sepConj_mono hkyb (sepConj_mono_left hver)))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w5
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w6
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w7
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w9
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w10
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w11
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w12
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w13
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w14
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro H15
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w15
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w18
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w19
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w20
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro Hkyb
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w30
  let bk := m.baseKey.bytes.toList
  let ik := m.identityKey.publicKey.bytes.toList
  let ws : r2_SlotWords :=
    ⟨g.msg.pqCap, g.msg.pqPtr, BitVec.ofNat 64 m.message.pqRatchet.length,
     w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
     w15, g.serPtr, BitVec.ofNat 64 m.serialized.length, w18, w19, w20,
     r2_pack8 (bk.take 8), r2_pack8 ((bk.drop 8).take 8),
     r2_pack8 ((bk.drop 16).take 8), r2_pack8 (bk.drop 24),
     r2_pack8 (ik.take 8), r2_pack8 ((ik.drop 8).take 8),
     r2_pack8 ((ik.drop 16).take 8), r2_pack8 (ik.drop 24),
     r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId), w30⟩
  let Htot : SepProp := H15 ∗ r2_boxLive A g.serPtr m.serialized ∗ Hkyb
  refine Entails.trans (Q :=
      ⌜g.msg.pqCap.toNat < 2 ^ 63 ∧
        ∀ dst : BitVec 64,
          ((dst ↦₆₄ g.msg.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.msg.pqPtr) ∗
            ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.message.pqRatchet.length) ∗
            ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗
            ((dst + 40#64) ↦₆₄ w5) ∗ ((dst + 48#64) ↦₆₄ w6) ∗
            ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
            ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10) ∗
            ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗
            ((dst + 104#64) ↦₆₄ w13) ∗ ((dst + 112#64) ↦₆₄ w14) ∗ H15) ⊢
            signalMessageAt A g.msg dst m.message⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w15) ⊢ optU32At dst m.preKeyId⌝ ∗
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
        ⌜∀ dst,
          (dst ↦₆₄ w18) ∗ ((dst + 8#64) ↦₆₄ w19) ∗ ((dst + 16#64) ↦₆₄ w20) ∗ Hkyb ⊢
            optKyberAt A dst g.kyberPtr m.kyberPayload⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w30) ⊢ (dst ↦₈ m.messageVersion) ∗ memRegion (dst + 1#64) 7⌝ ∗
        r2_words31 r ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ Htot)
    (by unfold r2_words31; dsimp only [ws, Htot, bk, ik]
        exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hpq_lt, hclose15⟩
  apply Entails.pure_left; intro hclose_u32
  apply Entails.pure_left; rintro ⟨hser_ne, hser_lt⟩
  apply Entails.pure_left; intro hclose_kyb
  apply Entails.pure_left; intro hclose_ver
  refine Entails.sepExists_right ws (Entails.sepExists_right Htot ?_)
  refine Entails.pure_right ⟨hpq_lt, rfl, rfl, hser_ne, hser_lt, fun dst => ?_⟩ (Entails.refl _)
  rw [r2_words31_split dst ws]
  have hd_reg_spk :
      ((dst + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((dst + 0xec#64) ↦₃₂ m.signedPreKeyId) =
        ((dst + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (dst + 232#64) m.registrationId m.signedPreKeyId
  rw [r2_boxU8At_eq A (dst + 0x80#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (dst + 0xa8#64) bk hbk_len,
      r2_pk32_eq_words4 (dst + 0xc8#64) ik hik_len]
  have hd_u32 : ((dst + 120#64) ↦₆₄ w15) ⊢ optU32At (dst + 0x78#64) m.preKeyId :=
    hclose_u32 (dst + 0x78#64)
  have hd_kyb :
      ((dst + 144#64) ↦₆₄ w18) ∗ ((dst + 152#64) ↦₆₄ w19) ∗ ((dst + 160#64) ↦₆₄ w20) ∗ Hkyb ⊢
        optKyberAt A (dst + 0x90#64) g.kyberPtr m.kyberPayload := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_kyb (dst + 0x90#64)
  have hd_ver :
      ((dst + 240#64) ↦₆₄ w30) ⊢
        ((dst + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (dst + 0xf1#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ver (dst + 0xf0#64)
  have hd_ser :
      ((dst + 128#64) ↦₆₄ g.serPtr) ∗ ((dst + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ⊢
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((dst + 0x80#64) ↦₆₄ g.serPtr) ∗
          ((dst + 0x80#64 + 8#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.pure_right ⟨hser_ne, hser_lt⟩ (Entails.refl _)
  have hd_15 : r2_words15 dst ws ∗ H15 ⊢ signalMessageAt A g.msg dst m.message := by
    unfold r2_words15; dsimp only [ws]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (hclose15 dst)
  refine Entails.trans (Entails.of_eq (Q :=
      (r2_words15 dst ws ∗ H15) ∗ ((dst + 120#64) ↦₆₄ w15) ∗
        (((dst + 128#64) ↦₆₄ g.serPtr) ∗
          ((dst + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ∗
        (((dst + 144#64) ↦₆₄ w18) ∗ ((dst + 152#64) ↦₆₄ w19) ∗ ((dst + 160#64) ↦₆₄ w20) ∗ Hkyb) ∗
        ((dst + 240#64) ↦₆₄ w30) ∗
        (((dst + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) ∗
          ((dst + 0xa8#64) ↦₆₄ r2_pack8 (bk.take 8)) ∗
          ((dst + 0xa8#64 + 8#64) ↦₆₄ r2_pack8 ((bk.drop 8).take 8)) ∗
          ((dst + 0xa8#64 + 16#64) ↦₆₄ r2_pack8 ((bk.drop 16).take 8)) ∗
          ((dst + 0xa8#64 + 24#64) ↦₆₄ r2_pack8 (bk.drop 24)) ∗
          ((dst + 0xc8#64) ↦₆₄ r2_pack8 (ik.take 8)) ∗
          ((dst + 0xc8#64 + 8#64) ↦₆₄ r2_pack8 ((ik.drop 8).take 8)) ∗
          ((dst + 0xc8#64 + 16#64) ↦₆₄ r2_pack8 ((ik.drop 16).take 8)) ∗
          ((dst + 0xc8#64 + 24#64) ↦₆₄ r2_pack8 (ik.drop 24))))
    (by unfold r2_words3 r2_words13; dsimp only [ws, Htot]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); ac_rfl)) ?_
  rw [← hd_reg_spk]
  refine Entails.trans
    (sepConj_mono hd_15
      (sepConj_mono hd_u32
        (sepConj_mono hd_ser
          (sepConj_mono hd_kyb (sepConj_mono_left hd_ver))))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
