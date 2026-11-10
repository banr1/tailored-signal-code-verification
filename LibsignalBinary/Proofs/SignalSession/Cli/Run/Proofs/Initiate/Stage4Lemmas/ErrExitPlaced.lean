/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.DecodePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.FramesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Stage 4 Stack/OOM Helpers and Early `Err` Exit (`[LibsignalPlacement]`, `+4508 → RET`)

Relocatable `[LibsignalPlacement]` `SepWPp` call/step combinators, OOM panic entailments,
`errExitMemPlaced`, and `stage4_err_exit_placed` (`+4508 → RET`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

/-! ## OOM Panic and `SepWPp` Call Helpers -/

theorem panic_oom_entails_initOnPanic_placed [LibsignalPlacement] (A : RustAlloc) (S : RunSem)
    (x : InitGhost) (stk : Nat) (s0 s sm : State) (F : SepProp) (φ : Prop)
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sm ∧ φ⌝ ∗ anyHeap) ∗ F ⊢
      (initSlotSpecPlaced A S stk).onPanic x s0 sm := by
  dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  exact Entails.pure_left fun h =>
    Entails.pure_right (Or.inr (allocFailedIn_of_trace_eq' htr h.1)) (entails_anyHeap _)

theorem panic_oom_only_entails_initOnPanic_placed [LibsignalPlacement] (A : RustAlloc) (S : RunSem)
    (x : InitGhost) (stk : Nat) (s0 s sm : State) (F : SepProp)
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sm⌝ ∗ anyHeap) ∗ F ⊢
      (initSlotSpecPlaced A S stk).onPanic x s0 sm := by
  dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  exact Entails.pure_left fun h =>
    Entails.pure_right (Or.inr (allocFailedIn_of_trace_eq' htr h)) (entails_anyHeap _)

theorem sepWPp_step_to_lscro [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog ret sm Pm Q Qp oom)) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hfalse⟩⟩
  · have hinv_m := hinv.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := hnext hinv_m R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem sepWPp_call_wpp_split_plain [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    (x : α) {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hsplit : P = T ∗ F)
    (hpreT : T ⊢ spec.pre x s)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq hsplit) (sepConj_mono_left hpreT))) hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ |
    ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan ⟨F ∗ R, by rwa [sepConj_assoc] at hpost⟩⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

theorem sepWPp_call_wpp_split_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (x : α) {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hsplit : P = T ∗ F)
    (hpreT : T ⊢ spec.pre x s)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine sepWPp_call_wpp_split_plain hcall x hinv hpc hrun hsp hlr hsplit ?_ hexit hpanic hnext hoom
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_comm]
  exact Entails.pure_right hinv hpreT

/-! ## Error Cleanup Spatial Bundle and Proof (`+4508 → RET`) -/

def errExitMemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost)
    (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr kemCtPtr w70 w78 : BitVec 64) (opkId : BitVec 32)
    (Rest5ba Leak : SepProp) (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗
    memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗
    A.pool ∗
    initSaved s0 ∗
    memRegion fsp 0x60 ∗
    ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
    A.live kemCtPtr 1569 1 ∗ memRegion kemCtPtr 1569 ∗
    ((fsp + 0x70#64) ↦₆₄ w70) ∗ ((fsp + 0x78#64) ↦₆₄ w78) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗
    ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    Rest5ba ∗
    ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
    memRegion (fsp + 5648#64) 40 ∗
    Leak ∗
    stackAt fsp (stk - cliInitiateFrame)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem stage4_err_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr kemCtPtr w70 w78 : BitVec 64} {opkId : BitVec 32}
    {Rest5ba Leak : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    {s : State}
    (hctrl : InInitiatePlaced s0 s 4508)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hekA : ekAPk.length = 32)
    (hekASk : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (_hpqspkNonNull : pqspkPtr ≠ 0#64)
    (_hkemNonNull : kemCtPtr ≠ 0#64)
    (herr : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hRest : Rest5ba ∗ memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5640#64) 48 ⊢
      memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x5ba#64) (initLocalsSize - 0x5ba)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (errExitMemPlaced A x kp ekASk ekAPk pqspkPtr kemCtPtr w70 w78 opkId Rest5ba Leak stk s0)
      Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hfsp_eq : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp := rfl
  have hsaved_fsp : s0.sp - 0x60#64 = fsp + 7312#64 := by
    dsimp only [fsp, cliInitiateFrame]; bv_omega
  have hs0_sp_fsp : s0.sp = fsp + 7408#64 := by
    dsimp only [fsp, cliInitiateFrame]; bv_omega
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl.spAligned
  have hdealloc := dealloc_ok_at_init_placed hh
  have hpc_start : s.pc = (blkPl_521).base + 4508#64 := hctrl.pc
  have hrun_start : s.status = .Running := hctrl.run
  have hsp_start : s.sp = fsp := hctrl.sp
  have halign_start : s.spAligned = true := hfsp_align s hsp_start
  have hx19_start : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hvregs_start : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
      (Pf ⊢ storesAt A x.stores StoresGhost.opened ∗
        initResAt A x.ret (.error (.protocol .invalidKeyAgreement)) ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp stk ∗ anyHeap))
  ·
    unfold errExitMemPlaced
    conv => arg 4; dsimp only
    rw [hfsp_eq,
      cells5_eq_memRegion40 (fsp + 5648#64),
      stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)]
    s4_elim_exists e0; s4_elim_exists e1; s4_elim_exists e2
    s4_elim_exists e3; s4_elim_exists e4
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply sepWPp_step_to_lscro hctrl.inv (mid := lsρ lsRustDeallocSymCli)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs1_inv
    have h48 := cells6_entails_memRegion48 (fsp + 5640#64) (speWord 10) e0 e1 e2 e3 e4
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
    have h5ba : (Rest5ba ∗ (((fsp + 5640#64) ↦₆₄ speWord 10) ∗
        ((fsp + 5648#64) ↦₆₄ e0) ∗ ((fsp + 5656#64) ↦₆₄ e1) ∗
        ((fsp + 5664#64) ↦₆₄ e2) ∗ ((fsp + 5672#64) ↦₆₄ e3) ∗
        ((fsp + 5680#64) ↦₆₄ e4))) ⊢
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) :=
      Entails.trans (sepConj_mono (Entails.refl _) h48) hRest
    s4_fold_pre h5ba
    refine sepWPp_call_wpp_split_lscro hdealloc (kemCtPtr, 1569, 1)
      (T := A.pool ∗ A.live kemCtPtr 1569 1 ∗ memRegion kemCtPtr 1569 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs1_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [rustDeallocExternSpecWithStack]
      have hs1_sp_eq := lscro_sp_eq hs1_inv fsp (by wp_norm_goal)
      rw [hs1_sp_eq]
      exact Entails.pure_right
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩
        (Entails.of_eq (by s4_ac_rfl))
    intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_inv
    dsimp only [rustDeallocExternSpecWithStack]
    have hs1_sp_eq := lscro_sp_eq hs1_inv fsp (by wp_norm_goal)
    rw [hs1_sp_eq]
    s4_pure_elim
    intro hs2_tr_eq
    have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans (by wp_norm_goal)
    have hs2_sp' : s2.sp = fsp := hs2_sp.trans hs1_sp_eq
    have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
    have hs2_x19 : s2.readReg64 (.gpr 19#5) = x.ret :=
      (hs2_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs2_x26 : s2.readReg64 (.gpr 26#5) = speWord 10 :=
      (hs2_cs.gpr ⟨26, by decide⟩).trans (by wp_norm_goal)
    have hs2_x27 : s2.readReg64 (.gpr 27#5) = e0 :=
      (hs2_cs.gpr ⟨27, by decide⟩).trans (by wp_norm_goal)
    have hs2_x25 : s2.readReg64 (.gpr 25#5) = e1 :=
      (hs2_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs2_x28 : s2.readReg64 (.gpr 28#5) = e2 :=
      (hs2_cs.gpr ⟨28, by decide⟩).trans (by wp_norm_goal)
    have hs2_x24 : s2.readReg64 (.gpr 24#5) = e3 :=
      (hs2_cs.gpr ⟨24, by decide⟩).trans (by wp_norm_goal)
    have hs2_x21 : s2.readReg64 (.gpr 21#5) = e4 :=
      (hs2_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvregs_start
    have hs2_pc' : s2.pc = (blkPl_521).base + 4828#64 := by
      rw [hs2_pc]; wp_norm_goal
    unfold stage3KeySlotsAt
    conv => arg 4; dsimp only
    rw [hfsp_eq]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hkpk_mem : (pqspkPtr ↦ₛ x.bundle.kpk) ⊢ memRegion pqspkPtr 1568 :=
      hkpkLen ▸ pointsToBytes_entails_memRegion pqspkPtr x.bundle.kpk
    s4_fold_pre hkpk_mem
    apply sepWPp_step_to_lscro hs2_inv (mid := lsρ lsRustDeallocSymCli)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs3_inv
    refine sepWPp_call_wpp_split_lscro hdealloc (pqspkPtr, 1568, 1)
      (T := A.pool ∗ A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs3_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [rustDeallocExternSpecWithStack]
      have hs3_sp_eq := lscro_sp_eq hs3_inv fsp (by wp_norm_goal)
      rw [hs3_sp_eq]
      exact Entails.pure_right
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩
        (Entails.of_eq (by s4_ac_rfl))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs _hs4_inv
    dsimp only [rustDeallocExternSpecWithStack]
    have hs3_sp_eq := lscro_sp_eq hs3_inv fsp (by wp_norm_goal)
    rw [hs3_sp_eq]
    s4_pure_elim
    intro hs4_tr_eq
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans (by wp_norm_goal)
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
    have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = x.ret :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs4_x26 : s4.readReg64 (.gpr 26#5) = speWord 10 :=
      (hs4_cs.gpr ⟨26, by decide⟩).trans (by wp_norm_goal)
    have hs4_x27 : s4.readReg64 (.gpr 27#5) = e0 :=
      (hs4_cs.gpr ⟨27, by decide⟩).trans (by wp_norm_goal)
    have hs4_x25 : s4.readReg64 (.gpr 25#5) = e1 :=
      (hs4_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs4_x28 : s4.readReg64 (.gpr 28#5) = e2 :=
      (hs4_cs.gpr ⟨28, by decide⟩).trans (by wp_norm_goal)
    have hs4_x24 : s4.readReg64 (.gpr 24#5) = e3 :=
      (hs4_cs.gpr ⟨24, by decide⟩).trans (by wp_norm_goal)
    have hs2_x21_4 : s4.readReg64 (.gpr 21#5) = e4 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hs4_cs.vregs.trans hs2_vr
    have hs4_pc' : s4.pc = (blkPl_521).base + 5500#64 := by
      rw [hs4_pc]; wp_norm_goal
    rw [cells6_eq_memRegion48 x.ret]
    unfold initFreshRecAt initSaved
    conv => arg 4; dsimp only
    rw [hsaved_fsp]
    s4_elim_exists r0; s4_elim_exists r1; s4_elim_exists r2
    s4_elim_exists r3; s4_elim_exists r4; s4_elim_exists r5
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcond1 := cond_eq_adds_neg1_1
    have hcond2 := cond_ne_adds_speWord10_3
    apply SepWPp.of_sepWP_ret
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by rw [hs0_sp_fsp]; wp_norm_goal, ?_, by wp_norm_goal, ?_⟩
    · exact ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr⟩
    · have hspe := speWord10_cells5_entails_initResAt A x.ret e0 e1 e2 e3 e4
      have hany : Leak ⊢ anyHeap := entails_anyHeap _
      have hd0 := stage4Prefix_0xd0_merge fsp kemCtPtr w70 w78
      have hsaved_mem := initSaved_entails_memRegion s0
      have hstk_back := (stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)).symm
      have hstk_full := stage4FrameRegions_placed_entails_stackAt hstk hstk64 x kp ekASk ekAPk
        pqspkPtr opkId 0#8 0#8 s0 hekA hekASk
      have heq_saved :
          ((fsp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((fsp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((fsp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
          ((fsp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
          ((fsp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
          ((fsp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
          ((fsp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
          ((fsp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
          ((fsp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((fsp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((fsp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((fsp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) =
            initSaved s0 := by
        unfold initSaved
        dsimp only
        rw [hsaved_fsp]
        simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
      have heq_fresh :
          ((fsp + 0x128#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
          ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) =
            initFreshRecAt fsp := rfl
      s4_fold_ent hspe
      s4_fold_ent hany
      s4_fold_ent hd0
      s4_rw_ent heq_saved
      s4_fold_ent hsaved_mem
      s4_rw_ent heq_fresh
      s4_rw_ent hstk_back
      s4_fold_ent hstk_full
      exact Entails.of_eq (by s4_ac_rfl)
  ·
    intro sf Pf hsteps ⟨hsp, hcs, htr_sf, hent⟩
    apply hpost
    refine ⟨hsp, hcs, ?_⟩
    have hfiles_sf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hh.fs hsteps
        (htr_sf.trans htr.symm)).trans hctrl.files0
    have hslotTr : slotTrace s0 sf :=
      ⟨by rw [htr_sf], hfiles_sf, by rw [htr_sf]⟩
    have hslotOut : slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins)
        StoresGhost.opened (.error (.protocol .invalidKeyAgreement)) s0 sf :=
      ⟨by decide, by decide, herr⟩
    dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    exact Entails.trans hent
      (Entails.sepExists_right StoresGhost.opened
        (Entails.sepExists_right (.error (.protocol .invalidKeyAgreement))
          (Entails.pure_right ⟨hslotTr, hslotOut⟩ (Entails.refl _))))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
