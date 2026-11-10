/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Stage 1 Frame Combinators and Early Error Exits

Provides `[LibsignalPlacement]` Stage 1 `SepWPp` stepping (`sepWPp_step_to_placed`) and shared early
`Err` exit paths (`stage1_plain11_exit_placed_ok`, `stage1_untrusted_exit_placed_ok`), while
re-exporting pure frame/layout lemmas from `SegPrologueHelpers`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-- Steps a `SepWP` basic-block segment inside `SepWPp` under `StoreKit.LibsignalCodeRoLoaded lsmpl`. -/
theorem sepWPp_step_to_placed [LibsignalPlacement] {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => ∀ sNext : State, sm = sNext →
        sNext.pc = mid → sNext.status = .Running →
        LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sNext.mem →
        SepWPp prog ret sNext Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext sm rfl hpc hrun (hinv.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

set_option maxHeartbeats 2400000 in
/-- `SpeOwned.plain 11` (`SignatureValidationFailed`) error return from `0x0350` on `initProgPlaced`. -/
theorem stage1_plain11_exit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 11) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A x stk s0) Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_mono_pre ?_
    (stage1_epilogue_err_placed_ok hstk hstk64 hctrl htr hx8 hans hpost
      (H_err := emp)
      (H_extra := coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt)
      (by
        rw [sepConj_emp]
        exact words_to_plain11_initResAt A x.ret
          (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
          (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 28#5))
          (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 21#5)) hx26))
  unfold stage2MemPlaced
  dsimp only [fsp]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (stage2LocalsPlaced_entails_memRegion fsp x s0)))))))))))
  sep_frame

set_option maxHeartbeats 2400000 in
/-- Untrusted-identity `Err` exit (`0x0244 → String::clone → 0x026c → 0x0350 → ret`) on `initProgPlaced`. -/
theorem stage1_untrusted_exit_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0244)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (htr : s.trace = s0.trace)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A x stk s0) Q Qp (initOom s0) := by
  have hpc : s.pc = (blkPl_521).base + 580#64 := hctrl.pc
  have hrun := hctrl.run; have hsp := hctrl.sp
  have hfp := hctrl.fp; have hx19 := hctrl.x19; have hfs0 := hctrl.files0
  have hvregs := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal := InInitiatePlaced.spAligned_cur hctrl
  unfold stage2MemPlaced; dsimp only; rw [← hsp]
  have hsplit5ba :
      memRegion (s.sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1600#64) 24 ∗
          (∃∗ b0 : BitVec 8, (s.sp + 0x1618#64) ↦₈ b0) ∗
          memRegion (s.sp + 0x1619#64) 7 ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) := by
    rw [show initLocalsSize - 0x5ba = (0x1600 - 0x5ba) + (24 + (1 + (7 + (initLocalsSize - 0x1620)))) by decide,
      memRegion_split (s.sp + 0x5ba#64) (0x1600 - 0x5ba) _ (by decide),
      memRegion_split _ 24 _ (by decide),
      memRegion_split _ 1 _ (by decide), ProofLib.memRegion_one,
      memRegion_split _ 7 _ (by decide)]
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit5ba]
  refine sepWPp_mono_pre (P' :=
      ∃∗ b0 : BitVec 8,
        ((s.sp + 0x1618#64) ↦₈ b0) ∗
        memRegion (s.sp + 0x1619#64) 7 ∗
        memRegion (s.sp + 0x1600#64) 24 ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro b0
      exact Entails.sepExists_right b0 (by sep_frame)) ?_
  refine sepWPp_exists_elim fun b0 => ?_
  unfold initArgsAtPlaced
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_placed (lsmpl.base 623) hctrl.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sClone hsClone hpcC hrunC hinvC
  have hspC : sClone.sp = s.sp := by rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx0C : sClone.readReg64 .x0 = x.peerA := by rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx8C : sClone.readReg64 .x8 = s.sp + 0x1600#64 := by
    rw [← hsClone]; simp [wp_norm, arm64_norm, hsp]; try bv_omega
  have hlrC : sClone.readReg64 .lr = initPcPlaced 0x0258 := by
    rw [← hsClone]
    change _ = (blkPl_521).base + 600#64
    simp [wp_norm, arm64_norm]; try bv_omega
  have hx20C : sClone.readReg64 (.gpr 20#5) = x.peerA := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx21C : sClone.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := by
    rw [← hsClone]; simp [wp_norm, arm64_norm, hx21]
  have hfpC : sClone.readReg64 .fp = s.readReg64 .fp := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx19C : sClone.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hvregsC : calleeSavedVRegs sClone = calleeSavedVRegs s0 := by
    rw [← hsClone]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs]
  have htrC : sClone.trace = s0.trace := by rw [← hsClone]; simp [wp_norm, arm64_norm, htr]
  have hfsC : sClone.fs.files = s0.fs.files := by rw [← hsClone]; simp [wp_norm, arm64_norm, hfs0]
  have halC : sClone.spAligned = true := by simpa only [State.spAligned, hspC] using hal
  clear hsClone
  have hclone := init_stringClone_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
  have hpcC' : sClone.pc = lsmpl.base 623 := hpcC
  change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sClone _ Q Qp (initOom s0)
  refine sepWPp_mono_pre (P' :=
      ((stringCloneAtStkSpec A (stk - cliInitiateFrame)).pre
        (x.peerA, s.sp + 0x1600#64, x.peer.name) sClone) ∗
      (((s.sp + 0x1618#64) ↦₈ b0) ∗ memRegion (s.sp + 0x1619#64) 7 ∗
        (((x.peerA + asm64% addrDeviceOff) ↦₈ x.peer.device) ∗
          memRegion (x.peerA + asm64% (addrDeviceOff + 1))
            (asm% (protocolAddressSize - (addrDeviceOff + 1)))) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620))) ?_ ?_
  · unfold stringCloneAtStkSpec protocolAddressAt initArgsAtPlaced
    dsimp only
    rw [hspC]
    repeat rw [sepConj_assoc]
    exact pure_sepConj_intro ⟨hx0C, hx8C⟩ (by sep_frame)
  refine initCallLscro hh hpanic hclone hpcC' hrunC halC hinvC htrC hfsC hlrC
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sm hpcM hrunM hspM hcsM hinvM hfsM
  unfold stringCloneAtStkSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun htrM => ?_
  have htrM' : sm.trace = s0.trace := htrM.trans htrC
  have hfsM' : sm.fs.files = s0.fs.files := hfsM htrM'
  have hspM' : sm.sp = s.sp := hspM.trans hspC
  have hx20M : sm.readReg64 (.gpr 20#5) = x.peerA := (cs_x20 hcsM).trans hx20C
  have hx21M : sm.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := (cs_x21 hcsM).trans hx21C
  refine sepWPp_mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (vecU8_unpack_words A (s.sp + 0x1600#64) x.peer.val.name)))
      (Entails.refl _)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun cap => ?_
  refine sepWPp_exists_elim fun ptr => ?_
  have haddr1618 : (s.sp + 0xfe0#64) + 0x638#64 = s.sp + 0x1618#64 := by bv_omega
  change sm.pc = (blkPl_521).base + 600#64 at hpcM
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_placed ((blkPl_521).base + 620#64) hinvM ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sMid hsMid hpcMid hrunMid hinvMid
  have hspMid : sMid.sp = s.sp := by rw [← hsMid]; simp [wp_norm, arm64_norm, hspM']
  have hx27Mid : sMid.readReg64 (.gpr 27#5) = cap := by rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hx25Mid : sMid.readReg64 (.gpr 25#5) = ptr := by rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hx28Mid : sMid.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
    rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hfpMid : sMid.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, cs_fp hcsM, hfpC, hfp]
  have hx19Mid : sMid.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, cs_x19 hcsM, hx19C, hx19]
  have hvregsMid : calleeSavedVRegs sMid = calleeSavedVRegs s0 := by
    rw [← hsMid]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsM, hvregsC]
  have htrMid : sMid.trace = s0.trace := by rw [← hsMid]; simp [wp_norm, arm64_norm, htrM']
  have hfsMid : sMid.fs.files = s0.fs.files := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, hfsM']
  clear hsMid
  have hdev8 : BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
    bv_bits
  have htrunc8 : BitVec.truncate 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
    bv_bits
  try rw [haddr1618]
  try rw [hdev8]
  try rw [htrunc8]
  refine sepWPp_mono_pre (P' :=
      ((∃∗ w4 : BitVec 64,
          ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗
          ((s.sp + 0x1618#64) ↦₆₄ w4)) ∗
        ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
        ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
        ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
        stage1VecBuf A cap ptr x.peer.val.name ∗
        protocolAddressAt A x.peer x.peerA ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))) ?_ ?_
  · rw [hspC]
    unfold protocolAddressAt
    have hpack4 : ((s.sp + 0x1618#64) ↦₈ x.peer.device) ∗ memRegion (s.sp + 0x1619#64) 7 ⊢
        ∃∗ w4 : BitVec 64, ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗ ((s.sp + 0x1618#64) ↦₆₄ w4) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        byte_and_pad7_entails_word64 (s.sp + 0x1618#64) x.peer.device
    refine Entails.trans ?_ (sepConj_mono_left hpack4)
    sep_frame
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun w4 => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun hw4 => ?_
  refine sepWPp_step_to_placed ((blkPl_521).base + 848#64) hinvMid ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sErr hsErr hpcErr hrunErr hinvErr
  have hspErr : sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hspMid, hsp]
  have hfpErr : sErr.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hfpMid]
  have hx19Err : sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx19Mid]
  have hvregsErr : calleeSavedVRegs sErr = calleeSavedVRegs s0 := by
    rw [← hsErr]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsMid]
  have hfsErr : sErr.fs.files = s0.fs.files := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hfsMid]
  have htrErr : sErr.trace = s0.trace := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, htrMid]
  have hx26Err : sErr.readReg64 (.gpr 26#5) = speWord speUntrustedIdentity := by
    rw [← hsErr]; simp [wp_norm, arm64_norm]; rfl
  have hx27Err : sErr.readReg64 (.gpr 27#5) = cap := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx27Mid]
  have hx25Err : sErr.readReg64 (.gpr 25#5) = ptr := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx25Mid]
  have hx28Err : sErr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx28Mid]
  have hx24Err : sErr.readReg64 (.gpr 24#5) = w4 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm]
  clear hsErr
  have hctrlErr : InInitiatePlaced s0 sErr 0x0350 :=
    ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
  have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
    rw [hS]
    exact initDef_eq_some_none_of_trust_false X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
      x.bundle x.coins htrustF
  change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sErr _ Q Qp (initOom s0)
  refine sepWPp_mono_pre ?_
    (stage1_epilogue_err_placed_ok hstk hstk64 hctrlErr htrErr hx8 hans hpost
      (H_err := stage1VecBuf A cap ptr x.peer.val.name)
      (H_extra := coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt)
      (by
        rw [hx27Err, hx25Err]
        exact words_to_untrusted_initResAt A x.ret x.peer.val
          (sErr.readReg64 (.gpr 26#5)) cap ptr
          (sErr.readReg64 (.gpr 28#5))
          (sErr.readReg64 (.gpr 24#5)) (sErr.readReg64 (.gpr 21#5))
          hx26Err hx28Err (hx24Err ▸ hw4)))
  rw [← hsp]
  have hlocMerge :
      memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        (memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
          ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
          ((s.sp + 0x1618#64) ↦₆₄ w4) ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620)) ⊢
        memRegion s.sp initLocalsSize := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right ?_)))))
      (stage2LocalsPlaced_entails_memRegion s.sp x s0)
    have m64 := pointsTo64_entails_memRegion
    refine Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _)
      (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _) (Entails.refl _)))))) ?_
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1600#64) (0x1600 - 0x5ba) 8 (0x1608 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1608#64) (0x1608 - 0x5ba) 8 (0x1610 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1610#64) (0x1610 - 0x5ba) 8 (0x1618 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1618#64) (0x1618 - 0x5ba) 8 (0x1620 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1620#64) (0x1620 - 0x5ba) (initLocalsSize - 0x1620)
      (initLocalsSize - 0x5ba) (by bv_omega) (by decide) (by decide)]
    exact Entails.refl _
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hlocMerge))))))))))
  sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
