/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGenPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5

/-!
# Relocatable `[LibsignalPlacement]` Poll Stage P3 Instantiations

Proves `StageP3PrevEmptyVRegsPlacedStmt`, `StageP3GenStepsVRegsPlacedStmt`, and
`StageP3Prev1VRegsA0PlacedStmt` (plus `LibsignalFrozen` variants) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp decryptPrekeyClosureName eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem stageP3PrevEmpty_m3_placed_inst [LibsignalPlacement] :
    Matched.StageP3PrevEmptyVRegsM3PlacedStmt :=
  Matched.stageP3Gen_prevEmpty_vregs_placed_ok_of_clone cloneGen_vregs_placed_ok

structure StageP3CalleesM3Placed [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec
  alloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A)
  dealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)
  memcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec
  grow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A))
  setState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A))
  dropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511) (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A)))
  dropSs3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))
  logClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)
  panic : ext lsHandleErrorSym = some Rust.panicked
  chainClone : ChainClone3OkPlaced A ext
  senderChainClone : SenderChainClone3OkPlaced A ext

theorem StageP3CalleesM3Placed.of_cliExternsPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLogClosure : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3CalleesM3Placed E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  refine {
    shim := ls_hook_ok_ultra_of_mem hh.codecHooks.shim (by decide)
    alloc := ls_hook_ok_ultra_of_mem hh.codecHooks.alloc (by decide)
    dealloc := ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
    memcpy := ls_hook_ok_ultra_of_mem
      ((show CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
          CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec from rfl) ▸
        hh.codecHooks.memcpy) (by decide)
    grow := Matched.grow_one_spe_placed_ok_at hh.codecHooks.shim
      hh.codecHooks.alloc hh.codecHooks.realloc hh.codecHooks.panic_raw
    setState := Matched.set_session_state_placed_ok_at
      ((show CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
          CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec from rfl) ▸
        hh.codecHooks.memcpy) hh.codecHooks.dealloc
    dropSpe2 := drop_spe2_placed_ok_at hh.codecHooks.dealloc
    dropSs3 := cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
    logClosure := hLogClosure
    panic := hh.codecHooks.panic_raw
    chainClone := cliChainClone3_placed_ok mmpl gh W hh
    senderChainClone := cliSenderChainClone3_placed_ok mmpl gh W hh
  }

section StageP3ZeroCap

open ProofLib.ProgramReflection SepProp CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.CliHandshake.Placed CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private abbrev bind_sepWP_lscro_frame_zero := @bind_sepWP_lscro_frame_zero_placed
private abbrev call_lscl_nopanic_zero := @call_lscl_nopanic_prev1
private abbrev call_lscl_ro_nopanic_zero := @call_lscl_ro_nopanic_prev1
private abbrev intro_lsro_decryptionFailed_zero := @intro_lsro_decryptionFailed_zero_placed

private theorem call_lscl_oom_zero [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_oom : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩; rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ := subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at hoom_post; rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hpan_oom, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm, _, hpost, allowPanic_oom_of_prefix (F := F) (htr ▸ List.prefix_refl _)⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost; rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_tail_dup_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]; refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hstep1 := p3_err_tail_dup_a_placed_wp ext s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  refine bind_sepWP_lscro_frame_zero hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64) (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4) (by sep_focus)
        (P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_)))
  have hcommon := stageP3_err_tail_common_zero_placed_ok ext hDropSS3
    s0 s1 coroPtr outPtr 0x8000000000000017#64 prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro1 hpc1 hrun1 (by rw [hsp1_s]; exact hsp_align) (htr1_s.trans htr) hx0_1 hx19_1 hx22_1
    (by rw [hx25_1, hsp1_s]) (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ =>
    ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof, hvregs_f.trans hvregs_1⟩

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_dup_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
          speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H =>
    P3P4.SepWPp.weaken_frame
      (P₁ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
      (P₂ := ⌜∀ c : BitVec 64, words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
      (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  have hstep1 := p3_err_dup_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_zero hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  refine call_lscl_nopanic_zero (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro1 hDropSS3 hpc1 hrun1 (by simpa only [State.spAligned, hsp1_s] using hsp_align) hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s]) hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1_s, sepConj_assoc]; refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have htail := stageP3_err_tail_dup_zero_placed_ok ext hDropSS3
    s0 s2 coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro2 hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align) (htr2_1.trans (htr1_s.trans htr))
    (hx19_cs2.trans hx19_1) (by rw [hx24_cs2, hx24_1, hsp2_s]) (by rw [hx25_cs2, hx25_1, hsp2_s])
    (hx26_cs2.trans hx26_1) (hx28_cs2.trans hx28_1)
  rw [hsp2_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  dsimp only [recordResultAt, vecResultAt]
  exact ⟨entails_replace_sub (hreassemble outPtr) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_tail_nondup_dec_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511) (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A))))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (b_2c0 : BitVec 8) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = dpClosureEntryM3Placed + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       A.live errsPtr 192 8 ∗ speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]; refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p3_err_tail_nondup_a1_placed_wp ext s coroPtr errsPtr hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_frame_zero hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hstack_drop : stackAt s.sp dropSessionStructure2Stack = memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_zero (spec := dropSpeSpec A) (x := (⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost))
    (T := speAt A (utf8 "decrypt") errsPtr e ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro1 hDropSpe2 hpc1 hrun1 (by simpa only [State.spAligned, hsp1_s] using hsp_align) hx30_1
    (by dsimp only [dropSpeSpec]; rw [hsp1_s]) hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSpeSpec]; rw [hsp1_s, sepConj_assoc]; refine SepWPp.pure_elim fun htr2_1 => ?_
  have hjoin192 : memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢ memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hstack_alloc : stackAt s.sp dropSpeStack = memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine P3P4.SepWPp.weaken_frame hjoin192 (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_)
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hstep3 := p3_err_tail_nondup_a2_placed_wp ext hdealloc s2 coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align)
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1)
    (by rw [hx24_cs2, hx24_1, hx24, hsp2_s]) (by rw [hx25_cs2, hx25_1, hx25, hsp2_s])
    (hx28_cs2.trans (hx28_1.trans hx28))
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_zero hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _, hx30_3, hvregs_3⟩
  have hstack_restore : memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗
      stackAt s.sp allocHookStack ⊢ stackAt s.sp dropSessionStructure2Stack := by
    rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32) (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hstack_restore (by sep_focus)
    (P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
        (P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4) (by sep_focus)
          (P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_))))
  have hcommon := stageP3_err_tail_common_zero_placed_ok ext hDropSS3
    s0 s3 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hcro3 hpc3 hrun3 (by rw [hsp3_2]; exact hsp_align) (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 (by rw [hx25_3, hsp3_2]) (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26))) hx28_3 hx30_3
  rw [hsp3_2] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ =>
    ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_3, hvregs_cs2, hvregs_1]⟩

def stageP3ErrPreZeroPlaced [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_nondup_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPreZeroPlaced stageP3ErrPost_placed
  rw [recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23]
  refine intro_lsro_decryptionFailed_zero hcro ?_
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 => SepWPp.exists_elim fun u940 =>
    SepWPp.exists_elim fun u948 => SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp ext s coroPtr outPtr (speTag e) w0 w1 w2 w3 w4
    u930 u938 u940 u948 u950 u958 (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine bind_sepWP_lscro_frame_zero hcro hstep1 (by sep_focus) fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_zero (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack) hcro1 hC.logClosure hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]; refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hstep3 := p3_err_nondup_b_placed_wp ext s2 coroPtr hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align) (hx19_cs2.trans hx19_1)
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_zero hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_zero (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro3 htr3_0 hC.grow hpc3 hrun3 hsp3_al hx30_3
    (by rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_2, pure_true, emp_sepConj]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr4_3 => SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_2
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hstep5 := p3_err_nondup_c_placed_wp ext hC.shim s4 coroPtr errsPtr (speTag e) w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hpc4 hrun4 (by rw [hsp4_s]; exact hsp_align) (hx19_cs4.trans hx19_3) (hx21_cs4.trans hx21_3)
    (by rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4_s])
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_zero hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs : ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗ ((errsPtr + 0x10#64) ↦₆₄ w1) ∗
      ((errsPtr + 0x18#64) ↦₆₄ w2) ∗ ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus)
    (P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_))
  have halloc17 := p3_alloc_2eac_zero_placed_ok (A := A) ext hC.alloc hC.panic s0 s5 emp
    hcro5 hpc5 hrun5 (by rw [hsp5_4]; exact hsp_align) htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_4] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hstep7 := p3_err_nondup_d_placed_wp ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 (by rw [hsp6_5]; exact hsp_align) rfl (hx19_cs6.trans hx19_5)
  rw [hsp6_5] at hstep7
  refine bind_sepWP_lscro_frame_zero hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  refine SepWPp.drop_frame (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
    ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64)) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_))
  refine call_lscl_nopanic_zero (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro7 hC.dropSs3 hpc7 hrun7 (by simpa only [State.spAligned, hsp7_6] using hsp_align) hx30_7
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6]) hx0_7 (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6, sepConj_assoc]; refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_6
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have htail := stageP3_err_tail_nondup_dec_zero_placed_ok ext hC.dealloc hC.dropSpe2 hC.dropSs3
    s0 s8 coroPtr outPtr errsPtr prevStatesPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e b_2c0 recG recSt
    hcro8 hpc8 hrun8 (by rw [hsp8_s]; exact hsp_align) (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    (hx19_cs8.trans hx19_7) (by rw [hx24_cs8, hx24_7, hx24_cs6, hx24_5, hx24_cs4, hx24_3, hx24_cs2, hx24_1, hsp8_s])
    (by rw [hx25_cs8, hx25_7, hx25_cs6, hx25_5, hsp8_s])
    (hx26_cs8.trans (hx26_7.trans (hx26_cs6.trans (hx26_5.trans (hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans hx26_1)))))))
    (hx28_cs8.trans hx28_7)
  rw [hsp8_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  refine ⟨Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64
    (Entails.trans (entails_replace_sub hrec (by sep_focus) rfl)
      (entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)))))),
    hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPreZeroPlaced stageP3ErrPost_placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_zero_placed_ok ext hC.dropSs3
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine P3P4.SepWPp.ret_sepWPp_frame hdup (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof, hvregs_f⟩
  · exact stageP3_sub5_err_nondup_zero_placed_ok ext hC s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      hinit_ne e he_npan htag23 b_2c0 G₂ recG st₂ recSt hcro hpc hrun hsp_align htr hx19 hx24

set_option maxHeartbeats 1200000 in
private theorem stageP3_err_ver_tail_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s7 : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem)
    (hpc7 : s7.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr7 : s7.trace = s0.trace)
    (hx0_7 : s7.readReg64 .x0 = 17#64) (hx1_7 : s7.readReg64 .x1 = 1#64) (hx19_7 : s7.readReg64 .x19 = coroPtr)
    (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64) (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0) := by
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_33b0_zero_placed_ok ext halloc hpanic s0 s7 emp
    hcro7 hpc7 hrun7 (by rw [hs7_sp]; exact hsp_align) htr7 hx0_7 hx1_7
  rw [sepConj_emp, hs7_sp] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine P3P4.SepWPp.weaken_frame hP8 (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0))) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 => SepWPp.exists_elim fun u_df0 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 => SepWPp.exists_elim fun u_280 =>
    SepWPp.exists_elim fun u_288 => SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  refine intro_lsro_decryptionFailed_zero hcro8 ?_
  have hstep9 := p3_err_ver_e_placed_wp ext s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hdf_ne hpc8 hrun8 (by rw [hsp8_7]; exact hsp_align) rfl (hx19_cs8.trans hx19_7)
  rw [hsp8_7] at hstep9
  refine bind_sepWP_lscro_frame_zero hcro8 hstep9 (by sep_focus) fun s9 hpc9 hrun9 hcro9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine SepWPp.drop_frame (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
    ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64)) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_)
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_spe := stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_)
  refine call_lscl_ro_nopanic_zero (spec := dropSpe2VerSpec A) (x := (errsPtr, msgVer)) (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hcro9 (drop_spe2_ver_placed_ok_at (A := A)) hpc9 hrun9 (by simpa only [State.spAligned, hsp9_8] using hsp_align) hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_8]) hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 => ?_)
  dsimp only [dropSpe2VerSpec]; rw [hsp9_8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe.symm) (by sep_focus)
        (P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 => SepWPp.exists_elim fun u_250 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_8
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10, hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hstep11 := p3_err_ver_f_placed_wp ext hdealloc s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 (by rw [hsp10_s]; exact hsp_align)
    (hx19_cs10.trans hx19_9) (hx21_cs10.trans hx21_9) (hx22_cs10.trans hx22_9) (hx23_cs10.trans hx23_9)
    (by rw [hx24_cs10, hx24_9, hx24_cs8, hx24_7, hsp10_s]) (by rw [hx25_cs10, hx25_9, hx25_cs8, hx25_7, hsp10_s]) (hx28_cs10.trans hx28_9)
  rw [hsp10_s] at hstep11
  refine bind_sepWP_lscro_frame_zero hcro10 hstep11 (by sep_focus) fun s11 hpc11 hrun11 hcro11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11, hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  have hfold250 : ((s.sp + 0x250#64) ↦₆₄ ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32) ((17#64 : BitVec 64).extractLsb' 32 32)
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
    (P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus)
        (P3P4.SepWPp.weaken_frame
          (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4) (by sep_focus)
          (P3P4.SepWPp.weaken_frame hfold250 (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_)))))
  have hcommon := stageP3_err_tail_common_zero_placed_ok ext hDropSS3
    s0 s11 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr 17#64 (s8.readReg64 .x0) 17#64 w3' w4 b_2c0 recG st
    hcro11 hpc11 hrun11 (by rw [hsp11_10]; exact hsp_align) (htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7))))
    hx0_11 hx19_11 hx22_11 (by rw [hx25_11, hsp11_10])
    (hx26_11.trans (hx26_cs10.trans (hx26_9.trans (hx26_cs8.trans hx26_7)))) hx28_11 hx30_11
  rw [hsp11_10] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  refine ⟨Entails.trans (entails_replace_sub hrec (by sep_focus) rfl)
    (entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))),
    hspf, htrf, hcc, hcrof, by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3Placed A ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPost_placed; dsimp only [SessionState.recordError]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w)) (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_placed_wp ext s1 coroPtr u3e0 msgVer (u3e8_w.extractLsb' 0 32)
    hpc1 hrun1 (by rw [hs1_sp]; exact hsp_align) hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_lscro_frame_zero hcro1 hstep1 (by sep_focus) fun s2 hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, _, hx30_2, hvregs_2⟩
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_zero (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hcro2 hC.logClosure hpc2 hrun2 (by simpa only [State.spAligned, hsp2_1] using hsp_align) hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hcro3 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_1
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, _, hvregs_cs3⟩
  have hstep3 := p3_err_ver_b_placed_wp ext s3 coroPtr hpc3 hrun3 (by rw [hsp3_s]; exact hsp_align) (hx19_cs3.trans hx19_2)
  rw [hsp3_s] at hstep3
  refine bind_sepWP_lscro_frame_zero hcro3 hstep3 (by sep_focus) fun s4 hpc4 hrun4 hcro4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, _, hx30_4, hvregs_4⟩
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_oom_zero (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 htr4_0 hC.grow hpc4 hrun4 (by simpa only [State.spAligned, hsp4_3] using hsp_align) hx30_4
    (by rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_3, pure_true, emp_sepConj]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr5_4 => SepWPp.pure_elim fun _ =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32))) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 => SepWPp.exists_elim fun u_e3 =>
    SepWPp.exists_elim fun u_e2 => SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_3
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, _, hvregs_cs5⟩
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans (hx27_cs3.trans (hx27_2.trans hx27_1)))
  have hstep5 := p3_err_ver_c_placed_wp ext s5 coroPtr errsPtr 0x8000000000000006#64
    (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 (by rw [hsp5_s]; exact hsp_align) (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4)
    (by rw [hx24_cs5, hx24_4, hx24_cs3, hx24_2, hx24_1, hsp5_s])
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_lscro_frame_zero hcro5 hstep5 (by sep_focus) fun s6 hpc6 hrun6 hcro6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, _, hx30_6, hvregs_6⟩
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32)) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_)
  refine call_lscl_nopanic_zero (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro6 hC.dropSs3 hpc6 hrun6 (by simpa only [State.spAligned, hsp6_5] using hsp_align) hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5]) hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_5
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, _, hvregs_cs6b⟩
  have hstep7 := p3_err_ver_d_placed_wp ext hC.shim s6b coroPtr outPtr ctxPtr recG.localIk.cap
    0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt) hpc6b hrun6b
    (by rw [hsp6b_s]; exact hsp_align) (hx19_cs6b.trans hx19_6)
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_lscro_frame_zero hcro6b hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  have hfold3e0_48 : ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.sp + 0x3e8#64) ↦₆₄ (u3e8_w.extractLsb' 32 32 ++ msgVer)) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
      ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ⊢
      memRegion (s.sp + 0x3e0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using words6_entails_memRegion48 (s.sp + 0x3e0#64)
      0xffffffffffffffff#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus)
    (P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus)
      (P3P4.SepWPp.weaken_frame hfold3e0_48 (by sep_focus)
        (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp).symm) (by sep_focus) ?_)))
  have htail := stageP3_err_ver_tail_zero_placed_ok ext hC.alloc hC.dealloc hC.dropSs3 hC.panic s0 s s7 coroPtr outPtr errsPtr prevStatesPtr
    msgVer b_2c0 recG st hcro7 hpc7 hrun7 hsp7_6b hsp_align
    (htr7_6b.trans (htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0)))) hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ =>
    ⟨Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64
      (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))))), hspf, htrf, hcc, hcrof,
     by rw [hvregs_f, hvregs_7, hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]⟩

def stageP3DispatchPreZeroPlaced [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A (s.sp + 0x270#64) res ∗ sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

theorem postTryDecrypt_entails_s5Dispatch_zero_placed [LibsignalPlacement] {A : RustAlloc}
    (s0 s : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (coinsPost : SepProp) :
    (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A (s.sp + 0x270#64) res ∗ protocolAddressAt A rem remAddrPtr ∗
      protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗
      coinsPost ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
    (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) ⊢
    stageP3DispatchPreZeroPlaced A s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G' recG st₂ st ∗
    genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer rem loc msgG msg coinsPost := by
  unfold stageP3Sub5ExtraPre stageP3DispatchPreZeroPlaced genP3S5PostFrame_placed LsTokenInit LsTokenInitM3
  rw [GenP3.stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

theorem stageP3_clone_vregs_prefix_placed_steps [LibsignalPlacement]
    {A : RustAlloc} (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ext : String → Option (State → State))
    (hC : StageP3CalleesM3Placed A ext) (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (s0 s : State) (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (P_extra F_frame : SepProp) (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 → s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ P_extra ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
      (LsTokenInit ∗ genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := cloneGen_vregs_placed_ok ext hC.shim hC.alloc hC.memcpy hC.panic hcc hscc s0 s s.sp
    (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp := LsTokenInitM3 ∗ P_extra ∗ F_frame
  have hP : (LsTokenInit ∗ genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame) =
    genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    change (LsTokenInitM3 ∗ genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
        locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame) = _
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ := hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hcro1
      (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end StageP3ZeroCap

set_option maxHeartbeats 1200000 in
theorem stageP3PrevEmptyVRegs_placed_ok [LibsignalPlacement]
    (hCallees : ∀ {A : RustAlloc} (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A ext →
      subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
      StageP3CalleesM3Placed A ext) :
    StageP3PrevEmptyVRegsPlacedStmt := by
  intro A ext C ctl K hA hcc hscc hroot hDropSS3 s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest g recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hcro hpc hrun hsp_align hsp_root htr hvregs hOk hErr hVerNe
  have hC := hCallees ext hA hDropSS3
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr
      g b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5DispatchPrevEmpty_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prevEmpty_placed_ok ext hC.shim hC.alloc hC.dealloc hC.memcpy
        hC.grow hDropSS3 hC.logClosure hC.panic s0 s2 coroPtr outPtr initErrsPtr hinit_ne e he_npan
        b_2c0 g G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed at herr
      have herr_post : stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_ hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      change _ ⊢ stageP3DispatchOkMidPrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr
          ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      unfold stageP3DispatchOkMidPrevEmptyPlaced; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced Matched.stageP3Sub5ExtraPrePrevEmpty; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_prevEmpty_placed_ok ext hC.shim hC.alloc hC.dealloc hC.grow
      hDropSS3 hC.logClosure hC.panic s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer
      b_2c0 g G₁ recG st hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr (.invalidMessage .preKey .decryptionFailed) ∗
      genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
        rem loc msgG msg (coinsAtPlaced cur rest)
    unfold genP3S5PostFramePlaced; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3GenStepsVRegs_placed_ok [LibsignalPlacement]
    (hCallees : ∀ {A : RustAlloc} (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A ext → StageP3CalleesM3Placed A ext) :
    StageP3GenStepsVRegsPlacedStmt := by
  intro A ext C ctl K hA hcc hscc hroot s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hcro hpc hrun hsp_align hsp_root htr hvregs hOk hErr hVerNe
  have hC := hCallees ext hA
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr
      prevStatesPtr b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5Dispatch_zero_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPreZeroPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_zero_placed_ok ext hC s0 s2 coroPtr outPtr initErrsPtr
        prevStatesPtr hinit_ne e he_npan b_2c0 G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPreZeroPlaced at herr
      have herr_post : stageP3ErrPost_placed A s0 s2 coroPtr outPtr prevStatesPtr e =
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e := by
        unfold stageP3ErrPost_placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ =>
          hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan
            (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))) hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMid_placed; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPre; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_zero_placed_ok ext hC s0 s s1 coroPtr ctxPtr outPtr initErrsPtr
      prevStatesPtr hinit_ne msgVer b_2c0 G₁ recG st hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
      hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed LsTokenInit LsTokenInitM3; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

theorem stageP3Prev1VRegs_a0_placed_of_verNeAt [LibsignalPlacement]
    (hCallees : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) →
      StageP3CalleesM3Placed E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hVerNeAt : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) →
      Over.OverVerNe1e04CliAtPlacedBody E2E.HooksE.A0 Over.OverPrevEncOK
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3Prev1VRegsA0PlacedStmt := by
  intro mmpl gh W hh hcc hscc hroot hDropSS3; have hC := hCallees mmpl gh W hh hDropSS3
  exact Over.stageP3Gen_prev1_vregs_at_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
    W.C 0#64 W.Q.K hC.shim hC.alloc hC.dealloc
    hC.memcpy hC.grow hC.setState hDropSS3 hC.logClosure hC.panic hcc hscc hroot
    (hVerNeAt mmpl gh W hh hDropSS3)

private theorem logClosure_verNe_of_matched [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl Matched.pqxdhLogClosurePlacedSpec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl VerNe.pqxdhLogClosurePlacedSpec) := by
  refine subroutine_ok_outcome_intro fun x F s0 hpc hrun hm hsp hL => ?_
  have hm' : s0.mem ⊨ (withLsCodeLoaded lsmpl Matched.pqxdhLogClosurePlacedSpec).pre x s0 ∗ F := by
    dsimp only [withLsCodeLoaded, VerNe.pqxdhLogClosurePlacedSpec, Matched.pqxdhLogClosurePlacedSpec,
      VerNe.pqLogLevelCellPlaced, FromRecordCallees.lsLogOff] at hm ⊢
    simpa only [pure_true, emp_sepConj] using hm
  exact subroutine_ok_apply_outcome h x F hpc hrun hm' hsp hL

theorem cliVerNe1e04_a0_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLogClosure : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    Over.OverVerNe1e04CliAtPlacedBody E2E.HooksE.A0 Over.OverPrevEncOK
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hC := StageP3CalleesM3Placed.of_cliExternsPlaced mmpl gh W hh hLogClosure
  exact Over.overVerNe1e04CliAtPlacedBody_a0_of_hooks (fun _ ⟨s, h⟩ => ⟨s, h⟩)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) (logClosure_verNe_of_matched hC.logClosure) hC.grow hC.dropSs3
    hh.codecHooks.shim hh.codecHooks.alloc hh.codecHooks.realloc
    hh.codecHooks.dealloc hh.codecHooks.memcpy
    hh.codecHooks.panic_alloc hh.codecHooks.panic_raw

theorem stageP3_prev1_placed_ok [LibsignalPlacement]
    (hLogClosure : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3Prev1VRegsA0PlacedStmt :=
  stageP3Prev1VRegs_a0_placed_of_verNeAt
    (fun mmpl gh W hh _ => StageP3CalleesM3Placed.of_cliExternsPlaced mmpl gh W hh (hLogClosure mmpl gh W))
    (fun mmpl gh W hh _ => cliVerNe1e04_a0_placed_ok mmpl gh W hh (hLogClosure mmpl gh W))

/-! ## `LibsignalFullPlacement` / `LibsignalFrozen` Variants (Block `519` Discharged Internally) -/

structure StageP3CalleesM3BasePlaced [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec
  alloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A)
  dealloc : subroutine_ok (lsProg_518 ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)
  memcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec
  grow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A))
  setState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48) (withLsCodeLoaded lsmpl (setSessionStateSpec A))
  dropSpe2 : subroutine_ok (lsProg_518 ext) (lsmpl.base 511) (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A)))
  dropSs3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))
  panic : ext lsHandleErrorSym = some Rust.panicked
  chainClone : ChainClone3OkPlaced A ext
  senderChainClone : SenderChainClone3OkPlaced A ext

theorem StageP3CalleesM3BasePlaced.of_cliExternsPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3CalleesM3BasePlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  refine {
    shim := ls_hook_ok_ultra_of_mem hh.codecHooks.shim (by decide)
    alloc := ls_hook_ok_ultra_of_mem hh.codecHooks.alloc (by decide)
    dealloc := ls_hook_ok_ultra_of_mem hh.codecHooks.dealloc (by decide)
    memcpy := ls_hook_ok_ultra_of_mem
      ((show CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
          CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec from rfl) ▸
        hh.codecHooks.memcpy) (by decide)
    grow := Matched.grow_one_spe_placed_ok_at hh.codecHooks.shim
      hh.codecHooks.alloc hh.codecHooks.realloc hh.codecHooks.panic_raw
    setState := Matched.set_session_state_placed_ok_at
      ((show CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
          CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec from rfl) ▸
        hh.codecHooks.memcpy) hh.codecHooks.dealloc
    dropSpe2 := drop_spe2_placed_ok_at hh.codecHooks.dealloc
    dropSs3 := cliDropSessionStructure4_placed_ok_at mmpl gh W hh
      (callerProg := lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
    panic := hh.codecHooks.panic_raw
    chainClone := cliChainClone3_placed_ok mmpl gh W hh
    senderChainClone := cliSenderChainClone3_placed_ok mmpl gh W hh
  }

theorem stageP3PrevEmpty_m3_full_placed_inst [LibsignalFullPlacement] :
    Matched.StageP3PrevEmptyVRegsM3FullPlacedStmt :=
  Matched.stageP3Gen_prevEmpty_vregs_full_placed_ok_of_clone cloneGen_vregs_placed_ok

section StageP3ZeroCapFull

open ProofLib.ProgramReflection SepProp CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.CliHandshake.Placed CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private abbrev bind_sepWP_lscro_frame_zero_full := @bind_sepWP_lscro_frame_zero_placed
private abbrev call_lscl_nopanic_zero_full := @call_lscl_nopanic_prev1
private abbrev intro_lsro_decryptionFailed_zero_full := @intro_lsro_decryptionFailed_zero_placed

set_option maxHeartbeats 1200000 in
private theorem stageP3_sub5_err_nondup_zero_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := Matched.lscro_of_frozen hfr
  unfold stageP3ErrPreZeroPlaced stageP3ErrPost_placed
  rw [recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23]
  refine intro_lsro_decryptionFailed_zero_full hcro ?_
  have hdecomp : vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢; refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64, words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢ speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hreassemble => ?_)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 => SepWPp.exists_elim fun u940 =>
    SepWPp.exists_elim fun u948 => SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_placed_wp ext s coroPtr outPtr (speTag e) w0 w1 w2 w3 w4
    u930 u938 u940 u948 u950 u958 (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine Matched.bind_sepWP_lsfr_frame_ver hfr hstep1 (by sep_focus) fun s1 hpc1 hrun1 hfr1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _, hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine Matched.call_lsfr_nopanic_ver (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr1 (Matched.pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hfr2 => ?_)
  have hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem := Matched.lscro_of_frozen hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1_s, sepConj_assoc]; refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hstep3 := p3_err_nondup_b_placed_wp ext s2 coroPtr hpc2 hrun2 (by rw [hsp2_s]; exact hsp_align) (hx19_cs2.trans hx19_1)
  rw [hsp2_s] at hstep3
  refine bind_sepWP_lscro_frame_zero_full hcro2 hstep3 (by sep_focus) fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _, hx30_3, hvregs_3⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp_align
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine call_lscl_oom_zero (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro3 htr3_0 hC.grow hpc3 hrun3 hsp3_al hx30_3
    (by rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_2, pure_true, emp_sepConj]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr4_3 => SepWPp.pure_elim fun _ => ?_
  have hsplit192 : memRegion errsPtr 192 = memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144) (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_2
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hstep5 := p3_err_nondup_c_placed_wp ext hC.shim s4 coroPtr errsPtr (speTag e) w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hpc4 hrun4 (by rw [hsp4_s]; exact hsp_align) (hx19_cs4.trans hx19_3) (hx21_cs4.trans hx21_3)
    (by rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4_s])
  rw [hsp4_s] at hstep5
  refine bind_sepWP_lscro_frame_zero_full hcro4 hstep5 (by sep_focus) fun s5 hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _, hvregs_5⟩
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs : ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗ ((errsPtr + 0x10#64) ↦₆₄ w1) ∗
      ((errsPtr + 0x18#64) ↦₆₄ w2) ∗ ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hreassemble errsPtr
  have hstack_alloc := stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus)
    (P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_))
  have halloc17 := p3_alloc_2eac_zero_placed_ok (A := A) ext hC.alloc hC.panic s0 s5 emp
    hcro5 hpc5 hrun5 (by rw [hsp5_4]; exact hsp_align) htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_4] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hcro6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0))) (by sep_focus) ?_))
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 => SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hstep7 := p3_err_nondup_d_placed_wp ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64 df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hdf_ne hpc6 hrun6 (by rw [hsp6_5]; exact hsp_align) rfl (hx19_cs6.trans hx19_5)
  rw [hsp6_5] at hstep7
  refine bind_sepWP_lscro_frame_zero_full hcro6 hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7, hvregs_7⟩
  refine SepWPp.drop_frame (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
    ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64)) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0))) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_))
  refine call_lscl_nopanic_zero_full (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro7 hC.dropSs3 hpc7 hrun7 (by simpa only [State.spAligned, hsp7_6] using hsp_align) hx30_7
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6]) hx0_7 (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hcro8 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp7_6, sepConj_assoc]; refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_6
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have htail := stageP3_err_tail_nondup_dec_zero_placed_ok ext hC.dealloc hC.dropSpe2 hC.dropSs3
    s0 s8 coroPtr outPtr errsPtr prevStatesPtr 17#64 (s6.readReg64 .x0) 17#64 w3' w4 e b_2c0 recG recSt
    hcro8 hpc8 hrun8 (by rw [hsp8_s]; exact hsp_align) (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    (hx19_cs8.trans hx19_7) (by rw [hx24_cs8, hx24_7, hx24_cs6, hx24_5, hx24_cs4, hx24_3, hx24_cs2, hx24_1, hsp8_s])
    (by rw [hx25_cs8, hx25_7, hx25_cs6, hx25_5, hsp8_s])
    (hx26_cs8.trans (hx26_7.trans (hx26_cs6.trans (hx26_5.trans (hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans hx26_1)))))))
    (hx28_cs8.trans hx28_7)
  rw [hsp8_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  refine ⟨Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64
    (Entails.trans (entails_replace_sub hrec (by sep_focus) rfl)
      (entails_replace_sub (Entails.of_eq hstack_drop2.symm) (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)))))),
    hspf, htrf, hcc, hcrof,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3, hvregs_cs2, hvregs_1]⟩

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_zero_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64) (hinit_ne : initErrsPtr ≠ 0#64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP3ErrPreZeroPlaced A s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := Matched.lscro_of_frozen hfr
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPreZeroPlaced stageP3ErrPost_placed
    have hstack_drop2 : stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_zero_placed_ok ext hC.dropSs3
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
      hcro hpc hrun hsp_align htr hx19 hx24
    refine P3P4.SepWPp.ret_sepWPp_frame hdup (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ => ?_
    have herrs : ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hcrof, hvregs_f⟩
  · exact stageP3_sub5_err_nondup_zero_full_placed_ok ext hC s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      hinit_ne e he_npan htag23 b_2c0 G₂ recG st₂ recSt hfr hpc hrun hsp_align htr hx19 hx24

set_option maxHeartbeats 1200000 in
theorem stageP3_ver_ne_zero_full_placed_ok [LibsignalFullPlacement] {A : RustAlloc}
    (ext : String → Option (State → State)) (hC : StageP3CalleesM3BasePlaced A ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPost_placed; dsimp only [SessionState.recordError]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64))) (by sep_focus) ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w)) (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_placed_wp ext s1 coroPtr u3e0 msgVer (u3e8_w.extractLsb' 0 32)
    hpc1 hrun1 (by rw [hs1_sp]; exact hsp_align) hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine Matched.bind_sepWP_lsfr_frame_ver hfr1 hstep1 (by sep_focus) fun s2 hpc2 hrun2 hfr2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, _, hx30_2, hvregs_2⟩
  have hstack_log := stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine Matched.call_lsfr_nopanic_ver (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := FromRecordCallees.lsLogOff ∗ stackAt s.sp pqxdhClosureStack)
    hfr2 (Matched.pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc2 hrun2 (by simpa only [State.spAligned, hsp2_1] using hsp_align) hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, pure_true, emp_sepConj]) trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hfr3 => ?_)
  have hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := Matched.lscro_of_frozen hfr3
  dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_1
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, _, hvregs_cs3⟩
  have hstep3 := p3_err_ver_b_placed_wp ext s3 coroPtr hpc3 hrun3 (by rw [hsp3_s]; exact hsp_align) (hx19_cs3.trans hx19_2)
  rw [hsp3_s] at hstep3
  refine bind_sepWP_lscro_frame_zero_full hcro3 hstep3 (by sep_focus) fun s4 hpc4 hrun4 hcro4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, _, hx30_4, hvregs_4⟩
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_oom_zero (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8)))) (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 htr4_0 hC.grow hpc4 hrun4 (by simpa only [State.spAligned, hsp4_3] using hsp_align) hx30_4
    (by rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_3, pure_true, emp_sepConj]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus) (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => SepWPp.pure_elim fun htr5_4 => SepWPp.pure_elim fun _ =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32))) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 => SepWPp.exists_elim fun u_e3 =>
    SepWPp.exists_elim fun u_e2 => SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_3
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, _, hvregs_cs5⟩
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans (hx27_cs3.trans (hx27_2.trans hx27_1)))
  have hstep5 := p3_err_ver_c_placed_wp ext s5 coroPtr errsPtr 0x8000000000000006#64
    (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 (by rw [hsp5_s]; exact hsp_align) (hx19_cs5.trans hx19_4) (hx21_cs5.trans hx21_4)
    (by rw [hx24_cs5, hx24_4, hx24_cs3, hx24_2, hx24_1, hsp5_s])
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_lscro_frame_zero_full hcro5 hstep5 (by sep_focus) fun s6 hpc6 hrun6 hcro6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, _, hx30_6, hvregs_6⟩
  have hstack_drop2 := stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32)) (by sep_focus)
    (P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_)
  refine call_lscl_nopanic_zero_full (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hcro6 hC.dropSs3 hpc6 hrun6 (by simpa only [State.spAligned, hsp6_5] using hsp_align) hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5]) hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 =>
    P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus)
      (P3P4.SepWPp.weaken_frame (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧ SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_)
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_5
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, _, hvregs_cs6b⟩
  have hstep7 := p3_err_ver_d_placed_wp ext hC.shim s6b coroPtr outPtr ctxPtr recG.localIk.cap
    0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt) hpc6b hrun6b
    (by rw [hsp6b_s]; exact hsp_align) (hx19_cs6b.trans hx19_6)
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_lscro_frame_zero_full hcro6b hstep7 (by sep_focus) fun s7 hpc7 hrun7 hcro7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  have hpack_ss : ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢ sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  have hfold3e0_48 : ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.sp + 0x3e8#64) ↦₆₄ (u3e8_w.extractLsb' 32 32 ++ msgVer)) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
      ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ⊢
      memRegion (s.sp + 0x3e0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using words6_entails_memRegion48 (s.sp + 0x3e0#64)
      0xffffffffffffffff#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus)
    (P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus)
      (P3P4.SepWPp.weaken_frame hfold3e0_48 (by sep_focus)
        (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp).symm) (by sep_focus) ?_)))
  have htail := stageP3_err_ver_tail_zero_placed_ok ext hC.alloc hC.dealloc hC.dropSs3 hC.panic
    s0 s s7 coroPtr outPtr errsPtr prevStatesPtr
    msgVer b_2c0 recG st hcro7 hpc7 hrun7 hsp7_6b hsp_align
    (htr7_6b.trans (htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0)))) hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc, hcrof, hvregs_f⟩ =>
    ⟨Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64
      (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))))), hspf, htrf, hcc, hcrof,
     by rw [hvregs_f, hvregs_7, hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]⟩

theorem stageP3_clone_vregs_prefix_base_placed_steps [LibsignalPlacement]
    {A : RustAlloc} (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ext : String → Option (State → State))
    (hC : StageP3CalleesM3BasePlaced A ext) (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (s0 s : State) (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (P_extra F_frame : SepProp) (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 → s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢ genP3PostPlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ P_extra ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
      (LsTokenInit ∗ genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := cloneGen_vregs_placed_ok ext hC.shim hC.alloc hC.memcpy hC.panic hcc hscc s0 s s.sp
    (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp := LsTokenInitM3 ∗ P_extra ∗ F_frame
  have hP : (LsTokenInit ∗ genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame) =
    genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    change (LsTokenInitM3 ∗ genP3PrePlaced A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
        locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ P_extra ∗ F_frame) = _
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ := hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hcro1
      (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end StageP3ZeroCapFull

set_option maxHeartbeats 1200000 in
theorem stageP3PrevEmptyVRegs_of_base_full_placed_ok [LibsignalFullPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hC : StageP3CalleesM3BasePlaced A ext)
    (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (hroot : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))))
    (hDropSS3 : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))) :
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' → s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro s0 s coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer b_2c0 rest g recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hfr hpc hrun hsp_align hsp_root htr hvregs hOk hErr hVerNe
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := Matched.lscro_of_frozen hfr
  refine stageP3_clone_vregs_prefix_base_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem := libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr
      g b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem := libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5DispatchPrevEmpty_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prevEmpty_full_placed_ok ext hC.shim hC.alloc hC.dealloc hC.memcpy
        hC.grow hDropSS3 hC.panic s0 s2 coroPtr outPtr initErrsPtr hinit_ne e he_npan
        b_2c0 g G' recG (genP3S5Model C K rem loc msg rest st).2 st hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed at herr
      have herr_post : stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_ hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      change _ ⊢ stageP3DispatchOkMidPrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr
          ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      unfold stageP3DispatchOkMidPrevEmptyPlaced; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced Matched.stageP3Sub5ExtraPrePrevEmpty; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_prevEmpty_full_placed_ok ext hC.shim hC.alloc hC.dealloc hC.grow
      hDropSS3 hC.panic s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer
      b_2c0 g G₁ recG st hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr (.invalidMessage .preKey .decryptionFailed) ∗
      genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
        rem loc msgG msg (coinsAtPlaced cur rest)
    unfold genP3S5PostFramePlaced; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

theorem stageP3PrevEmptyVRegs_full_placed_ok [LibsignalFullPlacement]
    (hCallees : ∀ {A : RustAlloc} (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A ext →
      subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
      StageP3CalleesM3BasePlaced A ext) :
    StageP3PrevEmptyVRegsFrozenPlacedStmt :=
  fun ext C ctl K hA hcc hscc hroot hDropSS3 =>
    stageP3PrevEmptyVRegs_of_base_full_placed_ok ext C ctl K
      (hCallees ext hA hDropSS3) hcc hscc hroot hDropSS3

set_option maxHeartbeats 1200000 in
theorem stageP3GenStepsVRegs_of_base_full_placed_ok [LibsignalFullPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hC : StageP3CalleesM3BasePlaced A ext)
    (hcc : ChainClone3OkPlaced A ext) (hscc : SenderChainClone3OkPlaced A ext)
    (hroot : subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K)))) :
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' → s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest recG st rem loc msgG msg F_frame Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hfr hpc hrun hsp_align hsp_root htr hvregs hOk hErr hVerNe
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := Matched.lscro_of_frozen hfr
  refine stageP3_clone_vregs_prefix_base_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : LibsignalFrozen lsmpl s1.mem := libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr
      prevStatesPtr b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : LibsignalFrozen lsmpl s2.mem := libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5Dispatch_zero_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPreZeroPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_zero_full_placed_ok ext hC s0 s2 coroPtr outPtr initErrsPtr
        prevStatesPtr hinit_ne e he_npan b_2c0 G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPreZeroPlaced at herr
      have herr_post : stageP3ErrPost_placed A s0 s2 coroPtr outPtr prevStatesPtr e =
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e := by
        unfold stageP3ErrPost_placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ =>
          hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan
            (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))) hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMid_placed; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPre; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_zero_full_placed_ok ext hC s0 s s1 coroPtr ctxPtr outPtr initErrsPtr
      prevStatesPtr hinit_ne msgVer b_2c0 G₁ recG st hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
      hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed LsTokenInit LsTokenInitM3; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

theorem stageP3GenStepsVRegs_full_placed_ok [LibsignalFullPlacement]
    (hCallees : ∀ {A : RustAlloc} (ext : String → Option (State → State)),
      AllocContractsXCliPlaced A ext → StageP3CalleesM3BasePlaced A ext) :
    StageP3GenStepsVRegsFrozenPlacedStmt :=
  fun ext C ctl K hA hcc hscc hroot =>
    stageP3GenStepsVRegs_of_base_full_placed_ok ext C ctl K
      (hCallees ext hA) hcc hscc hroot

theorem stageP3Prev1VRegs_a0_full_placed_of_verNeAt [LibsignalFullPlacement]
    (hCallees : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) →
      StageP3CalleesM3BasePlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hVerNeAt : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) →
      Over.OverVerNe1e04CliAtFrozenPlacedBody E2E.HooksE.A0 Over.OverPrevEncOK
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3Prev1VRegsA0FrozenPlacedStmt := by
  intro mmpl gh W hh hcc hscc hroot hDropSS3; have hC := hCallees mmpl gh W hh hDropSS3
  exact Over.stageP3Gen_prev1_vregs_at_full_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))
    W.C 0#64 W.Q.K hC.shim hC.alloc hC.dealloc
    hC.memcpy hC.grow hC.setState hDropSS3 hC.panic hcc hscc hroot
    (hVerNeAt mmpl gh W hh hDropSS3)

theorem cliVerNe1e04_a0_full_placed_ok [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Over.OverVerNe1e04CliAtFrozenPlacedBody E2E.HooksE.A0 Over.OverPrevEncOK
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hC := StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hh
  exact Over.overVerNe1e04CliAtFrozenPlacedBody_a0_of_hooks (fun _ ⟨s, h⟩ => ⟨s, h⟩)
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) hC.grow hC.dropSs3
    hh.codecHooks.shim hh.codecHooks.alloc hh.codecHooks.realloc
    hh.codecHooks.dealloc hh.codecHooks.memcpy
    hh.codecHooks.panic_alloc hh.codecHooks.panic_raw

theorem stageP3_prev1_full_placed_ok [LibsignalFullPlacement] :
    StageP3Prev1VRegsA0FrozenPlacedStmt :=
  stageP3Prev1VRegs_a0_full_placed_of_verNeAt
    (fun mmpl gh W hh _ => StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hh)
    (fun mmpl gh W hh _ => cliVerNe1e04_a0_full_placed_ok mmpl gh W hh)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
