/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `Dir::put` Tail & Dual-`Vec` Drops for `KpkMarkPoll`

Proves the budget-threaded shared `Dir::put::<String>` tail (`+184`) and dual-`Vec` drop blocks
(`+108`, `+240`) on Block `578` (`lsProg_578 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost DirPutGhost KpkMarkPollGhost dirAt kpkMarkBoxAt kpkMarkOutAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (bind_sepWP_state_mark bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20 epilogueOut epiloguePre
   kpkMarkOutAt_ok_reassemble kpkMinStk kpkSubMax layoutOk_u8_of_ne_zero savedCalleeSlots
   sepWPp_conseq sepWPp_of_sepWP_fs_placed sepWPp_of_sepWP_lscro setWidth_32_setWidth_64
   spAligned_sub_f0 subStack_split vecU8Tail vecU8_free_ne vecU8_free_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
  (freeOnlyEvs_optDeallocBufEvents kpk_epilogue_330_placed)

private theorem bv_sub_add_lit_kpk (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit_kpk BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

/-- Events emitted when dropping `(bytesCap, nameCap)` in `kpk_drop_both_{6c,f0}_placed`. -/
abbrev kpkDropBothEvents (bytesCap nameCap : BitVec 64) : List AllocEvent :=
  optDeallocBufEvents bytesCap ++ optDeallocBufEvents nameCap

theorem freeOnlyEvs_kpkDropBothEvents (bytesCap nameCap : BitVec 64) :
    FreeOnlyEvs (kpkDropBothEvents bytesCap nameCap) :=
  (freeOnlyEvs_optDeallocBufEvents bytesCap).append (freeOnlyEvs_optDeallocBufEvents nameCap)

private theorem entails_withLsCodeRoLoaded_pre_kpk [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

private theorem kpk_call_dirPut_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {putStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutSpecPlaced A lim PutEnv putStk))
    (xg : DirPutGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hlr_ok : LsRetAddr624 ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PutEnv xg.dir xg.name xg.bytes))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ vecU8 A.repAlloc xg.nameV xg.name ∗
      vecU8 A.repAlloc xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → PutEnv xg.dir xg.name xg.bytes evs →
      SepWPp prog ret sm
        ((dirAt A.repAlloc xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hpre' : P ⊢ (dirPutSpecPlaced A lim PutEnv putStk).pre (xg, st) s ∗ F := by
    refine Entails.trans hpre ?_
    unfold dirPutSpecPlaced withLsCodeRoLoaded
    refine entails_withLsCodeRoLoaded_pre_kpk hcrl ?_
    simp only [sepConj_assoc]
    have hlr30 : LsRetAddr624 (s.readReg64 .x30) := by
      change LsRetAddr624 (s.readReg64 Reg.lr)
      rwa [hlr]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit, hlr30⟩ (Entails.refl _)
  refine sepWPp_of_sepWP_lscro hcrl (mid := ret_pc) ?_
  exact ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr
    (fun R hm => by
      have hm' : s.mem ⊨ ((dirPutSpecPlaced A lim PutEnv putStk).pre (xg, st) s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hpre') hm
      rwa [sepConj_assoc] at hm')
    (fun _ _ _ hp => by
      simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm fun hcrlm => by
        simp only [dirPutSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
        exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
          (hnext sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs))
    (fun _ _ _ ho => by
      simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)

/-- Shared `Ok(())` tail (`+184 .. +192` → `kpk_epilogue_330_placed`) used by both `one_time` nonempty
(`dirA = x.self`, `nameV = s0.sp - 0x80#64`, `bytesV = s0.sp - 0xb0#64`) and `last_resort` append
(`dirA = x.self + 0x28#64`, `nameV = s0.sp - 0xb0#64`, `bytesV = s0.sp - 0xc8#64`). -/
theorem kpk_put_and_epilogue_b8_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk : Nat}
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542) (dirPutSpecPlaced A lim PutEnv putStk))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (dirA nameV bytesV : BitVec 64)
    (dir : DirGhost) (name bytes : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hlen : dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PutEnv dir name bytes))
    (hpc : s.pc = (blkPl_578).base + 184#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = dirA)
    (hx1 : s.readReg64 .x1 = nameV)
    (hx2 : s.readReg64 .x2 = bytesV)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hfoc : P ⊢
      dirAt A.repAlloc dirA dir ∗
      vecU8 A.repAlloc nameV name ∗
      vecU8 A.repAlloc bytesV bytes ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (evs : List AllocEvent) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      PutEnv dir name bytes evs →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .ok ∗
        dirAt A.repAlloc dirA (dir.put name bytes) ∗
        memRegion nameV 24 ∗ memRegion bytesV 24 ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗ A.pool lim (M.stepEvents evs st) sf ∗ F) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hput_le : putStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hep := @kpk_epilogue_330_placed _ M A lim H
  dsimp only [lsProg_578] at hPut hep
  change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
  refine sepWPp_conseq hfoc ?_
  apply sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 542)
  wp_steps_sync_pool (lsmpl.base 542)
  apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
  intro hcrl_put
  apply bind_sepWPp_state_mark; intro st_put
  have hsp_put : st_put.sp = s0.sp - 0xf0#64 := by kpk_norm
  refine kpk_call_dirPut_placed hPut ⟨dirA, dir, nameV, name, bytesV, bytes⟩ st
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
      (kpkSubMax decStk getStk putStk - putStk) ∗ epiloguePre s0 x ∗ F)
    (ret_pc := (blkPl_578).base + 188#64)
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp_put)
    (by kpk_norm)
    (lsRetAddr624_blockPlacement_base_add 578 188#64 (by decide) (by decide))
    hcrl_put
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    hlen
    hfit
    (by
      rw [hsp_put, subStack_split s0.sp hput_le hhi]
      kpk_sep_norm
      sep_focus)
    fun sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs => ?_
  have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_put
  have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
  have hsm_19 : sm.readReg64 .x19 = x.fut := by
    rw [(cs_x19 hcsm)]; kpk_norm
  have hsm_20 : sm.readReg64 .x20 = x.out := by
    rw [(cs_x20 hcsm)]; kpk_norm
  have hsm_v : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    rw [(cs_vregs hcsm)]; kpk_norm
  have hsm_tr : sm.trace = s0.trace := by
    rw [htrm]; kpk_norm
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscro hcrlm (mid := (blkPl_578).base + 816#64)
  wp_steps_sync_pool ((blkPl_578).base + 816#64)
  apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
  intro _hcrl_330
  refine hep x (M.stepEvents evs st) s0 _ 0xFFFFFFFFFFFFFFFE#64
    (sm.readReg64 .x27) (sm.readReg64 .x25) (sm.readReg64 .x22)
    (sm.readReg64 .x28) (sm.readReg64 .x23) (sm.readReg64 .x26) _
    (dirAt A.repAlloc dirA (dir.put name bytes) ∗
      memRegion nameV 24 ∗ memRegion bytesV 24 ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ F)
    (by kpk_norm)
    (by kpk_norm)
    hsp_align
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by
      rw [hsp_put, subStack_split s0.sp hput_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf evs P_f (htr_f.trans ((by kpk_norm : _ = sm.trace).trans hsm_tr))
        hsp_f hcs_f hevs <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_ok_reassemble A.repAlloc x.out
                (sm.readReg64 .x27) (sm.readReg64 .x25) (sm.readReg64 .x22) (sm.readReg64 .x26)
                ((sm.readReg64 .x28).setWidth 8) ((sm.readReg64 .x23).setWidth 32)
                (((sm.readReg64 .x23) >>> 32).setWidth 16)
                (((sm.readReg64 .x23) >>> 48).setWidth 8)))
          sep_focus

/-- Dual-`Vec` drop block at `+108 .. +144` (`one_time` nonempty: drops `bytes` then `name`,
joining at `+148`). -/
theorem kpk_drop_both_6c_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (st : M.σ) (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {post : State → SepProp → Prop}
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 108#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A.repAlloc bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool lim st s ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (blkPl_578).base + 148#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP (lsProg_578 H) ret sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool lim (M.stepEvents (kpkDropBothEvents bytesCap nameCap) st) sm ∗ F)
        post) :
    SepWP (lsProg_578 H) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_578 H) hC
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  dsimp only [lsProg_578] at hk
  clear hC
  let st1 : M.σ := M.stepEvents (optDeallocBufEvents bytesCap) st
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) ret s P post
  refine SepWP.weaken_pre hfoc ?_
  have hsecond : ∀ (s1 : State) (Q1 : SepProp),
      s1.pc = (blkPl_578).base + 128#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = namePtr →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (Q1 ⊢
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        bytesAt false namePtr nameBs ∗
        vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim st1 s1 ∗ F) →
      SepWP ((blkPC_578).rebase (blkPl_578).base H) ret s1 Q1 post := by
    intro s1 Q1 hpc1 hrun1 hsp1 hcrl1 htr1 r19 r20 r23 r24 r26 r28 r29 hv1 hQ1
    have hsp_al1 : s1.spAligned = true := spAligned_sub_f0 hsp_align hsp1
    refine SepWP.weaken_pre hQ1 ?_
    by_cases hncap : nameCap = 0#64
    · subst hncap
      have hst2_eq : st1 = M.stepEvents (kpkDropBothEvents bytesCap 0#64) st := by
        simp only [st1, kpkDropBothEvents, optDeallocBufEvents, ↓reduceIte, List.append_nil]
      refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl1 (mid := (blkPl_578).base + 148#64)
      wp_steps_sync_pool ((blkPl_578).base + 148#64)
      apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl2
      refine SepWP.weaken_pre (by rw [hst2_eq]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hcrl2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
    · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
      have hlay_n : RustLayoutOk nameCap.toNat 1 := ⟨⟨hn_pos, hn_pow1, hn_hi⟩, by decide⟩
      have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
      have hst2_eq :
          M.stepEvents (rustDeallocEvents nameCap.toNat 1) st1 =
            M.stepEvents (kpkDropBothEvents bytesCap nameCap) st := by
        simp only [st1, kpkDropBothEvents, optDeallocBufEvents, hncap, ↓reduceIte,
          M.stepEvents_append]
      refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := namePtr) hncap hnlen hnlt)
        (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustDeallocSymCli)
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_da2
      apply sepWP_seq_lscro hcrl_da2 (mid := (blkPl_578).base + 148#64)
      rcases hcrl_da2 with ⟨hcl_da2, hro_da2⟩
      wp_call hdealloc (namePtr, nameCap.toNat, 1, st1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl2
      refine SepWP.weaken_pre (by rw [hsp1, hst2_eq]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hcrl2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    have hst1_eq : st = st1 := by
      simp only [st1, optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    refine SepWP.fold (vecU8_free_zero A.repAlloc bytesPtr hblen) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 128#64)
    wp_steps_sync_pool ((blkPl_578).base + 128#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by rw [← hst1_eq]; kpk_sep_focus)
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hlay_b : RustLayoutOk bytesCap.toNat 1 := ⟨⟨hb_pos, hb_pow1, hb_hi⟩, by decide⟩
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    have hst1_eq : M.stepEvents (rustDeallocEvents bytesCap.toNat 1) st = st1 := by
      simp only [st1, optDeallocBufEvents, hbcap, ↓reduceIte]
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := bytesPtr) hbcap hblen hblt)
      (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_da1
    apply sepWP_seq_lscro hcrl_da1 (mid := (blkPl_578).base + 128#64)
    rcases hcrl_da1 with ⟨hcl_da1, hro_da1⟩
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by rw [hsp, hst1_eq]; kpk_sep_focus)

private theorem kpk_drop_both_f0_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (st : M.σ) (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 240#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A.repAlloc bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool lim st s ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (blkPl_578).base + 280#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP (lsProg_578 H)
        ((blkPl_578).base + 280#64) sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool lim (M.stepEvents (kpkDropBothEvents bytesCap nameCap) st) sm ∗ F)
        post) :
    SepWP (lsProg_578 H) ((blkPl_578).base + 280#64) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_578 H) hC
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  dsimp only [lsProg_578] at hk
  clear hC
  let st1 : M.σ := M.stepEvents (optDeallocBufEvents bytesCap) st
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) ((blkPl_578).base + 280#64) s P post
  refine SepWP.weaken_pre hfoc ?_
  have hsecond : ∀ (s1 : State) (Q1 : SepProp),
      s1.pc = (blkPl_578).base + 260#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = namePtr →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (Q1 ⊢
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        bytesAt false namePtr nameBs ∗
        vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim st1 s1 ∗ F) →
      SepWP ((blkPC_578).rebase (blkPl_578).base H)
        ((blkPl_578).base + 280#64) s1 Q1 post := by
    intro s1 Q1 hpc1 hrun1 hsp1 hcrl1 htr1 r19 r20 r23 r24 r26 r28 r29 hv1 hQ1
    have hsp_al1 : s1.spAligned = true := spAligned_sub_f0 hsp_align hsp1
    refine SepWP.weaken_pre hQ1 ?_
    by_cases hncap : nameCap = 0#64
    · subst hncap
      have hst2_eq : st1 = M.stepEvents (kpkDropBothEvents bytesCap 0#64) st := by
        simp only [st1, kpkDropBothEvents, optDeallocBufEvents, ↓reduceIte, List.append_nil]
      refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl1 (mid := (blkPl_578).base + 280#64)
      wp_steps_sync_pool ((blkPl_578).base + 280#64)
      apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl2
      refine SepWP.weaken_pre (by rw [hst2_eq]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hcrl2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
    · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
      have hlay_n : RustLayoutOk nameCap.toNat 1 := ⟨⟨hn_pos, hn_pow1, hn_hi⟩, by decide⟩
      have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
      have hst2_eq :
          M.stepEvents (rustDeallocEvents nameCap.toNat 1) st1 =
            M.stepEvents (kpkDropBothEvents bytesCap nameCap) st := by
        simp only [st1, kpkDropBothEvents, optDeallocBufEvents, hncap, ↓reduceIte,
          M.stepEvents_append]
      refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := namePtr) hncap hnlen hnlt)
        (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustDeallocSymCli)
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_da2
      apply sepWP_seq_lscro hcrl_da2 (mid := (blkPl_578).base + 280#64)
      rcases hcrl_da2 with ⟨hcl_da2, hro_da2⟩
      wp_call hdealloc (namePtr, nameCap.toNat, 1, st1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl2
      refine SepWP.weaken_pre (by rw [hsp1, hst2_eq]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hcrl2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    have hst1_eq : st = st1 := by
      simp only [st1, optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    refine SepWP.fold (vecU8_free_zero A.repAlloc bytesPtr hblen) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 260#64)
    wp_steps_sync_pool ((blkPl_578).base + 260#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by rw [← hst1_eq]; kpk_sep_focus)
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hlay_b : RustLayoutOk bytesCap.toNat 1 := ⟨⟨hb_pos, hb_pow1, hb_hi⟩, by decide⟩
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    have hst1_eq : M.stepEvents (rustDeallocEvents bytesCap.toNat 1) st = st1 := by
      simp only [st1, optDeallocBufEvents, hbcap, ↓reduceIte]
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := bytesPtr) hbcap hblen hblt)
      (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_da1
    apply sepWP_seq_lscro hcrl_da1 (mid := (blkPl_578).base + 260#64)
    rcases hcrl_da1 with ⟨hcl_da1, hro_da1⟩
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by rw [hsp, hst1_eq]; kpk_sep_focus)

/-- Dual-`Vec` drop block at `+240 .. +276` (`one_time` empty: drops `bytes` then `name`,
preserving `FsInv` across `Steps` via `TraceFsSound`, joining at `+280`). -/
theorem kpk_drop_both_f0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (st : M.σ) (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent}
    (hFs : TraceFsSound (lsProg_578 H))
    (hfs_s : FsInv F0 T0 s)
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 240#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A.repAlloc bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool lim st s ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (blkPl_578).base + 280#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv F0 T0 sm →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (lsProg_578 H) ret sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool lim (M.stepEvents (kpkDropBothEvents bytesCap nameCap) st) sm ∗ F)
        Q Qp) :
    SepWPp (lsProg_578 H) ret s P Q Qp :=
  sepWPp_of_sepWP_fs_placed hFs hcrl hfs_s <|
    kpk_drop_both_f0_wp_placed hC st s0 s bytesCap bytesPtr bytesBs nameCap namePtr nameBs P F
      hblen hblt _hbptr hnlen hnlt _hnptr hpc hrun hsp_align hsp hfp hcrl hvregs
      hx27 hx25 hx24 hfoc fun sm hpcm hrunm hspm hcrlm htrm r19 r20 r23 r26 r28 r29 hvm =>
        SepWP.done hpcm hrunm fun _ hfs_sm =>
          hk sm hpcm hrunm hspm hcrlm hfs_sm htrm r19 r20 r23 r26 r28 r29 hvm

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudget
