/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Helpers for `load_session::{closure#0}`

Defines `OptLoadDeserEnv` and `CliLoadPollEnv`, and provides `lpoll_call_total_placed_raw` on
Block `569` (`lsProg_569 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName sessionMemcpyRegionSpec withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.E2E.Record
  (RecordGhost encodeRecord recDeserializeStack sessionRecordAt)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.E2E.Record.DeserializeGeneral (DeserializeGenGhost)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (AddrTextGhost DirGetGhost DirGhost ReadRule SessLoadPollGhost addressText dirAt
   getResultAt pathOf withFsInv)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_569 blkPl_569 lsProg_569)
open CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
  (entails_withLsCodeRoLoaded_pre sepWPp_conseq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_base_add lsRetAddr624_base_zero
   lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced addrTextSpecPlaced dirGetSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (dealloc_lscro_of_cli session_memcpy_region_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)

section Placed

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem freeOnlyEvs_optDeallocBufEvents (cap : BitVec 64) :
    FreeOnlyEvs (optDeallocBufEvents cap) := by
  unfold optDeallocBufEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

/-- Optional `SessionRecord::deserialize` event envelope on `gr = x.dir.get rd F0 ...`. -/
def OptLoadDeserEnv (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (gr : Except Unit (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match gr with
  | .ok (b0 :: bsRest) =>
    ∃ r, encodeRecord r = b0 :: bsRest ∧ Scope r ∧ DeserEnv r evs
  | _ => evs = []

/-- Composed `AllocEvent` envelope for `load_session::{closure#0}`: `address_text` followed by
`Dir::get`, optional `SessionRecord::deserialize`, and `FreeOnlyEvs` buffer drops. -/
def CliLoadPollEnv (rd : ReadRule) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (F0 : FsFiles) (x : SessLoadPollGhost) : List AllocEvent → Prop :=
  SeqEnv (AddrEnv x.call.addr)
    (SeqEnv (GetEnv F0 x.dir (addressText x.call.addr.val))
      (SeqEnv (OptLoadDeserEnv Scope DeserEnv
        (x.dir.get rd F0 (addressText x.call.addr.val))) FreeOnlyEvs))

theorem lpoll_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := lsProg_569 H) hC

theorem lpoll_memcpy_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX) := by
  have h := session_memcpy_region_lscro_of_cli (callerProg := lsProg_569 H) hC (stk := extHookStack)
  refine subroutine_ok_mono h (fun _ _ _ hp => ?_) (fun x _ _ _ hq => ?_)
  · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · rcases x with ⟨dst, src, bs⟩
    dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, session2MemcpyBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

/-- Call any total `Spec` whose panic/exit/OOM are `False`, preserving `LibsignalCodeRoLoaded pl`
in a `SepWPp` continuation. -/
theorem lpoll_call_total_placed_raw {α : Type} {prog : Program} {pl : MultiPlacement}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onPanic x s sm ∗ R'))
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded pl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_seq_lscro (mid := ret_pc) hcrl ?_
  exact ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr
    (fun R hm => by
      have hm' : s.mem ⊨ (spec.pre x s ∗ F) ∗ R := Satisfies.mono (sepConj_mono_left hpre) hm
      rwa [sepConj_assoc] at hm')
    (fun R' sm _ hp => hpan_imp sm R' hp)
    (fun R' code sm _ he => hexit_imp code sm R' he)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm (fun hcrlm => hnext sm hpcm hrunm hspm hcsm hcrlm))
    (fun R' sm _ ho => (hoom_imp sm (F ∗ R') ho).elim)

theorem lpoll_call_addrText_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {addrStk : Nat} {callee ret_pc ret : BitVec 64}
    {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (addrTextSpecPlaced A lim AddrEnv addrStk) s0_files s0_trace))
    (xg : AddrTextGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.addr)
    (hlen : xg.g.name.bytes.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (AddrEnv xg.g))
    (hpre : P ⊢ (protocolAddressAt A.repAlloc xg.g xg.addr ∗ memRegion xg.ret 24 ∗
      stackAt s.sp addrStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace → AddrEnv xg.g evs →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.ret (addressText xg.g.val) ∗
          protocolAddressAt A.repAlloc xg.g xg.addr ∗
          stackAt s.sp addrStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | (apply lsRetAddr624_blockPlacement_base_add <;> decide)
      | (apply lsRetAddr624_base_add <;> decide)
      | (apply lsRetAddr624_blockPlacement_base_zero <;> decide)
      | (apply lsRetAddr624_base_zero <;> decide)
      | simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFsInv]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfs ?_
    unfold addrTextSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    have hlr30 : LsRetAddr624 (s.readReg64 .x30) := by
      change LsRetAddr624 (s.readReg64 Reg.lr)
      rwa [hlr]
    exact Entails.pure_right ⟨hx0, hx1, hlen, hfit, hlr30⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, addrTextSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfsm htrm hevs)

theorem lpoll_call_dirGet_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (xg : DirGetGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hfit : FitsEnv M lim st (GetEnv s.fs.files xg.dir xg.name))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace ∧
        GetEnv s.fs.files xg.dir xg.name evs) →
      SepWPp prog ret sm
        ((getResultAt A.repAlloc xg.ret gr ∗ dirAt A.repAlloc xg.self xg.dir ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold dirGetSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hcrlm hgr)

theorem lpoll_call_deser_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (xg : DeserializeGenGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord xg.r).length)
    (hx8 : s.readReg64 .x8 = xg.out)
    (hsc : Scope xg.r)
    (hfit : FitsEnv M lim st (DeserEnv xg.r))
    (hpre : P ⊢ ((xg.p ↦ₛ encodeRecord xg.r) ∗ memRegion xg.out 368 ∗
      A.pool lim st s ∗ stackAt s.sp recDeserializeStack) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gE2E : RecordGhost),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → DeserEnv xg.r evs → CanonRecord gE2E xg.r →
      SepWPp prog ret sm
        (((xg.p ↦ₛ encodeRecord xg.r) ∗
          sessionRecordAt A.repAlloc xg.out gE2E xg.r ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt s.sp recDeserializeStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold sessDeserializeSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx8, hsc, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [sessDeserializeSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gE2E =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    refine sepWPp_conseq
      (P' := ⌜CanonRecord gE2E xg.r⌝ ∗
        (((xg.p ↦ₛ encodeRecord xg.r) ∗
          sessionRecordAt A.repAlloc xg.out gE2E xg.r ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt s.sp recDeserializeStack) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    exact SepWPp.pure_elim fun hcan =>
      hnext sm evs gE2E hpcm hrunm hspm hcsm hcrlm htrm hevs hcan

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
