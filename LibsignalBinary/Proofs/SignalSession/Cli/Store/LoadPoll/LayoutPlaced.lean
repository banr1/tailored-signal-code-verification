/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Layout
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Helpers for `load_session::{closure#0}`

Provides relocatable call and spatial helpers for Block `569` (`lsProg_569 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

theorem lpoll_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := lsProg_569 H) hC

theorem lpoll_memcpy_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX) := by
  have h := session_memcpy_region_lscro_of_cli (callerProg := lsProg_569 H) hC (stk := extHookStack)
  exact subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [StoreKit.withLsCodeRoLoaded, withStack, sessionMemcpyRegionSpec,
        memcpyRegionSpec, session2MemcpySpecX] at hp ⊢
      simpa only [sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by
      dsimp only [StoreKit.withLsCodeRoLoaded, withStack, sessionMemcpyRegionSpec,
        memcpyRegionSpec, session2MemcpySpecX] at hq ⊢
      simpa only [sepConj_assoc] using hq)

theorem entails_withLsCodeRoLoaded_pre {α : Type} {pl : MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {P F : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s0.mem)
    (h : P ⊢ spec.pre x s0 ∗ F) :
    P ⊢ (StoreKit.withLsCodeRoLoaded pl spec).pre x s0 ∗ F := by
  refine Entails.trans h ?_
  dsimp only [StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm]
  exact Entails.pure_right hcrl (Entails.refl _)

/-- Call any `Spec` whose panic implies `allocFailedIn` and whose exit/OOM are `False`,
preserving `StoreKit.LibsignalCodeRoLoaded pl`. -/
theorem lpoll_call_panicking_placed_raw {α : Type} {prog : Program} {pl : MultiPlacement}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded pl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq hpre ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun hm_pre hsp_align hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R' hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic x s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan, hpan sm _ halloc0⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

theorem lpoll_call_addrText_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {addrStk : Nat} {callee ret_pc ret : BitVec 64}
    {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (addrTextSpecPlaced A addrStk) s0_files s0_trace))
    (xg : AddrTextGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.addr)
    (hlen : xg.g.name.bytes.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (protocolAddressAt A xg.g xg.addr ∗ memRegion xg.ret 24 ∗
      stackAt s.sp addrStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (addressText xg.g.val) ∗ protocolAddressAt A xg.g xg.addr ∗
          stackAt s.sp addrStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_placed_raw hcall xg F hpc hrun hsp_align hlr htr hcrl hpan
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFsInv]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfs ?_
    unfold addrTextSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlen⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, addrTextSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm hfsm htrm)

theorem lpoll_call_dirGet_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpecPlaced rd pathOk A getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_placed_raw hcall xg F hpc hrun hsp_align hlr htr hcrl hpan
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold dirGetSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hcrlm hgr)

theorem lpoll_call_deser_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (sessDeserializeSpecPlaced Scope A))
    (xg : E2E.Record.DeserializeGeneral.DeserializeGenGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord xg.r).length)
    (hx8 : s.readReg64 .x8 = xg.out)
    (hsc : Scope xg.r)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗ memRegion xg.out 368 ∗
      stackAt s.sp E2E.Record.recDeserializeStack) ∗ F)
    (hnext : ∀ (sm : State) (gE2E : E2E.Record.RecordGhost),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → E2E.Record.Serialization.CanonRecord gE2E xg.r →
      SepWPp prog ret sm
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_placed_raw hcall xg F hpc hrun hsp_align hlr htr hcrl hpan
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold sessDeserializeSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx8, hsc⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sessDeserializeSpecPlaced, StoreKit.withLsCodeRoLoaded,
      E2E.Record.Serialization.allocPanic, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [sessDeserializeSpecPlaced, StoreKit.withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun gE2E => SepWPp.pure_elim fun htrm => ?_
    refine sepWPp_conseq
      (P' := ⌜E2E.Record.Serialization.CanonRecord gE2E xg.r⌝ ∗
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    exact SepWPp.pure_elim fun hcan =>
      hnext sm gE2E hpcm hrunm hspm hcsm hcrlm htrm hcan

end Placed

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
