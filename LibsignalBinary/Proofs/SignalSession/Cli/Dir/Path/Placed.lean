/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `signal_session::stores::path` (Block `596`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Path.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification CryptoVerification.LibsignalPublicApi CryptoVerification.SignalSession

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Callee-Saved Invariant & Unified `memcpy` (`ro : Bool`) Contract -/

private def PathCalleeSavedP (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem PathCalleeSavedP.refl (s0 : State) : PathCalleeSavedP s0 s0 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem PathCalleeSavedP.trans {s0 s1 s2 : State}
    (h01 : PathCalleeSavedP s0 s1) (h12 : PathCalleeSavedP s1 s2) :
    PathCalleeSavedP s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.trans h01.2.2.2⟩

private theorem PathCalleeSavedP.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) : PathCalleeSavedP s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem memcpy_bytesAt_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtSpecX ro)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_596 H)
      (stk := extHookStack) hC
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      simp only [session2MemcpyBytesAtSpecX, withStack, sessionMemcpyRegionSpec,
        memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc,
        satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    rcases hmc (dst, src, bs) R s0 hpc hrun hpre' hal hL with ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [session2MemcpyBytesAtSpecX, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
        SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
      ls_hook_ok_ultra_of_mem hRO (by decide)
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨_hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨ sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
        (stackAt s0.sp extHookStack ∗ R) := by
      simp only [session2MemcpyBytesAtSpecX, sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    rcases hmc_ro (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal hL with
      ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [session2MemcpyBytesAtSpecX, sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

/-! ## 2. `SepWPp` Call & Panic Helpers -/

private abbrev pathOnPanicP [LibsignalPlacement] (A : RustAlloc) (stk : Nat)
    (x0 : PathGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pathSpecPlaced A stk).onPanic x0 s0 sf ∗ R)

private theorem step_shim_call_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat} {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (hshim : subroutine_ok (lsProg_596 H) call_pc
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = stackAt fsp extHookStack ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        (stackAt fsp extHookStack ∗ F) Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine SepWPp.call_lscro (x := ()) (F := F)
    hshim hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStack, sessionShimSpec, emp_sepConj, hsp]
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStack, sessionShimSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    simp only [withStack, sessionShimSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)
    exact Entails.of_eq (by ac_rfl)

private theorem step_handle_error_panic_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat} {call_pc ret : BitVec 64} {s0 s : State}
    (hpanic : (lsProg_596 H).externAt? call_pc = some Rust.panicked)
    {x0 : PathGhost} {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A stk x0 s0 R) := by
  have hext : (lsProg_596 H).externAt? s.pc = some Rust.panicked := by rwa [hpc]
  refine SepWPp.panic hrun hext fun hm => ?_
  simpa only [pathSpecPlaced, StoreKit.withLsCodeRoLoaded, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, htr])) hm

private theorem step_alloc_call_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk size : Nat} {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (halloc : subroutine_ok (lsProg_596 H) call_pc
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk size 1)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (A.pool ∗ stackAt fsp extHookStack) ∗ F)
    (hoom_next : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s0.trace ++ [allocFailedEvent] →
      CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        ((A.pool ∗ stackAt fsp extHookStack) ∗ F) Q (pathOnPanicP A stk x0 s0 R))
    (halloc_next : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        ((A.pool ∗ stackAt fsp extHookStack ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine SepWPp.call_lscro (x := (size, 1)) (F := F)
    halloc hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [rustAllocSpecWithStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlay⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [rustAllocSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    have hcs_s0 := hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)
    simp only [rustAllocSpecWithStack, hsp, BitVec.ofNat_eq_ofNat]
    by_cases hoom : sm.readReg64 .x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]
      have hpure_front :
          A.pool ∗ stackAt fsp extHookStack ∗ ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗ F =
          ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗ ((A.pool ∗ stackAt fsp extHookStack) ∗ F) := by
        ac_rfl
      rw [hpure_front]
      refine SepWPp.pure_elim fun htrm => ?_
      rw [htr] at htrm
      exact hoom_next sm hpcm hrunm hspm hoom htrm hcsm hcs_s0 hcrlm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hpure_front :
          A.pool ∗ stackAt fsp extHookStack ∗
            ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F =
          ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            ((A.pool ∗ stackAt fsp extHookStack ∗
              A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size) ∗ F) := by
        ac_rfl
      rw [hpure_front]
      refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
      exact halloc_next sm hpcm hrunm hspm hoom (htrm.trans htr) hcsm hcs_s0 hcrlm

private theorem step_memcpy_ro_call_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat} {ro : Bool} {call_pc dst src fsp ret_pc ret : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State}
    (hmc : subroutine_ok (lsProg_596 H) call_pc
      (StoreKit.withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtSpecX ro)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (memRegion dst bs.length ∗ SpqrV1.ChainProofs.bytesAt ro src bs ∗
      stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        (((dst ↦ₛ bs) ∗ SpqrV1.ChainProofs.bytesAt ro src bs ∗
          stackAt fsp extHookStack) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine SepWPp.call_lscro (x := (dst, src, bs)) (F := F)
    hmc hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [session2MemcpyBytesAtSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [session2MemcpyBytesAtSpecX, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    simp only [session2MemcpyBytesAtSpecX, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)
    exact Entails.of_eq (by ac_rfl)

private theorem step_cli_reserve_call_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {resStack stk additional : Nat}
    {call_pc v curCap curPtr fsp ret_pc ret : BitVec 64} {curBs : List (BitVec 8)}
    {s0 s : State}
    (hres : subroutine_ok (lsProg_596 H) call_pc
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt fsp resStack) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional))
          newPtr curBs ∗ A.pool ∗ stackAt fsp resStack) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine SepWPp.call_lscro (x := DoReserveCall.mk v curCap curPtr curBs additional) (F := F)
    hres hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [doReserveSpecOf, doReserveSpec, pathSpecPlaced, StoreKit.withLsCodeRoLoaded,
      allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    dsimp only [doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Symbolic-Execution Phases on Block `596` -/

private theorem step_to_owned_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret dirA nameA ret_lr : BitVec 64} {dir name : List (BitVec 8)} {dirRo : Bool}
    (hshim : subroutine_ok (lsProg_596 H) (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)))
    (halloc : subroutine_ok (lsProg_596 H) (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hmc_dir : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtSpecX dirRo)))
    (hpanic : (lsProg_596 H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hdir_lt : dir.length < 2 ^ 32)
    (hpc : s.pc = (blkPl_596).base + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = dirA)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptr0 : BitVec 64),
      ptr0 ≠ 0#64 →
      sm.pc = (blkPl_596).base + 120#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x21 = nameA →
      sm.readReg64 .x22 = BitVec.ofNat 64 dir.length →
      sm.readReg64 .x23 = ptr0 →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir ∗
          SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A stk x0 s0 R) := by
  subst hP
  rcases (show dir = [] ∨ 0 < dir.length by cases dir <;> simp) with rfl | hdir_pos
  · apply StoreKit.sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 120#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    refine SepWPp.weaken_pre ?_
      (hnext _ 1#64 (by decide)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
        hcrl1)
    simp only [vecU8RestAt, List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · have hdir_lt64 : dir.length < 2 ^ 64 := by omega
    have hdir_beq0 : (BitVec.ofNat 64 dir.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos hdir_lt64
    have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
    have hlay : LayoutOk dir.length 1 := ⟨hdir_pos, ⟨0, rfl⟩, by omega⟩
    rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    refine step_shim_call_p hshim hcrl1
      (fsp := fsp) (ret_pc := (blkPl_596).base + 84#64)
      (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal)
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      (by ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1 hcrl_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx24_1
    apply StoreKit.sepWPp_seq_lscro hcrl_s1 (mid := lsρ lsRustAllocSymCli)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl2
    refine step_alloc_call_p halloc hcrl2 (size := dir.length)
      (fsp := fsp) (ret_pc := (blkPl_596).base + 100#64)
      (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal)
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]; try rfl) hlay
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      (by ac_rfl) ?_ ?_
    · intro s2 hpc2 hrun2 hsp2 hoom2 htr2 _ _ _
      apply SepWPp.of_sepWP
        (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      exact step_handle_error_panic_p hpanic
        (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
    · intro s2 hpc2 hrun2 hsp2 hptr_ne0 htr2 hcs2 hcs_s2 hcrl_s2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, _⟩
      simp only [arm64_norm, wp_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx24_2
      have hptr_beq0 : (s2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hptr_ne0
      apply StoreKit.sepWPp_seq_lscro hcrl_s2 (mid := lsρ memcpyName)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl3
      refine step_memcpy_ro_call_p hmc_dir hcrl3
        (dst := s2.readReg64 Reg.x0) (src := dirA) (fsp := fsp)
        (ret_pc := (blkPl_596).base + 120#64) (bs := dir)
        (F := A.pool ∗ A.live (s2.readReg64 Reg.x0) dir.length 1 ∗
          memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
            (max resStack extHookStack - extHookStack) ∗ F)
        (by wp_norm_goal)
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by omega)
        (hcs_s2.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
        (by ac_rfl) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hcs3 hcs_s3 hcrl_s3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, _⟩
      simp only [arm64_norm, wp_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      have hcap0_ne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero hdir_pos hdir_lt64
      have hrest_eq :
          A.live (s2.readReg64 Reg.x0) dir.length 1 ∗ ((s2.readReg64 Reg.x0) ↦ₛ dir) =
            vecU8RestAt A (BitVec.ofNat 64 dir.length) (s2.readReg64 Reg.x0) dir := by
        simp only [vecU8RestAt, BitVec.ofNat_eq_ofNat, hcap0_ne, ite_false, hdir_toNat,
          Nat.sub_self, memRegion_zero, sepConj_emp]
      refine SepWPp.weaken_pre ?_
        (hnext s3 (s2.readReg64 Reg.x0) hptr_ne0
          hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs_s3 hcrl_s3)
      rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest_eq]
      exact Entails.of_eq (by ac_rfl)

private theorem step_push_slash_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA ptr0 v1 v2 v3 ret_lr : BitVec 64} {dir name : List (BitVec 8)}
    (hres : subroutine_ok (lsProg_596 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hdir_lt : dir.length < 2 ^ 32)
    (hptr0 : ptr0 ≠ 0#64)
    (hpc : s.pc = (blkPl_596).base + 120#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hx23 : s.readReg64 .x23 = ptr0)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      dir.length + 1 ≤ cap1.toNat →
      cap1.toNat < 2 ^ 34 →
      sm.pc = (blkPl_596).base + 180#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x9 = cap1 - BitVec.ofNat 64 (dir.length + 1) →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x21 = nameA →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A stk x0 s0 R) := by
  subst hP
  have hdir_lt64 : dir.length < 2 ^ 64 := by omega
  have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl1
  have hvec0 :
      ((fsp + 8#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        ((fsp + 16#64) ↦₆₄ ptr0) ∗
        ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir =
      vecU8At A (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir := by
    have h0 := vecU8At_of_header_rest A (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir
      (by omega) (by omega) hptr0
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h0
  have hbound1 : reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1 + 1 ≤ 2 ^ 63 := by
    simp only [reserveCap, hdir_toNat]; omega
  refine step_cli_reserve_call_p hres hcrl1 hbound1
    (v := fsp + 8#64) (curCap := BitVec.ofNat 64 dir.length) (curPtr := ptr0)
    (fsp := fsp) (ret_pc := (blkPl_596).base + 152#64) (curBs := dir) (additional := 1)
    (F := memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
      (max resStack extHookStack - resStack) ∗ F)
    (by wp_norm_goal)
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]; try rfl)
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
    (by rw [← hvec0]; ac_rfl) ?_
  intro s1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1 hcrl_s1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
  simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1
  set cap1 : BitVec 64 := BitVec.ofNat 64 (reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1)
  have hcap1_lt34 : cap1.toNat < 2 ^ 34 := by
    simp only [cap1, reserveCap, hdir_toNat, BitVec.toNat_ofNat]; omega
  have hcap1_ge : dir.length + 1 ≤ cap1.toNat := by
    have hlt64 : reserveCap dir.length dir.length 1 < 2 ^ 64 := by simp only [reserveCap]; omega
    simp only [cap1, hdir_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    simp only [reserveCap]; omega
  simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap1 ptr1 dir, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
  have hback1 :
      ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A cap1 ptr1 dir ∗ A.pool ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F =
      vecU8At A (fsp + 8#64) cap1 ptr1 dir ∗ A.pool ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F := by
    rw [← vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 dir hle_v1 hlt_v1 hptr1]
    ac_rfl
  rw [hback1,
    vecU8At_expose_slice A (fsp + 8#64) cap1 ptr1 dir 1 hcap1_ge (by omega) hptr1 (by decide),
    memRegion_1_eq_pointsTo8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => ?_
  apply StoreKit.sepWPp_seq_lscro hcrl_s1 (mid := (blkPl_596).base + 180#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl2
  have hadd1 : BitVec.ofNat 64 dir.length + 1#64 = BitVec.ofNat 64 (dir.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hpack1 := vecU8At_pack_slice A (fsp + 8#64) cap1 ptr1 dir [0x2f#8]
    (by simpa using hcap1_ge) (by omega) hptr1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_singleton] at hpack1
  refine SepWPp.weaken_pre ?_
    (hnext _ cap1 ptr1 hcap1_ge hcap1_lt34
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      hcrl2)
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt,
    pointsTo8_eq_singleton, ← hpack1]
  exact Entails.of_eq (by ac_rfl)

private theorem step_copy_name_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA cap2 ptr2 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hmc_name : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtSpecX nameRo)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hname_lt : name.length < 2 ^ 32)
    (hne : name ≠ [])
    (hle : (dir.length + 1) + name.length ≤ cap2.toNat)
    (hcap2 : cap2.toNat < 2 ^ 63)
    (hptr2 : ptr2 ≠ 0#64)
    (hpc : s.pc = (blkPl_596).base + 192#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (v_len : BitVec 64),
      sm.pc = (blkPl_596).base + 212#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A stk x0 s0 R) := by
  subst hP
  have hpos : 0 < name.length := List.length_pos_of_ne_nil hne
  have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  rw [vecU8At_expose_slice A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) name.length
      (by simpa [hlen1] using hle) hcap2 hptr2 hpos,
    stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1]
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsρ memcpyName)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl1
  refine step_memcpy_ro_call_p hmc_name hcrl1
    (dst := ptr2 + BitVec.ofNat 64 (dir.length + 1)) (src := nameA) (fsp := fsp)
    (ret_pc := (blkPl_596).base + 212#64) (bs := name)
    (F := ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗
      ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
      A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
      memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
        (cap2.toNat - (dir.length + 1) - name.length) ∗
      memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
        (max resStack extHookStack - extHookStack) ∗ F)
    (by wp_norm_goal)
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by omega)
    (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
    (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hcsm hcs_s0 hcrlm
  rcases hcsm with ⟨hx19m, hx20m, _, hx22m, _⟩
  simp only [arm64_norm, wp_norm, *] at hx19m hx20m hx22m
  have hcap2_ne : cap2 ≠ 0 := by
    intro h0; subst h0; simp at hle
  have htot_len : (dir ++ [0x2f#8] ++ name).length = dir.length + 1 + name.length := by
    simp; omega
  have htot_bv :
      ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
        ptr2 + BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
    rw [htot_len, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrest2 :
      A.live ptr2 cap2.toNat 1 ∗
        ((ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗ ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name)) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) =
      vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
    have happ := pointsToBytes_append ptr2 (dir ++ [0x2f#8]) name
    rw [hlen1] at happ
    rw [← happ, htot_bv]
    simp only [vecU8RestAt, hcap2_ne, ite_false, htot_len, Nat.sub_sub]
  refine SepWPp.weaken_pre ?_
    (hnext sm (BitVec.ofNat 64 (dir.length + 1))
      hpcm hrunm hspm htrm hx19m hx20m hx22m hcs_s0 hcrlm)
  rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest2]
  exact Entails.of_eq (by ac_rfl)

private theorem step_append_name_p [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA cap1 ptr1 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hres : subroutine_ok (lsProg_596 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hmc_name : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtSpecX nameRo)))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hname_lt : name.length < 2 ^ 32)
    (hcap1_ge : dir.length + 1 ≤ cap1.toNat)
    (hcap1_lt : cap1.toNat < 2 ^ 34)
    (hpc : s.pc = (blkPl_596).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx9 : s.readReg64 .x9 = cap1 - BitVec.ofNat 64 (dir.length + 1))
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 v_len : BitVec 64),
      (dir ++ [0x2f#8] ++ name).length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 →
      ptr2 ≠ 0#64 →
      sm.pc = (blkPl_596).base + 212#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A stk x0 s0 R) := by
  subst hP
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  have hult_iff := elem_len_ult_spare_iff (cap := cap1) (bsLen := dir.length + 1)
    (elemLen := name.length) hcap1_ge (by omega) (by omega)
  by_cases hgrow : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = true
  · have hlt_cap : cap1.toNat < (dir.length + 1) + name.length := hult_iff.mp hgrow
    have hname_pos : 0 < name.length := by omega
    have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
    have hlen1_toNat : (BitVec.ofNat 64 (dir.length + 1)).toNat = dir.length + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    have hbound2 : reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length + 1 ≤ 2 ^ 63 := by
      simp only [reserveCap, hlen1]; omega
    refine step_cli_reserve_call_p hres hcrl1 hbound2
      (v := fsp + 8#64) (curCap := cap1) (curPtr := ptr1)
      (fsp := fsp) (ret_pc := (blkPl_596).base + 284#64)
      (curBs := dir ++ [0x2f#8]) (additional := name.length)
      (F := SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F)
      (by wp_norm_goal)
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      (by ac_rfl) ?_
    intro s1 ptr2 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1 hcrl_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length)
    have hcap2_lt : cap2.toNat < 2 ^ 63 := by
      simp only [cap2, reserveCap, hlen1, BitVec.toNat_ofNat]; omega
    have hcap2_ge : (dir.length + 1) + name.length ≤ cap2.toNat := by
      have hlt64 : reserveCap cap1.toNat (dir.length + 1) name.length < 2 ^ 64 := by
        simp only [reserveCap]; omega
      simp only [cap2, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      simp only [reserveCap]; omega
    simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]),
      BitVec.add_assoc, BitVec.reduceAdd, hlen1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v2, hlt_v2, hptr2⟩ => ?_
    apply StoreKit.sepWPp_seq_lscro hcrl_s1 (mid := (blkPl_596).base + 192#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl2
    refine step_copy_name_p (ret := ret) (nameA := nameA) hmc_name hcrl2 hsub_lt hname_lt hne
      hcap2_ge hcap2_lt hptr2 (F := A.pool ∗ F)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      (by
        rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
        have hhdr := vecU8At_of_header_rest A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8])
          (by omega) hlt_v2 hptr2
        simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr
        rw [← hhdr]
        ac_rfl) ?_
    intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm cap2 ptr2 v_len (by simp; omega) hcap2_lt hptr2
        hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm)
  · have hgrow_f : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = false :=
      Bool.eq_false_iff.mpr hgrow
    have hfit : (dir.length + 1) + name.length ≤ cap1.toNat := by
      have := mt hult_iff.mpr hgrow; omega
    simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]), sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
    have hrepack1 :
        ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
          (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ [0x2f#8]).length) ∗
          vecU8RestAt A cap1 ptr1 (dir ++ [0x2f#8]) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack) ∗ F =
        (vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F := by
      rw [← vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1]
      ac_rfl
    rw [hrepack1]
    rcases (show name = [] ∨ 0 < name.length by cases name <;> simp) with rfl | hname_pos
    · apply StoreKit.sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 212#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl1
      refine SepWPp.weaken_pre ?_
        (hnext _ cap1 ptr1 (BitVec.ofNat 64 (dir.length + 1))
          (by simpa using hfit) (by omega) hptr1
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
          hcrl1)
      have hhdr1 := vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1
      simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr1
      rw [← hhdr1, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    · have hname_beq0 : (BitVec.ofNat 64 name.length == 0#64) = false :=
        ofNat_beq_zero_false hname_pos (by omega)
      have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 192#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl1
      refine step_copy_name_p (ret := ret) (nameA := nameA) hmc_name hcrl1 hsub_lt hname_lt hne
        hfit (by omega) hptr1 (F := A.pool ∗ F)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]) hfsp_align
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
        (by ac_rfl) ?_
      intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sm cap1 ptr1 v_len (by simp; omega) (by omega) hptr1
          hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm)

/-! ## 4. Top-Level Relocatable Theorems -/

/-- Core `[LibsignalPlacement]` theorem proving `pathSpecPlaced A stk` on Block `596`. -/
theorem path_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resProg : Program} {resBlk : Nat} [IsLsBlockProg resProg resBlk H]
    {resStack stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_596 H) (lsmpl.base 596) (pathSpecPlaced A stk) := by
  have hres596 : subroutine_ok (lsProg_596 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)) :=
    ls_transfer_lscro (callerProg := lsProg_596 H) hRes (by decide) hresBlk hresUnmut
  have hshim : subroutine_ok (lsProg_596 H) (lsρ lsRustNoAllocShimSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)) :=
    shim_lscro_of_cli (callerProg := lsProg_596 H) (stk := extHookStack) hC
  have halloc : subroutine_ok (lsProg_596 H) (lsρ lsRustAllocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    alloc_lscro_of_cli (callerProg := lsProg_596 H) hC
  have hpanic : (lsProg_596 H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked :=
    ls_panicAt_of_cliPanic hpan
  change subroutine_ok (lsProg_596 H) (blkPl_596).base (pathSpecPlaced A stk)
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  rcases x with ⟨dirA, dir, dirRo, nameA, name, nameRo, ret⟩
  have hmc_dir := memcpy_bytesAt_placed_ok hC hRO dirRo
  have hmc_name := memcpy_bytesAt_placed_ok hC hRO nameRo
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = ret ∧ s0.readReg64 .x1 = dirA ∧
      (s0.readReg64 .x2).toNat = dir.length ∧ s0.readReg64 .x3 = nameA ∧
      (s0.readReg64 .x4).toNat = name.length ∧
      dir.length < 2 ^ 32 ∧ name.length < 2 ^ 32⌝ ∗
      SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
      stackAt s0.sp stk ∗ A.pool) ∗ R at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hdir_lt, hname_lt⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 dir.length := bv_eq_ofNat_of_toNat hx2_nat
  have hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 name.length := bv_eq_ofNat_of_toNat hx4_nat
  have hmem_stk : s0.mem ⊨ memRegion ret 24 ∗ stackAt s0.sp stk ∗
      (SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗ R) := by
    convert hmem using 1; ac_rfl
  have hstk_lt : stk < 2 ^ 64 := stk_lt_two_pow_64 hmem_stk
  have hsub_lt : max resStack extHookStack ≤ 2 ^ 64 := by omega
  have halign64 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using halign
  refine ⟨SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
    SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
    stackAt s0.sp stk ∗ A.pool, R, hmem, ?_⟩
  have hbit63 : (BitVec.ofNat 64 dir.length).getLsbD 63 = false := ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 dir.length)[63] = false := ofNat_getElem_63_false (by omega)
  rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega)]
  generalize hfsp : s0.sp - 112#64 = fsp
  have hfsp_align : fsp &&& 15#64 = 0#64 := by rw [← hfsp]; exact sp_sub_112_aligned halign64
  rw [memRegion_24_cells ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r0 => ?_
  refine SepWPp.exists_elim fun r1 => ?_
  refine SepWPp.exists_elim fun r2 => ?_
  rw [cells_14_eq fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => ?_
  refine SepWPp.exists_elim fun v1 => ?_
  refine SepWPp.exists_elim fun v2 => ?_
  refine SepWPp.exists_elim fun v3 => ?_
  refine SepWPp.exists_elim fun v4 => ?_
  refine SepWPp.exists_elim fun v5 => ?_
  refine SepWPp.exists_elim fun v6 => ?_
  refine SepWPp.exists_elim fun v7 => ?_
  refine SepWPp.exists_elim fun v8 => ?_
  refine SepWPp.exists_elim fun v9 => ?_
  refine SepWPp.exists_elim fun v10 => ?_
  refine SepWPp.exists_elim fun v11 => ?_
  refine SepWPp.exists_elim fun v12 => ?_
  refine SepWPp.exists_elim fun v13 => ?_
  apply StoreKit.sepWPp_seq_lscro hcrl0 (mid := (blkPl_596).base + 4#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_sp
  apply StoreKit.sepWPp_seq_lscro hcrl_sp (mid := (blkPl_596).base + 64#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_pro
  set savedFrame : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
    (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
    (fsp ↦₆₄ v0) ∗
    ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
    ((fsp + 56#64) ↦₆₄ v7) ∗
    ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
  clear_value savedFrame
  refine step_to_owned_p (ret := ret) (dirA := dirA) (nameA := nameA) (name := name)
    hshim halloc hmc_dir hpanic hcrl_pro hsub_lt hdir_lt
    (F := ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ savedFrame)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) hfsp_align
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])
    (by rw [hsaved_def]; ac_rfl) ?_
  intro s1 ptr0 hptr0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hcrl1
  refine step_push_slash_p hres596 hcrl1 hsub_lt hdir_lt hptr0
    (v1 := v1) (v2 := v2) (v3 := v3)
    (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ savedFrame)
    hpc1 hrun1 hsp1 hfsp_align htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    (by ac_rfl) ?_
  intro s2 cap1 ptr1 hcap1_ge hcap1_lt hpc2 hrun2 hsp2 htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hcrl2
  refine step_append_name_p hres596 hmc_name hcrl2 hsub_lt hname_lt hcap1_ge hcap1_lt
    (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ savedFrame)
    hpc2 hrun2 hsp2 hfsp_align htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
    (by ac_rfl) ?_
  intro s3 cap2 ptr2 v_len hcap2_ge hcap2_lt hptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hcs3 _hcrl3
  rcases hcs3 with ⟨hx26_3, hx27_3, hx28_3, hvregs_3⟩
  rw [hsaved_def]
  have hq_pre :
      (((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
        vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
        stackAt fsp (max resStack extHookStack)) ∗
        SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
          (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
          (fsp ↦₆₄ v0) ∗
          ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((fsp + 56#64) ↦₆₄ v7) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
      (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
        vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
        SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
        stackAt fsp (max resStack extHookStack) ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗
        ((fsp + 24#64) ↦₆₄ v_len) ∗
        ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        A.pool := by
    ac_rfl
  have hs3_spAligned : s3.spAligned = true := by simp [State.spAligned, hsp3, hfsp_align]
  rw [hq_pre]
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  apply SepWPp.done
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  refine ⟨?_, ?_, by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, *]⟩
  · intro hPR
    have htot_bv :
        BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
          BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
      simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add]
    have hvec_out :
        (ret ↦₆₄ cap2) ∗ ((ret + 8#64) ↦₆₄ ptr2) ∗
          ((ret + 16#64) ↦₆₄ (BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) =
        vecU8At A ret cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
      rw [htot_bv]
      exact vecU8At_of_header_rest A ret cap2 ptr2 (dir ++ [0x2f#8] ++ name) hcap2_ge hcap2_lt hptr2
    change _ ⊨ (⌜_ = s0.trace⌝ ∗ vecU8 A ret (dir ++ [0x2f#8] ++ name) ∗
      SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ stackAt s0.sp stk ∗ A.pool) ∗ R
    simp only [vecU8, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨cap2, ptr2, by simp only [arm64_norm, wp_norm, *], ?_⟩
    rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega),
      hfsp, cells_14_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc]
    refine ⟨v0, cap2, ptr2,
      BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 25#5), v7,
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    rw [← hvec_out]
    simp only [sepConj_assoc] at hPR ⊢
    exact hPR
  · simp only [arm64_norm, wp_norm, ← hfsp, fsp_add_112_eq]

/-- Caller-transferable `[LibsignalPlacement]` `path` contract for any block `< 619`. -/
theorem path_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg resProg : Program} {i resBlk : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg resProg resBlk H]
    {resStack stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (hi : i < 619 := by decide)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 596) (pathSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 596)
    (path_placed_ok_of_deps hC hpan hRO hRes hstk hresBlk hresUnmut) hi

end CryptoVerification.SignalSession.Cli.Path.Helpers
