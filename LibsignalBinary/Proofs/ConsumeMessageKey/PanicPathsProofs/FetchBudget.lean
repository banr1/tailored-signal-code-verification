/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Fetch
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Call Combinators for `consume_message_key` Panic Paths
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.FetchBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (PublicKey RatchetState ReceiverChain)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSessionRepr (RatchetGhost chainAt)
open CryptoVerification.LibsignalSession (ConsumeMessageKeyGhost)
open CryptoVerification.LibsignalSession.PanicPaths (introduce_withLsCodeLoaded)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents NullAllowed
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  cmkPlacedSpec cmkShimSpec findIndexPlacedSpec
)

theorem cmkPlacedSpec_onPanic_eq [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (s0 sf : State) :
    (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sf =
      (⌜(x.model F).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) :=
  rfl

theorem panic_cmk_placed {prog : Program} {ret panic_pc : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {x : ConsumeMessageKeyGhost}
    {s0 s : State} {P R_unused R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (hpan : (x.model F).1 = .error .panic)
    (htr : s0.trace <+: s.trace) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (R_unused ∗ R)) →
        (sf.mem ⊨ (⌜(x.model F).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun (hpc ▸ hext) fun hmf => ?_
  have htr' : s0.trace <+: (Rust.panicked s).trace := by simpa [Rust.panicked] using htr
  rw [← sepConj_assoc] at hmf
  exact allowPanic_panicked (And.intro hpan htr') hmf

theorem call_hmac_placed [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState}
    {ret entry : BitVec 64} (ret_pc out ka : BitVec 64) (key : List (BitVec 8))
    (ia : BitVec 64) (inp : List (BitVec 8)) (sp0 : BitVec 64)
    {s : State} {P Fr : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (hmacSpec F)))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = ka)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = ia)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hklen : key.length = 32) (hilen : inp.length = 1)
    (hframe : SepFrame (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      VmPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := stackAt_split_bottom sp0 2048 2048 (by decide)
  change stackAt sp0 4096 = memRegion (sp0 - 4096#64) 2048 ∗ stackAt sp0 2048 at h_stk
  refine SepWPp.seq_frozen (mid := ret_pc) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hcall (x := (out, ka, key, ia, inp))
    (F := memRegion (sp0 - 4096#64) 2048 ∗ Fr) hpc hrun hsp_align hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun hcl_sm R hpost => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · refine introduce_withLsCodeLoaded hcl ?_
    simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by simp [hx2, hklen], hx3, by simp [hx4, hilen], hklen, hilen⟩, ?_⟩
    have hm' := hm
    rw [hframe.eq, h_stk] at hm'
    exact Satisfies.of_eq hm'
  · have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
    rw [hsp] at hspm
    simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvmm, htrm, hpost⟩
    have hpost' : sm.mem ⊨
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) ∗ R := by
      rw [h_stk]
      exact Satisfies.of_eq hpost
    exact hnext sm hpcm hrunm hspm hsp_sm htrm hvmm hcl_sm hcsm R hpost'

theorem call_hmac_ro_placed [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState}
    {ret entry : BitVec 64} (ret_pc out ka : BitVec 64) (key : List (BitVec 8))
    (ia : BitVec 64) (inp : List (BitVec 8)) (sp0 : BitVec 64)
    {s : State} {P Fr : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = ka)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = ia)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hklen : key.length = 32) (hilen : inp.length = 1)
    (hframe : SepFrame (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      VmPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      LibsignalRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := stackAt_split_bottom sp0 2048 2048 (by decide)
  change stackAt sp0 4096 = memRegion (sp0 - 4096#64) 2048 ∗ stackAt sp0 2048 at h_stk
  refine SepWPp.seq_frozen (mid := ret_pc)
    (Φ := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, CryptoVerification.libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    ⟨hcl, hro⟩ ?_
  refine SepWP.call_subroutine_frame hcall (x := (out, ka, key, ia, inp))
    (F := memRegion (sp0 - 4096#64) 2048 ∗ Fr) hpc hrun hsp_align hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun ⟨hcl_sm, hro_sm⟩ R hpost => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · refine introduce_withLsCodeLoaded hcl ?_
    dsimp only
    rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalRoLoaded lsmpl s.mem⌝, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by simp [hx2, hklen], hx3, by simp [hx4, hilen], hklen, hilen⟩, ?_⟩
    have hm' := hm
    rw [hframe.eq, h_stk] at hm'
    exact Satisfies.of_eq hm'
  · have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
    rw [hsp] at hspm
    simp only [hmacSpec, withVmPreserved, CryptoVerification.LibsignalSession.hmacSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvmm, htrm, hpost⟩
    have hpost' : sm.mem ⊨
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) ∗ R := by
      rw [h_stk]
      exact Satisfies.of_eq hpost
    exact hnext sm hpcm hrunm hspm hsp_sm htrm hvmm hcl_sm hro_sm hcsm R hpost'

theorem call_findIndex_none_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {A : RustCliAllocBudget M}
    {ret entry : BitVec 64} (ret_pc p theirA sp0 : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (their : PublicKey)
    {s : State} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (findIndexPlacedSpec A)))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length)
    (hx2 : s.readReg64 .x2 = theirA)
    (hlen : Gc.chains.length = stc.receiverChains.length)
    (hxs_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63)
    (hnone : stc.findReceiverChainIndex their = none)
    (hframe : SepFrame
      (arrayAt (chainAt A.repAlloc) 104 p (Gc.chains.zip stc.receiverChains) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp0 4096) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      VmPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := stackAt_split_bottom sp0 1024 3072 (by decide)
  change stackAt sp0 4096 = memRegion (sp0 - 4096#64) 3072 ∗ stackAt sp0 1024 at h_stk
  have hx1' : (s.readReg64 .x1).toNat = (Gc.chains.zip stc.receiverChains).length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.seq_frozen (mid := ret_pc) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hcall (x := (p, Gc.chains.zip stc.receiverChains, theirA, their))
    (F := memRegion (sp0 - 4096#64) 3072 ∗ Fr) hpc hrun hsp_align hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by simp only [findIndexPlacedSpec, withVmPreserved, CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [findIndexPlacedSpec, withVmPreserved, CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun hcl_sm R hpost => ?_)
    (fun _ _ _ hpost => by simp only [findIndexPlacedSpec, withVmPreserved, CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · refine introduce_withLsCodeLoaded hcl ?_
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1', hx2, hxs_lt⟩, ?_⟩
    have hm' := hm
    rw [hframe.eq, h_stk] at hm'
    exact Satisfies.of_eq hm'
  · have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
    rw [hsp] at hspm
    have hmap : (Gc.chains.zip stc.receiverChains).map (·.2) = stc.receiverChains :=
      List.map_snd_zip (Nat.le_of_eq hlen.symm)
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec, hsp, hmap,
      show List.findIdx? (fun c : ReceiverChain => c.senderRatchetKey == their) stc.receiverChains =
        stc.findReceiverChainIndex their from rfl,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [hnone] at hpost
    rcases hpost with ⟨hvmm, ⟨htrm, hx0_sm⟩, hpost⟩
    have hpost' : sm.mem ⊨ P ∗ R := by
      rw [hframe.eq, h_stk]
      exact Satisfies.of_eq hpost
    exact hnext sm hpcm hrunm hspm hsp_sm htrm hvmm hcl_sm hcsm hx0_sm R hpost'

theorem call_shim_placed {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry : BitVec 64} (ret_pc sp0 : BitVec 64)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry cmkShimSpec)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      VmPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hcall (x := ()) (F := P) hpc hrun hsp_align hlr
    (fun R hm => by simpa [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec] using hm)
    (fun _ _ _ hpost => by simp only [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun hcl_sm R hpost => ?_)
    (fun _ _ _ hpost => by simp only [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
  rw [hsp] at hspm
  simp only [cmkShimSpec, withVmPreserved, CryptoVerification.LibsignalSession.cmkShimSpec,
    sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨hvmm, htrm, hpost⟩
  exact hnext sm hpcm hrunm hspm hsp_sm htrm hvmm hcl_sm hcsm R hpost

theorem call_alloc_32_placed [LibsignalPlacement] {M : AllocCostModel} {prog : Program} {pl : Obj.MultiPlacement}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ret entry : BitVec 64} (ret_pc sp0 : BitVec 64)
    {s : State} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false))
    (hfit : FitsEvents M lim st (rustAllocEvents 32 1))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 32#64)
    (hx1 : s.readReg64 .x1 = 1#64)
    (hframe : SepFrame (A.pool lim st s ∗ stackAt sp0 4096) P Fr)
    (hsucc : ∀ (sf : State) (a0 a1 a2 a3 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true →
      AllocCallPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      CalleeSavedPreserved s sf → (sf.readReg64 .x0 == 0#64) = false →
      SepWPp prog ret sf
        ((sf.readReg64 .x0 ↦₆₄ a0) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ a1) ∗
         ((sf.readReg64 .x0 + 16#64) ↦₆₄ a2) ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ a3) ∗
         A.live (sf.readReg64 .x0) 32 1 ∗
         A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) sf ∗
         stackAt sp0 4096 ∗ Fr) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog ret s P Q Qp := by
  have hlayout : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine SepWPp.seq_frozen (mid := ret_pc) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hcall (x := (32, 1, st)) (F := Fr) hpc hrun hsp_align hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by simp only [rustCliAllocBudgetSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [rustCliAllocBudgetSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun hcl_sm R hpost => ?_)
    (fun _ _ _ hoom => by
      dsimp only [rustCliAllocBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim (hoom.1.1 hfit))
  · simp only [rustCliAllocBudgetSpec, allocHookStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [hx0], by simp [hx1], hlayout, hlr.symm ▸ hlr_ls⟩, ?_⟩
    have hm' := hm
    rw [hframe.eq] at hm'
    exact Satisfies.of_eq hm'
  · have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
    rw [hsp] at hspm
    dsimp only [rustCliAllocBudgetSpec] at hpost
    simp only [Bool.false_eq_true, ↓reduceIte, allocHookStack, hsp] at hpost
    by_cases hx0_z : sm.readReg64 .x0 = 0
    · simp only [hx0_z, ↓reduceIte, sepConj_assoc] at hpost
      obtain ⟨_, hpost1⟩ := (satisfies_pure_sepConj _ _ _).1 hpost
      rw [sepConj_left_comm (stackAt _ _), sepConj_left_comm (A.pool _ _ _)] at hpost1
      have hna : NullAllowed 32 1 := ((satisfies_pure_sepConj _ _ _).1 hpost1).1
      unfold NullAllowed at hna
      omega
    · simp only [hx0_z, ↓reduceIte] at hpost
      have hc4 : memRegion (sm.readReg64 .x0) 32 =
          ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
            ((sm.readReg64 .x0) ↦₆₄ a0) ∗ ((sm.readReg64 .x0 + 8#64) ↦₆₄ a1) ∗
            ((sm.readReg64 .x0 + 16#64) ↦₆₄ a2) ∗ ((sm.readReg64 .x0 + 24#64) ↦₆₄ a3) := by
        have ha1 : sm.readReg64 .x0 + 8#64 + 8#64 = sm.readReg64 .x0 + 16#64 := by
          rw [BitVec.add_assoc]; rfl
        have ha2 : sm.readReg64 .x0 + 16#64 + 8#64 = sm.readReg64 .x0 + 24#64 := by
          rw [BitVec.add_assoc]; rfl
        rw [show (32 : Nat) = 8 * 4 from rfl, memRegion_cells _ 4 (by decide)]
        simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right, ha1, ha2]
      rw [hc4] at hpost
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      obtain ⟨a0, a1, a2, a3, hpost⟩ := hpost
      have hpost1 : sm.mem ⊨ ⌜AllocCallPreserved s sm⌝ ∗
          (⌜(sm.readReg64 .x0).toNat % 1 = 0⌝ ∗
            (((sm.readReg64 .x0 ↦₆₄ a0) ∗ ((sm.readReg64 .x0 + 8#64) ↦₆₄ a1) ∗
              ((sm.readReg64 .x0 + 16#64) ↦₆₄ a2) ∗ ((sm.readReg64 .x0 + 24#64) ↦₆₄ a3) ∗
              A.live (sm.readReg64 .x0) 32 1 ∗
              A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) sm ∗
              stackAt sp0 4096 ∗ Fr) ∗ R)) :=
        Satisfies.of_eq hpost
      obtain ⟨hacp, hpost2⟩ := (satisfies_pure_sepConj _ _ _).1 hpost1
      obtain ⟨_, hpost3⟩ := (satisfies_pure_sepConj _ _ _).1 hpost2
      have hx0_beq : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_z
      exact hsucc sm a0 a1 a2 a3 hpcm hrunm hspm hsp_sm hacp hcl_sm hcsm hx0_beq R hpost3

end LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.FetchBudget
