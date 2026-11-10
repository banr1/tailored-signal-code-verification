/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `[LibsignalPlacement]` `<signal_session::stores::Dir>::put::<alloc::string::String>` (Block `542`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.Put.Helpers

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

/-- Untouched callee-saved state across `Dir::put::<String>` (`x28`, `v8..v15`, and `StepInvPlaced`). -/
def PutCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem PutCalleeSavedPlaced.refl (s0 : State) : PutCalleeSavedPlaced s0 s0 :=
  ⟨rfl, rfl, StepInvPlaced.refl s0⟩

theorem PutCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h01 : PutCalleeSavedPlaced s0 s1) (h12 : PutCalleeSavedPlaced s1 s2) :
    PutCalleeSavedPlaced s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h01.2.2.trans h12.2.2⟩

theorem PutCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) :
    PutCalleeSavedPlaced s1 s2 := by
  rcases hcs with ⟨_, _, _, _, _, _, _, _, _, hx28, _, hv⟩
  exact ⟨hx28, hv, hinv⟩

theorem PutCalleeSavedPlaced.step {s0 s1 s2 : State}
    (h01 : PutCalleeSavedPlaced s0 s1)
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInvPlaced s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    PutCalleeSavedPlaced s0 s2 :=
  h01.trans ⟨hx28, hvregs, hinv⟩

def withPutCSPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜PutCalleeSavedPlaced s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withPutCSPlaced {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPutCSPlaced s0 spec) := by
  intro x R s hpc hrun hpre hsp hL
  rw [withPutCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s hpc hrun hpre.2 hsp hL

theorem subroutine_ok_withPutCSPlaced_lscro [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (h : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withPutCSPlaced s0 spec) := by
  intro x R s hpc hrun hpre hsp hL
  rw [withPutCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ R :=
    satisfies_lscro_pre (hcrl0.of_keepsFrozen hpre.1.2.2.2) hpre.2
  exact h x R s hpc hrun hpre' hsp hL
/-- Execute `bl bcmp` (`aRo = false, bRo = false`) inside `Dir::put::<String>`'s stack frame. -/
theorem step_bcmp_call_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hbcmp : subroutine_ok (lsProg_542 H) call_pc (withPutCSPlaced s0 cliBcmpSpec))
    (hsub : extHookStack ≤ stk - 96)
    (hle : stk ≤ 2 ^ 64)
    (a b ret_pc : BitVec 64) (bsA bsB : List (BitVec 8))
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hx1 : s.readReg64 .x1 = b)
    (hx2 : (s.readReg64 .x2).toNat = bsA.length)
    (hlen : bsB.length = bsA.length)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = ((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      ((sm.readReg64 .x0).setWidth 32 = 0#32 ↔ bsA = bsB) →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        (((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_542 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call_cs_placed (x := CliBcmpCall.mk a false bsA b false bsB)
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hbcmp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCSPlaced, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCSPlaced, cliBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCSPlaced, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' heq_iff hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)
/-- Execute `bl __rust_dealloc(ptr, cap.toNat, 1)` on `vecU8Rest A cap ptr bs` (`cap ≠ 0`)
inside `Dir::put::<String>`'s stack frame. -/
theorem step_dealloc_call_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_542 H) call_pc
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hsub : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hcap0 : cap ≠ 0)
    (hbs_le : bs.length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = (vecU8Rest A cap ptr bs ∗ A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        ((A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_542 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A) (ptr := ptr) hcap0 hbs_le hcap_lt
  refine SepWPp.call_cs_placed (x := (ptr, cap.toNat, 1))
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hdealloc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    have hm' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left hrest))) hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, by simp [hx1], by simp [hx2], hlayout⟩, ?_⟩
    convert hm' using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Execute `bl grow_one` inside `Dir::put::<String>`'s stack frame. -/
theorem step_grow_call_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hgrow : subroutine_ok (lsProg_542 H) call_pc
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)))
    (hsub : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (v cap ptr ret_pc : BitVec 64) (xs : List (List (BitVec 8) × List (BitVec 8)))
    (hcap_lt : cap.toNat < 2 ^ 32)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = (RustHeap.vecAt A 48 8 (dirEntryAt A) v cap ptr xs ∗ A.pool ∗
        stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_542 H) ret sm
        ((RustHeap.vecAt A 48 8 (dirEntryAt A) v
            (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) newPtr xs ∗
          A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_542 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call_cs_placed (x := GrowOneDirGhost.mk v cap ptr xs)
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - growStk) ∗ F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCSPlaced, growOneDirRawSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hcap_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withPutCSPlaced, growOneDirRawSpec, dirPutSpecPlaced, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withPutCSPlaced, growOneDirRawSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)
/-- Normal-return `SepWPp` postcondition expected by `subroutine_ok_of_sepWPp` for `dirPutSpecPlaced`. -/
abbrev putRetQPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat)
    (x : DirPutGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev stepDstP {a b : State} (_ : StepInvPlaced a b) : State := b

/-- Execute shared epilogue `+248 .. +272` (`LDP .. RET`) and discharge `dirPutSpecPlaced`'s postcondition. -/
theorem step_epilogue_ret_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {v3 : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hpc : s.pc = (blkPl_542).base + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        dirAt A x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let sf := stepDstP hinv_ep
  have htr_sf : sf.trace = s0.trace := by simp only [sf, stepDstP, arm64_norm, htr]
  dsimp only [sf, stepDstP] at htr_sf
  refine SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]⟩
  dsimp only [dirPutSpecPlaced]
  rw [htr_sf, pure_sepConj_of_true rfl]
  refine Entails.trans (Entails.of_eq (show _ =
    dirAt A x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
      (stackAt (s0.sp - 96#64) (stk - 96) ∗ putSavedCells s0 v3) ∗ A.pool by
    unfold putSavedCells; ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (putSavedCells_pack h96 hle_stk s0 v3)))))

/-- Execute hit-branch tail-dealloc epilogue `+156 .. +192` (`MOV X0..X2`, pop frame,
`B __rust_dealloc`) when `nameCap ≠ 0` and discharge `dirPutSpecPlaced`'s postcondition. -/
theorem step_epilogue_tail_dealloc_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {v3 nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hcap0 : nameCap ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_542).base + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        dirAt A x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsRustDeallocSymCli)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let s1 := stepDstP hinv_ep
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A) (ptr := namePtr) hcap0 hna_le hna_lt
  have hcs1 : CalleeSavedPreserved s0 s1 := by
    simp only [s1, stepDstP, CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]
  have hput_cs1 : PutCalleeSavedPlaced s0 s1 :=
    ⟨by simp only [s1, stepDstP, arm64_norm, hcs.1],
     by simp only [s1, stepDstP, arm64_norm, hcs.2.1],
     hcs.2.2.trans hinv_ep⟩
  have hsp1 : s1.sp = s0.sp := by simp only [s1, stepDstP, arm64_norm, *]
  have hsp_aligned1 : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]
    exact halign
  dsimp only [s1, stepDstP] at hcs1 hput_cs1 hsp1 hsp_aligned1
  refine SepWPp.call_cs_placed (ret_pc := s0.readReg64 .lr) (x := (namePtr, nameCap.toNat, 1))
    (F := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      dirAt A x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24)
    hdealloc
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_aligned1
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    have hpack :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
         ((s0.sp - 72#64) ↦₆₄ v3) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        stackAt (s0.sp - 96#64) (stk - 96) ⊢ stackAt s0.sp stk := by
      rw [sepConj_comm]
      exact putSavedCells_pack h96 hle_stk s0 v3
    have hm1 := Satisfies.mono
      (sepConj_mono_left (Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono hpack
          (sepConj_mono_left (Q := dirAt A x.self (x.dir.put x.name x.bytes) ∗
            memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) hrest)))) hm
    rw [stackAt_sub_split hhook hle_stk s0.sp] at hm1
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, hsp1, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hput_cs1, ⟨by simp only [arm64_norm, *], by simp [arm64_norm],
      by simp [arm64_norm], hlayout⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf hpcsf hrunsf hspsf hcsm _
    rw [hsp1] at hspsf
    simp only [withPutCSPlaced, rustDeallocExternSpecWithStack, hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun htrsf => ?_
    have htr_final : sf.trace = s0.trace := htrsf.trans (by simp only [arm64_norm, htr])
    refine SepWPp.done hpcsf hrunsf ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      hspsf, calleeSavedPreserved_trans hcs1 hcsm⟩
    dsimp only [dirPutSpecPlaced]
    rw [htr_final, pure_sepConj_of_true rfl, stackAt_sub_split hhook hle_stk s0.sp]
    exact Entails.of_eq (by ac_rfl)
/-! ## 2. Miss Path (`+196 .. +288`) -/

/-- Push `{name, bytes}` into an already non-full `Dir.changed` buffer (`+208 .. +244`)
and finish via `step_epilogue_ret_p` (`+248 .. +272`). -/
theorem step_write_miss_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hfit : x.dir.changed.length < cap.toNat)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (blkPl_542).base + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  subst hP
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hfit
    change x.dir.changed.length < 0 at hfit
    omega
  unfold RustHeap.vecAt vecHeader vecU8
  rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr x.dir.changed hcap0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap48_lt, hptr_ne⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
  have hspare_eq :
      (cap.toNat - x.dir.changed.length) * 48 =
        48 + (cap.toNat - (x.dir.changed.length + 1)) * 48 := by
    have : cap.toNat - x.dir.changed.length = 1 + (cap.toNat - (x.dir.changed.length + 1)) := by
      omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hspare_split := ProofLib.memRegion_split
    (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
    48 ((cap.toNat - (x.dir.changed.length + 1)) * 48) (by omega)
  have hslot_next :
      ptr + BitVec.ofNat 64 (x.dir.changed.length * 48) + 48#64 =
        ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48) := by
    rw [BitVec.add_assoc, show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
      ← BitVec.ofNat_add, Nat.succ_mul]
  have hmul_bv :
      BitVec.ofNat 64 (x.dir.changed.length * 48) =
        BitVec.ofNat 64 x.dir.changed.length * 48#64 := by
    rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_mul]
  rw [hspare_eq, hspare_split, hslot_next, hmul_bv,
      memRegion_48_split_entry (ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun l1 => ?_
  refine SepWPp.exists_elim fun q1 => ?_
  refine SepWPp.exists_elim fun l0 => ?_
  refine SepWPp.exists_elim fun p0 => ?_
  refine SepWPp.exists_elim fun c0 => ?_
  unfold pointsTo128
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 248#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_w
  set slot := ptr + BitVec.ofNat 64 (x.dir.changed.length * 48)
  have hslot_eq : ptr + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
    congrArg (ptr + ·) hmul_bv.symm
  have hlen1_eq :
      BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hentry_pack :
      ((slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
        vecU8Rest A nameCap namePtr x.name) ∗
      (((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes) ⊢
      dirEntryAt A (x.name, x.bytes) slot := by
    have hname_v :
        (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
          ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
          vecU8Rest A nameCap namePtr x.name ⊢ vecU8 A slot x.name := by
      have hhdr :
          (slot ↦₆₄ nameCap) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
            ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name =
          vecHeader slot nameCap namePtr (BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name := by
        unfold vecHeader; ac_rfl
      rw [hhdr]
      exact vecU8_intro_header_rest hna_le hna_lt hna_ptr
    have hbytes_v :
        ((slot + 24#64) ↦₆₄ bytesCap) ∗ ((slot + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A bytesCap bytesPtr x.bytes ⊢ vecU8 A (slot + 0x18#64) x.bytes := by
      have h40 : slot + 40#64 = (slot + 0x18#64) + 16#64 := by bv_arith
      have h24 : slot + 24#64 = slot + 0x18#64 := rfl
      rw [h40, h24]
      have hhdr2 :
          ((slot + 0x18#64) ↦₆₄ bytesCap) ∗ (((slot + 0x18#64) + 8#64) ↦₆₄ bytesPtr) ∗
            (((slot + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes =
          vecHeader (slot + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes := by
        unfold vecHeader; ac_rfl
      rw [hhdr2]
      exact vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr
    exact sepConj_mono hname_v hbytes_v
  have hput_eq : (x.dir.put x.name x.bytes) =
      { changed := x.dir.changed ++ [(x.name, x.bytes)], path := x.dir.path } := by
    simp only [DirGhost.put, setOrPush_miss hmiss]
  have hvec_pack :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (x.dir.changed.length + 1)) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        (arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗ dirEntryAt A (x.name, x.bytes) slot) ∗
        memRegion (ptr + BitVec.ofNat 64 ((x.dir.changed.length + 1) * 48))
          ((cap.toNat - (x.dir.changed.length + 1)) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A x.self (x.dir.put x.name x.bytes) := by
    have hnew_len : (x.dir.changed ++ [(x.name, x.bytes)]).length = x.dir.changed.length + 1 := by
      simp
    rw [hput_eq, ← arrayAt_concat (dirEntryAt A) 48 ptr x.dir.changed (x.name, x.bytes),
        ← hnew_len]
    refine Entails.trans ?_
      (dirAt_of_vecAt A x.self cap ptr (x.dir.changed ++ [(x.name, x.bytes)]) x.dir.path)
    unfold RustHeap.vecAt vecHeader
    rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr _ hcap0,
        pure_sepConj_of_true ⟨by rw [hnew_len]; omega, hcap48_lt, hptr_ne⟩]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre ?_
    (step_epilogue_ret_p (A := A) (H := H) (stk := stk) (v3 := v3) (R := R)
      h96 hle_stk
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv_w)
      rfl)
  rw [hslot_eq, hlen1_eq]
  have hbytesV_mem :
      ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ⊢ memRegion x.bytesV 24 := by
    have hhdrV :
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) =
        vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) := by
      unfold vecHeader; ac_rfl
    rw [hhdrV]
    exact vecHeader_entails_memRegion x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hvec_pack
        (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (sepConj_mono_right hentry_pack)))))))))
/-- Full miss handler (`+196 .. +288`): checks capacity at `+196 .. +204`, calls `grow_one`
at `+276 .. +288` if `len = cap`, and delegates to `step_write_miss_p` at `+208`. -/
theorem step_miss_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (blkPl_542).base + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  subst hP
  unfold RustHeap.vecAt vecHeader
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right (vecBuf_expose_arrayAt A 48 8 (dirEntryAt A) cap ptr x.dir.changed))))) ?_
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧
        x.dir.changed.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_le, hcap48_lt, _, hptr_ne⟩ => ?_
  have hvec_back :
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr x.dir.changed ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((cap.toNat - x.dir.changed.length) * 48))) =
      RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
    unfold RustHeap.vecAt vecHeader vecBuf
    rw [pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩]
    by_cases h0 : cap = 0
    · subst h0
      have hnil : x.dir.changed = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_le)
      simp only [hnil, ↓reduceIte, arrayAt_nil]
      ac_rfl
    · simp only [h0, ↓reduceIte]
      ac_rfl
  by_cases hcap_eq : BitVec.ofNat 64 x.dir.changed.length = cap
  · have hcap_nat : cap.toNat = x.dir.changed.length := by
      rw [← hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 586)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retGrow := (blkPl_542).base + 284#64
    refine step_grow_call_p (A := A) (H := H) (growStk := growStk) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes)
      hgrow hgrow_stk hle_stk x.self cap ptr retGrow x.dir.changed
      (by omega)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      halign
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by rw [← hvec_back]; ac_rfl)
      fun sm newPtr hpcm hrunm hspm htrm hcsm hput_csm => ?_
    dsimp only [retGrow] at hpcm
    clear retGrow
    rcases hcsm with ⟨hc19, hc20, hc21, hc22, hc23, hc24, _, _, _, _, _, _⟩
    have sm_x19 : sm.readReg64 .x19 = namePtr := hc19.trans (by simp only [arm64_norm, *])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hc20.trans (by simp only [arm64_norm, *])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hc21.trans (by simp only [arm64_norm, *])
    have sm_x22 : sm.readReg64 .x22 = x.self := hc22.trans (by simp only [arm64_norm, *])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hc23.trans (by simp only [arm64_norm, *])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hc24.trans (by simp only [arm64_norm, *])
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    unfold RustHeap.vecAt vecHeader
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 208#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hnew_fit : x.dir.changed.length < newCap.toNat := by
      simp only [newCap, BitVec.toNat_ofNat, hcap_nat]
      omega
    refine SepWPp.weaken_pre ?_
      (step_write_miss_p (A := A) (H := H) (stk := stk)
        (v3 := v3) (cap := newCap) (ptr := newPtr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hnew_fit hna_le hna_lt hna_ptr
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hput_csm.step (by simp only [arm64_norm]) hinv2)
        rfl)
    unfold RustHeap.vecAt vecHeader
    exact Entails.of_eq (by ac_rfl)
  · have hfit : x.dir.changed.length < cap.toNat := by
      have hne_nat : x.dir.changed.length ≠ cap.toNat := by
        intro heq
        apply hcap_eq
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact heq
      omega
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 208#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_write_miss_p (A := A) (H := H) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr)
        (R := R)
        h96 hle_stk hmiss hlen_lt32 hfit hna_le hna_lt hna_ptr
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    rw [← hvec_back]
    exact Entails.of_eq (by ac_rfl)
/-! ## 3. Hit Exit (`+112 .. +192`) and Search Loop (`+68 .. +108`) -/

private structure Hide (P : Prop) : Prop where
  out : P

@[irreducible] def PutCalleeOkPlaced [LibsignalPlacement] {α : Type}
    (H : LibsignalHooks) (target : BitVec 64) (spec : Spec α) : Prop :=
  subroutine_ok (lsProg_542 H) target spec

theorem putCalleeOkPlaced_mk [LibsignalPlacement] {α : Type}
    (H : LibsignalHooks) (target : BitVec 64) {spec : Spec α}
    (h : subroutine_ok (lsProg_542 H) target spec) :
    PutCalleeOkPlaced H target spec := by
  unfold PutCalleeOkPlaced
  exact h

theorem putCalleeOkPlaced_get [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {target : BitVec 64} {spec : Spec α}
    (h : PutCalleeOkPlaced H target spec) :
    subroutine_ok (lsProg_542 H) target spec := by
  unfold PutCalleeOkPlaced at h
  exact h

/-- Shared hit-branch continuation (`+136 .. +152`): writes `{bytes}` over `[curPtr + 24 .. +48)`,
reassembles `dirAt A x.self (x.dir.put x.name x.bytes)`, and branches on `nameCap = 0` between
`step_epilogue_ret_p` (`+248`) and `step_epilogue_tail_dealloc_p` (`+156`). -/
theorem step_hit_store_and_exit_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr oldCap oldPtr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_542).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A (ptr + BitVec.ofNat 64 (pre.length * 48)) x.name ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64) ↦₆₄ oldCap) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64) ↦₆₄ oldPtr) ∗
        ((ptr + BitVec.ofNat 64 (pre.length * 48) + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  clear hdealloc
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq_h.out, List.length_append, List.length_cons] at hlen_le
    omega
  have h32 : curPtr + 32#64 = (curPtr + 24#64) + 8#64 := by bv_arith
  have h40 : curPtr + 40#64 = (curPtr + 24#64) + 16#64 := by bv_arith
  rw [h32, h40,
      show vecU8 A x.bytesV x.bytes =
        (∃∗ bytesCap : BitVec 64, ∃∗ bytesPtr : BitVec 64,
          vecU8At A x.bytesV bytesCap bytesPtr x.bytes) from rfl]
  clear h32 h40
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun bytesCap => ?_
  refine SepWPp.exists_elim fun bytesPtr => ?_
  rw [vecU8At_eq_header_rest' A x.bytesV bytesCap bytesPtr x.bytes,
      show vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) =
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.bytes.length ≤ bytesCap.toNat ∧ bytesCap.toNat < 2 ^ 63 ∧ bytesPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        (x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Rest A bytesCap bytesPtr x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hbs_le, hbs_lt, hbs_ptr⟩ => ?_
  have hbytesV_mem :
      ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ⊢ memRegion x.bytesV 24 := by
    have hhdrV :
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) =
        vecHeader x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) := by
      unfold vecHeader; ac_rfl
    rw [hhdrV]
    exact vecHeader_entails_memRegion x.bytesV bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length)
  have hdir_pack :
      vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
          ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Rest A bytesCap bytesPtr x.bytes) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
      dirAt A x.self (x.dir.put x.name x.bytes) := by
    have hnew_entry :
        vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ⊢
        dirEntryAt A (x.name, x.bytes) curPtr := by
      have hhdr2 :
          ((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes =
          vecHeader (curPtr + 0x18#64) bytesCap bytesPtr (BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes := by
        unfold vecHeader; ac_rfl
      rw [hhdr2]
      exact sepConj_mono_right (vecU8_intro_header_rest hbs_le hbs_lt hbs_ptr)
    have hput_eq : (x.dir.put x.name x.bytes) =
        { changed := pre ++ (x.name, x.bytes) :: rest, path := x.dir.path } := by
      simp only [DirGhost.put, hx_eq_h.out, setOrPush_hit hpre]
    have hlen_same : (pre ++ (x.name, x.bytes) :: rest).length = x.dir.changed.length := by
      rw [hx_eq_h.out, List.length_append, List.length_append, List.length_cons, List.length_cons]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (Entails.trans (by rw [← sepConj_assoc]; exact Entails.refl _)
          (sepConj_mono_left hnew_entry))))) ?_
    have harr_join :
        arrayAt (dirEntryAt A) 48 ptr pre ∗
          (dirEntryAt A (x.name, x.bytes) curPtr ∗
            arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest) =
        arrayAt (dirEntryAt A) 48 ptr (pre ++ (x.name, x.bytes) :: rest) := by
      rw [arrayAt_append (dirEntryAt A) 48 ptr pre ((x.name, x.bytes) :: rest), arrayAt_cons]
    rw [hput_eq]
    refine Entails.trans ?_
      (dirAt_of_vecAt A x.self cap ptr (pre ++ (x.name, x.bytes) :: rest) x.dir.path)
    unfold RustHeap.vecAt
    rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr _ hcap0, hlen_same,
        pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩, ← harr_join]
    exact Entails.of_eq (by ac_rfl)
  by_cases hncap0 : nameCap = 0
  · subst hncap0
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 248#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_ret_p (A := A) (H := H) (stk := stk) (v3 := v3) (R := R)
        h96 hle_stk
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    rw [show vecU8Rest A 0 namePtr x.name = emp from rfl]
    simp only [emp_sepConj]
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem)))))
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 156#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_s
    refine SepWPp.weaken_pre ?_
      (step_epilogue_tail_dealloc_p (A := A) (H := H) (stk := stk)
        (v3 := v3) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 hhook hle_stk hncap0 hna_le hna_lt
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (hcs.step (by simp only [arm64_norm]) hinv_s)
        rfl)
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        (vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          vecU8 A curPtr x.name ∗
          (((curPtr + 24#64) ↦₆₄ bytesCap) ∗ ((curPtr + 24#64 + 8#64) ↦₆₄ bytesPtr) ∗
            ((curPtr + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Rest A bytesCap bytesPtr x.bytes) ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path) ∗
        memRegion x.nameV 24 ∗
        ((x.bytesV ↦₆₄ bytesCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bytesPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length)) ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hdir_pack
          (sepConj_mono_right (sepConj_mono_left hbytesV_mem))))))
/-- Full hit exit (`+112 .. +192`): drops `entry.bytes` if `oldCap ≠ 0` (`+112 .. +132`),
then calls `step_hit_store_and_exit_p` (`+136 .. +152`). -/
theorem step_hit_exit_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (x.name, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_542).base + 112#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A (x.name, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (x.name, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A (x.name, oldBs) curPtr =
        vecU8 A curPtr x.name ∗
          (∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
            vecU8At A (curPtr + 0x18#64) oldCap oldPtr oldBs) from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun oldCap => ?_
  refine SepWPp.exists_elim fun oldPtr => ?_
  rw [vecU8At_eq_header_rest' A (curPtr + 0x18#64) oldCap oldPtr oldBs,
      show vecHeader (curPtr + 0x18#64) oldCap oldPtr (BitVec.ofNat 64 oldBs.length) =
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗ (((curPtr + 0x18#64) + 8#64) ↦₆₄ oldPtr) ∗
          (((curPtr + 0x18#64) + 16#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) from rfl]
  have hcur24 : curPtr + 32#64 - 8#64 = curPtr + 24#64 := by bv_arith
  have hcur32 : (curPtr + 0x18#64) + 8#64 = curPtr + 32#64 := by bv_arith
  have hcur40 : (curPtr + 0x18#64) + 16#64 = curPtr + 40#64 := by bv_arith
  rw [hcur32, hcur40]
  clear hcur32 hcur40
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜oldBs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Rest A oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hold_le, hold_lt, _⟩ => ?_
  by_cases hold0 : oldCap = 0
  · subst hold0
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 136#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    rw [show vecU8Rest A 0 oldPtr oldBs = emp from rfl]
    simp only [emp_sepConj]
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit_p (A := A) (H := H) (stk := stk)
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := 0) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm]; rfl)
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl)
    exact Entails.refl _
  · apply SepWPp.of_sepWP_cs_placed (mid := lsρ lsRustDeallocSymCli)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    let retDealloc := (blkPl_542).base + 136#64
    refine step_dealloc_call_p (A := A) (H := H) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        vecU8 A curPtr x.name ∗
        ((curPtr + 24#64) ↦₆₄ oldCap) ∗
        ((curPtr + 32#64) ↦₆₄ oldPtr) ∗
        ((curPtr + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes)
      hdealloc hhook96 hle_stk oldCap oldPtr retDealloc oldBs
      hold0 hold_le hold_lt
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by ac_rfl)
      fun sm hpcm hrunm hspm htrm hcsm hput_csm => ?_
    dsimp only [retDealloc] at hpcm
    clear retDealloc
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = ptr + BitVec.ofNat 64 (pre.length * 48) + 24#64 :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm]; rfl)
    clear hcsm hinv1
    refine SepWPp.weaken_pre ?_
      (step_hit_store_and_exit_p (A := A) (H := H) (stk := stk)
        (pre := pre) (rest := rest) (oldBs := oldBs)
        (v3 := v3) (cap := cap) (ptr := ptr)
        (oldCap := oldCap) (oldPtr := oldPtr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hdealloc0) h96 (by omega) hle_stk
        hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
        hpcm hrunm hspm halign htrm
        sm_x19 sm_x20 sm_x21 sm_x22
        hput_csm
        rfl)
    exact Entails.of_eq (by dsimp only [curPtr]; ac_rfl)
/-- Loop latch (`+68 .. +76`): advances `X27 -= 48, X26 += 48`, exiting to `step_miss_p` (`+196`)
when `rest = []` or invoking `hcont` at `+80` when `rest = hd' :: rest'`. -/
theorem step_latch_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre : List (List (BitVec 8) × List (BitVec 8))}
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ hd :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hd.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (blkPl_542).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd :: rest).length))
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
    (hcont : ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (blkPl_542).base + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSavedPlaced s0 sn →
      SepWPp (lsProg_542 H) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr (pre ++ [hd]) ∗
          dirEntryAt A hd' (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48)) ∗
          arrayAt (dirEntryAt A) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)
        (putRetQPlaced A stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  have hgrow0 := putCalleeOkPlaced_mk H (lsmpl.base 586) hgrow
  clear hgrow
  subst hP
  have hpre' : ∀ e ∈ pre ++ [hd], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with h1 | h2
    · exact hpre e h1
    · rcases List.mem_singleton.mp h2 with rfl
      exact hhd_ne
  have hcap0 : cap ≠ 0 := by
    intro h0
    rw [h0] at hlen_le
    change x.dir.changed.length ≤ 0 at hlen_le
    rw [hx_eq, List.length_append, List.length_cons] at hlen_le
    omega
  cases rest with
  | nil =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ [hd]) := ⟨hx_eq⟩
    clear hx_eq
    have _ : Hide _ := ⟨hcont⟩
    clear hcont
    have hx27_48 : s.readReg64 .x27 = 48#64 := hx27
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 196#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_l
    have hvec_join :
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) [] ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) =
        RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed := by
      have harr_cat :
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) =
          arrayAt (dirEntryAt A) 48 ptr x.dir.changed := by
        rw [hx_eq_h.out, show hd :: ([] : List _) = [hd] from rfl,
            arrayAt_concat (dirEntryAt A) 48 ptr pre hd]
      unfold RustHeap.vecAt
      rw [vecBuf_of_ne_zero A 48 8 (dirEntryAt A) cap ptr x.dir.changed hcap0,
          pure_sepConj_of_true ⟨hlen_le, hcap48_lt, hptr_ne⟩,
          arrayAt_nil, emp_sepConj, ← harr_cat]
      ac_rfl
    refine SepWPp.weaken_pre ?_
      (step_miss_p (A := A) (H := H) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
        (by rwa [hx_eq_h.out])
        hlen_lt32 hna_le hna_lt hna_ptr
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (hcs.step (by simp only [arm64_norm]) hinv_l)
        rfl)
    refine Entails.of_eq ?_
    rw [← hvec_join]
    ac_rfl
  | cons hd' rest' =>
    have hx_eq_h : Hide (x.dir.changed = pre ++ hd :: hd' :: rest') := ⟨hx_eq⟩
    clear hx_eq
    have hcont_h : Hide _ := ⟨hcont⟩
    clear hcont
    have hrem_bound : 48 * (hd :: hd' :: rest').length < 2 ^ 64 := by
      rw [hx_eq_h.out, List.length_append] at hlen_lt32
      simp only [List.length_cons] at hlen_lt32 ⊢
      omega
    have hx27' : s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) + 48#64 := by
      rw [hx27, List.length_cons (a := hd), Nat.mul_succ, BitVec.ofNat_add]
    clear hx27
    have hx27_ne0 : BitVec.ofNat 64 (48 * (hd' :: rest').length) ≠ 0#64 := by
      intro h0
      have h := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by simp only [List.length_cons] at hrem_bound ⊢; omega),
          BitVec.toNat_zero] at h
      simp only [List.length_cons] at h
      omega
    generalize hrem_eq : BitVec.ofNat 64 (48 * (hd' :: rest').length) = rem at hx27' hx27_ne0
    have hrem_h : Hide _ := ⟨hrem_eq⟩
    clear hrem_eq hrem_bound
    have hcur_next :
        ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64 =
          ptr + BitVec.ofNat 64 ((pre ++ [hd]).length * 48) := by
      have hl : (pre ++ [hd]).length = pre.length + 1 := by simp
      rw [hl, BitVec.add_assoc,
          show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
          ← BitVec.ofNat_add, Nat.succ_mul]
    have hcur_next_h : Hide _ := ⟨hcur_next⟩
    clear hcur_next
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 80#64)
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv_l
    refine SepWPp.weaken_pre ?_
      (hcont_h.out hd' rest' _ rfl
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm]; rw [← hcur_next_h.out]; bv_arith)
        (by simp only [arm64_norm, ← hrem_h.out])
        (hcs.step (by simp only [arm64_norm]) hinv_l))
    rw [hcur_next_h.out, arrayAt_cons, arrayAt_concat (dirEntryAt A) 48 ptr pre hd]
    exact Entails.of_eq (by ac_rfl)
/-- Single iteration of the search loop body (`+80 .. +108`) at entry `(eName, oldBs)` followed by
`rest`: compares lengths (`+80 .. +88`), optionally calls `bcmp` (`+92 .. +108`), exits via
`step_hit_exit_p` on a match (`eName = x.name`), or advances via `step_latch_p` on a mismatch (`eName ≠ x.name`). -/
theorem step_loop_body_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 s : State} {x : DirPutGhost}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {eName oldBs : List (BitVec 8)}
    {v3 cap ptr nameCap namePtr : BitVec 64} {P R : SepProp}
    (hbcmp : subroutine_ok (lsProg_542 H) (lsρ cliBcmpName)
      (withPutCSPlaced s0 cliBcmpSpec))
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hx_eq : x.dir.changed = pre ++ (eName, oldBs) :: rest)
    (hpre : ∀ e ∈ pre, e.1 ≠ x.name)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (hpc : s.pc = (blkPl_542).base + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hx21 : s.readReg64 .x21 = x.bytesV)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.name.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length)
    (hx25 : s.readReg64 .x25 = ptr)
    (hx26 : s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length))
    (hcs : PutCalleeSavedPlaced s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A (eName, oldBs) (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
        arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
    (hcont : eName ≠ x.name →
      ∀ (hd' : List (BitVec 8) × List (BitVec 8))
        (rest' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest = hd' :: rest' →
      sn.pc = (blkPl_542).base + 80#64 →
      sn.status = .Running →
      sn.sp = s0.sp - 96#64 →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = namePtr →
      sn.readReg64 .x20 = nameCap →
      sn.readReg64 .x21 = x.bytesV →
      sn.readReg64 .x22 = x.self →
      sn.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      sn.readReg64 .x25 = ptr →
      sn.readReg64 .x26 = ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 32#64 →
      sn.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd' :: rest').length) →
      PutCalleeSavedPlaced s0 sn →
      SepWPp (lsProg_542 H) (s0.readReg64 .lr) sn
        (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr (pre ++ [(eName, oldBs)]) ∗
          dirEntryAt A hd' (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48)) ∗
          arrayAt (dirEntryAt A) 48
            (ptr + BitVec.ofNat 64 ((pre ++ [(eName, oldBs)]).length * 48) + 48#64) rest' ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)
        (putRetQPlaced A stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
      (putRetQPlaced A stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  have hgrow0 := putCalleeOkPlaced_mk H (lsmpl.base 586) hgrow
  have hcont_h : Hide _ := ⟨hcont⟩
  clear hdealloc hgrow hcont
  subst hP
  have hx_eq_h : Hide (x.dir.changed = pre ++ (eName, oldBs) :: rest) := ⟨hx_eq⟩
  clear hx_eq
  set curPtr := ptr + BitVec.ofNat 64 (pre.length * 48)
  rw [show dirEntryAt A (eName, oldBs) curPtr =
        (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64, vecU8At A curPtr eCap ePtr eName) ∗
          vecU8 A (curPtr + 0x18#64) oldBs from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun eCap => ?_
  refine SepWPp.exists_elim fun ePtr => ?_
  rw [vecU8At_eq_header_rest' A curPtr eCap ePtr eName,
      show vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) =
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) from rfl]
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜eName.length ≤ eCap.toNat ∧ eCap.toNat < 2 ^ 63 ∧ ePtr ≠ 0⌝ ∗
      (putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A eCap ePtr eName ∗
        vecU8 A (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨he_le, he_lt, he_ptr⟩ => ?_
  have he_repack :
      ((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        vecU8Rest A eCap ePtr eName) ∗
        vecU8 A (curPtr + 0x18#64) oldBs ⊢
      dirEntryAt A (eName, oldBs) curPtr := by
    refine sepConj_mono_left ?_
    have hhdr :
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName =
        vecHeader curPtr eCap ePtr (BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName := by
      unfold vecHeader; ac_rfl
    rw [hhdr]
    exact vecU8_intro_header_rest he_le he_lt he_ptr
  have hcur16 : curPtr + 32#64 - 16#64 = curPtr + 16#64 := by bv_arith
  have hcur8 : curPtr + 32#64 - 24#64 = curPtr + 8#64 := by bv_arith
  by_cases hlen_eq : BitVec.ofNat 64 eName.length = BitVec.ofNat 64 x.name.length
  · have hlen_nat : eName.length = x.name.length := by
      have h := congrArg BitVec.toNat hlen_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
      exact h
    apply SepWPp.of_sepWP_cs_placed (mid := lsρ cliBcmpName)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    rw [vecU8Rest_expose_bytes (A := A) (cap := eCap) (ptr := ePtr) he_le,
        vecU8Rest_expose_bytes (A := A) (cap := nameCap) (ptr := namePtr) hna_le]
    have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = eName.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen_nat]
    let retBcmp := (blkPl_542).base + 108#64
    refine step_bcmp_call_p (A := A) (H := H) (stk := stk)
      (x0 := x) (R := R)
      (F := putSavedCells s0 v3 ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
        ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
        (if eCap = 0 then emp
         else A.live ePtr eCap.toNat 1 ∗
           memRegion (ePtr + BitVec.ofNat 64 eName.length) (eCap.toNat - eName.length)) ∗
        vecU8 A (curPtr + 0x18#64) oldBs ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        (if nameCap = 0 then emp
         else A.live namePtr nameCap.toNat 1 ∗
           memRegion (namePtr + BitVec.ofNat 64 x.name.length) (nameCap.toNat - x.name.length)) ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool)
      hbcmp hhook96 hle_stk ePtr namePtr retBcmp eName x.name
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      halign
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, *]; rfl)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hx2_nat])
      hlen_nat.symm
      (hcs.step (by simp only [arm64_norm]) hinv1)
      (by ac_rfl)
      fun sm hpcm hrunm hspm htrm heq_iff hcsm hput_csm => ?_
    dsimp only [retBcmp] at hpcm
    clear retBcmp
    have sm_x19 : sm.readReg64 .x19 = namePtr := hcsm.1.trans (by simp only [arm64_norm, hx19])
    have sm_x20 : sm.readReg64 .x20 = nameCap := hcsm.2.1.trans (by simp only [arm64_norm, hx20])
    have sm_x21 : sm.readReg64 .x21 = x.bytesV := hcsm.2.2.1.trans (by simp only [arm64_norm, hx21])
    have sm_x22 : sm.readReg64 .x22 = x.self := hcsm.2.2.2.1.trans (by simp only [arm64_norm, hx22])
    have sm_x23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.name.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, hx23])
    have sm_x24 : sm.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx24])
    have sm_x25 : sm.readReg64 .x25 = ptr := hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
    have sm_x26 : sm.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 :=
      hcsm.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx26]; rfl)
    have sm_x27 : sm.readReg64 .x27 = BitVec.ofNat 64 (48 * ((eName, oldBs) :: rest).length) :=
      hcsm.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx27])
    clear hcsm hinv1
    refine SepWPp.weaken_pre
      (show _ ⊢
        putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A (eName, oldBs) curPtr ∗
          arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool by
        refine Entails.trans (Entails.of_eq (show _ =
          putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
            vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
              ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
              vecU8Rest A eCap ePtr eName) ∗
              vecU8 A (curPtr + 0x18#64) oldBs) ∗
            arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            vecU8Rest A nameCap namePtr x.name ∗
            memRegion x.nameV 24 ∗
            vecU8 A x.bytesV x.bytes ∗ A.pool by
            rw [vecU8Rest_expose_bytes (A := A) (cap := eCap) (ptr := ePtr) he_le,
                vecU8Rest_expose_bytes (A := A) (cap := nameCap) (ptr := namePtr) hna_le]
            ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))) ?_
    by_cases hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32
    · have heq_name : eName = x.name := heq_iff.mp hw0
      subst heq_name
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 112#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_hit_exit_p (A := A) (H := H) (stk := stk)
          (pre := pre) (rest := rest) (oldBs := oldBs)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOkPlaced_get hdealloc0) h96 hhook96 hle_stk
          hx_eq_h.out hpre hlen_le hcap48_lt hptr_ne hna_le hna_lt
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x26])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl)
      exact Entails.refl _
    · have hne_name : eName ≠ x.name := mt heq_iff.mpr hw0
      have hw0_64 :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        exact hw0 (by simpa using congrArg (BitVec.truncate 32) h0)
      apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 68#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      refine SepWPp.weaken_pre ?_
        (step_latch_p (A := A) (H := H) (growStk := growStk) (stk := stk)
          (pre := pre) (hd := (eName, oldBs)) (rest := rest)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
          hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
          hna_le hna_lt hna_ptr
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm])
          halign
          (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, sm_x19])
          (by simp only [arm64_norm, sm_x20])
          (by simp only [arm64_norm, sm_x21])
          (by simp only [arm64_norm, sm_x22])
          (by simp only [arm64_norm, sm_x23])
          (by simp only [arm64_norm, sm_x24])
          (by simp only [arm64_norm, sm_x25])
          (by simp only [arm64_norm, sm_x26])
          (by simp only [arm64_norm, sm_x27])
          (hput_csm.step (by simp only [arm64_norm]) hinv2)
          rfl
          (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
            hcont_h.out hne_name hd' rest' sn hrest hpcsn
              h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
      exact Entails.refl _
  · have hne_name : eName ≠ x.name := fun h => hlen_eq (h ▸ rfl)
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 68#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (step_latch_p (A := A) (H := H) (growStk := growStk) (stk := stk)
        (pre := pre) (hd := (eName, oldBs)) (rest := rest)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hle_stk
        hx_eq_h.out hpre hne_name hlen_lt32 hlen_le hcap48_lt hptr_ne
        hna_le hna_lt hna_ptr
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm, hsp])
        halign
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23])
        (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm, hx26]; rfl)
        (by simp only [arm64_norm, hx27])
        (hcs.step (by simp only [arm64_norm]) hinv1)
        rfl
        (fun hd' rest' sn hrest hpcsn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
          hcont_h.out hne_name hd' rest' sn hrest hpcsn
            h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12))
    refine Entails.trans (Entails.of_eq (show _ =
      putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        (((curPtr ↦₆₄ eCap) ∗ ((curPtr + 8#64) ↦₆₄ ePtr) ∗
          ((curPtr + 16#64) ↦₆₄ BitVec.ofNat 64 eName.length) ∗
          vecU8Rest A eCap ePtr eName) ∗
          vecU8 A (curPtr + 0x18#64) oldBs) ∗
        arrayAt (dirEntryAt A) 48 (curPtr + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
          ((cap.toNat - x.dir.changed.length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        vecU8Rest A nameCap namePtr x.name ∗
        memRegion x.nameV 24 ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left he_repack))))))
/-- Search loop (`+80 .. +108` + `+68 .. +76`) over `hd :: rest`: finds the first entry whose
name equals `x.name` (`step_hit_exit_p`) or falls through the end into `step_miss_p`. -/
theorem step_loop_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    {s0 : State} {x : DirPutGhost}
    {v3 cap ptr nameCap namePtr : BitVec 64} {R : SepProp}
    (hbcmp : subroutine_ok (lsProg_542 H) (lsρ cliBcmpName)
      (withPutCSPlaced s0 cliBcmpSpec))
    (hdealloc : subroutine_ok (lsProg_542 H) (lsρ lsRustDeallocSymCli)
      (withPutCSPlaced s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)))
    (h96 : 0x60 ≤ stk)
    (hhook96 : extHookStack ≤ stk - 96)
    (hgrow_stk : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (hlen_lt32 : x.dir.changed.length < 2 ^ 32)
    (hlen_le : x.dir.changed.length ≤ cap.toNat)
    (hcap48_lt : cap.toNat * 48 < 2 ^ 63)
    (hptr_ne : ptr ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hna_ptr : namePtr ≠ 0)
    (halign : s0.sp &&& 15#64 = 0#64)
    (rest : List (List (BitVec 8) × List (BitVec 8))) :
    ∀ (pre : List (List (BitVec 8) × List (BitVec 8)))
      (hd : List (BitVec 8) × List (BitVec 8))
      (s : State) (P : SepProp),
      x.dir.changed = pre ++ hd :: rest →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      s.pc = (blkPl_542).base + 80#64 →
      s.status = .Running →
      s.sp = s0.sp - 96#64 →
      s.trace = s0.trace →
      s.readReg64 .x19 = namePtr →
      s.readReg64 .x20 = nameCap →
      s.readReg64 .x21 = x.bytesV →
      s.readReg64 .x22 = x.self →
      s.readReg64 .x23 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x24 = BitVec.ofNat 64 x.dir.changed.length →
      s.readReg64 .x25 = ptr →
      s.readReg64 .x26 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 (48 * (hd :: rest).length) →
      PutCalleeSavedPlaced s0 s →
      P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
          vecHeader x.self cap ptr (BitVec.ofNat 64 x.dir.changed.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A hd (ptr + BitVec.ofNat 64 (pre.length * 48)) ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (pre.length * 48) + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          memRegion x.nameV 24 ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool →
      SepWPp (lsProg_542 H) (s0.readReg64 .lr) s P
        (putRetQPlaced A stk x s0 R)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpecPlaced A stk).onPanic x s0 sf ∗ R)) :=
  match rest with
  | [] => fun pre ⟨eName, oldBs⟩ s P hx_eq hpre hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP =>
    step_loop_body_p (A := A) (H := H) (growStk := growStk) (stk := stk)
      (s0 := s0) (s := s) (x := x) (pre := pre) (rest := []) (eName := eName) (oldBs := oldBs)
      (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (P := P) (R := R)
      hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
      hx_eq hpre hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr
      hpc hrun hsp halign htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP
      (fun _ _ _ _ hnil => nomatch hnil)
  | hd2 :: rest2 => fun pre ⟨eName, oldBs⟩ s P hx_eq hpre hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP =>
    step_loop_body_p (A := A) (H := H) (growStk := growStk) (stk := stk)
      (s0 := s0) (s := s) (x := x) (pre := pre) (rest := hd2 :: rest2)
      (eName := eName) (oldBs := oldBs)
      (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (P := P) (R := R)
      hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
      hx_eq hpre hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr
      hpc hrun hsp halign htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hcs hP
      (fun hne_cur _ _ sn hcons hpcsn hrunsn hspsn htrsn
          hx19s hx20s hx21s hx22s hx23s hx24s hx25s hx26s hx27s hcssn => by
        obtain ⟨rfl, rfl⟩ := List.cons.inj hcons
        exact step_loop_p (A := A) (H := H) (growStk := growStk) (stk := stk)
          (s0 := s0) (x := x)
          (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
          hbcmp hdealloc hgrow h96 hhook96 hgrow_stk hle_stk
          hlen_lt32 hlen_le hcap48_lt hptr_ne hna_le hna_lt hna_ptr halign
          rest2 (pre ++ [(eName, oldBs)]) hd2 sn _
          (by rw [hx_eq, List.append_assoc]; rfl)
          (fun e he => by
            rcases List.mem_append.mp he with h1 | h2
            · exact hpre e h1
            · rcases List.mem_singleton.mp h2 with rfl
              exact hne_cur)
          hpcsn hrunsn hspsn htrsn
          hx19s hx20s hx21s hx22s hx23s hx24s hx25s hx26s hx27s hcssn rfl)

end CryptoVerification.SignalSession.Cli.Put.Helpers
namespace CryptoVerification.SignalSession.Cli.Put

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Put.Helpers

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

private theorem mul_48_bv (n : BitVec 64) :
    ((n + (n <<< 1)) <<< 4) = 48#64 * n := by
  bv_bits

private theorem bcmp_ok_542 [LibsignalPlacement] {H : LibsignalHooks}
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec) :
    subroutine_ok (lsProg_542 H) (lsρ cliBcmpName) cliBcmpSpec :=
  ls_hook_ok_ultra_of_mem hBcmp (by decide)

/-- `Dir::put::<String>` satisfies `dirPutSpecPlaced A stk` on Block 542 under `[LibsignalPlacement]`. -/
theorem dirPut_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x60 + max growStk extHookStack ≤ stk) :
    subroutine_ok (lsProg_542 H) (lsmpl.base 542) (dirPutSpecPlaced A stk) := by
  have hGrow542 : subroutine_ok (lsProg_542 H) (lsmpl.base 586) (growOneDirSpecPlaced A growStk) :=
    ls_transfer_lscro (callerProg := lsProg_542 H) hGrow (by decide) hjGrow hjGrow_unmut
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  rw [show lsmpl.base 542 = (blkPl_542).base + 0#64 by rw [BitVec.add_zero]; rfl] at hpc0
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using hsp0
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [dirPutSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen_lt32⟩, hmem⟩
  rw [show dirAt A x.self x.dir =
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          RustHeap.vecAt A 48 8 (dirEntryAt A) x.self cap ptr x.dir.changed) ∗
          strRefAt (x.self + 0x18#64) x.dir.path from rfl,
      show vecU8 A x.nameV x.name =
        (∃∗ nameCap : BitVec 64, ∃∗ namePtr : BitVec 64,
          vecU8At A x.nameV nameCap namePtr x.name) from rfl] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨nameCap, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨namePtr, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨cap, hmem⟩ := hmem
  rw [satisfies_sepExists] at hmem; obtain ⟨ptr, hmem⟩ := hmem
  have hstk_le : stk ≤ 2 ^ 64 := by
    have hcell : s0.mem ⊨ (x.self ↦₆₄ cap) ∗ (stackAt s0.sp stk ∗
        (((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8At A x.nameV nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool ∗ R)) := by
      unfold RustHeap.vecAt vecHeader at hmem
      convert hmem using 1; ac_rfl
    exact Nat.le_of_lt (stk_lt_two_pow_64 (by omega) hcell)
  have h96 : 0x60 ≤ stk := by omega
  have hgrow_stk : growStk ≤ stk - 96 := by omega
  have hhook96 : extHookStack ≤ stk - 96 := by omega
  have hbcmp := subroutine_ok_withPutCSPlaced s0 (bcmp_ok_542 hBcmp)
  have hdealloc := subroutine_ok_withPutCSPlaced_lscro s0 hcrl0
    (dealloc_lscro_of_cli (callerProg := lsProg_542 H) hC)
  have hgrow : subroutine_ok (lsProg_542 H) (lsmpl.base 586)
      (withPutCSPlaced s0 (growOneDirRawSpec A growStk)) :=
    subroutine_ok_withPutCSPlaced_lscro s0 hcrl0 hGrow542
  rw [stackAt_put_frame h96 hstk_le s0.sp,
      vecU8At_eq_header_rest' A x.nameV nameCap namePtr x.name] at hmem
  simp only [← sepConj_assoc] at hmem
  refine ⟨_, R, hmem, ?_⟩
  have hbcmp0 := putCalleeOkPlaced_mk H (lsρ cliBcmpName) hbcmp
  have hdealloc0 := putCalleeOkPlaced_mk H (lsρ lsRustDeallocSymCli) hdealloc
  have hgrow0 := putCalleeOkPlaced_mk H (lsmpl.base 586) hgrow
  clear hbcmp hdealloc hgrow hGrow542 hGrow hC hBcmp
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
  unfold RustHeap.vecAt vecHeader
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜x.name.length ≤ nameCap.toNat ∧ nameCap.toNat < 2 ^ 63 ∧ namePtr ≠ 0⌝ ∗
      (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
        ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
        ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
        ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
        ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
        ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
        stackAt (s0.sp - 96#64) (stk - 96) ∗
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hna_le, hna_lt, hna_ptr⟩ => ?_
  have hsp_align96 : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  cases hchanged : x.dir.changed with
  | nil =>
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 196#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_p
    refine SepWPp.weaken_pre ?_
      (step_miss_p (A := A) (H := H) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hgrow0) h96 hgrow_stk hstk_le
        (by rw [hchanged]; intro _ h; exact nomatch h)
        hlen_lt32 hna_le hna_lt hna_ptr
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        halign
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [hchanged]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        ((PutCalleeSavedPlaced.refl s0).step (by simp only [arm64_norm]) hinv_p)
        rfl)
    have hname_mem :
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ⊢
        memRegion x.nameV 24 :=
      vecHeader_entails_memRegion x.nameV nameCap namePtr (BitVec.ofNat 64 x.name.length)
    unfold putSavedCells RustHeap.vecAt vecHeader
    rw [hchanged]
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List _).length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr [] ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hname_mem) (Entails.of_eq (by ac_rfl)))
  | cons hd rest =>
    have hlen_cons_lt32 : (hd :: rest).length < 2 ^ 32 := by rw [← hchanged]; exact hlen_lt32
    have hlen_ne0 : BitVec.ofNat 64 (hd :: rest).length ≠ 0#64 := by
      intro h0
      have h := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_zero,
          List.length_cons] at h
      omega
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        vecBuf A 48 8 (dirEntryAt A) cap ptr (hd :: rest) ∗
          (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
            ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
            ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
            ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
            ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
            ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
            stackAt (s0.sp - 96#64) (stk - 96) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
            ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
            vecU8Rest A nameCap namePtr x.name ∗
            vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl))
        (sepConj_mono_left (vecBuf_expose_arrayAt A 48 8 (dirEntryAt A) cap ptr (hd :: rest)))) ?_
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        ⌜(hd :: rest).length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧
          (hd :: rest).length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((s0.sp - 96#64) ↦₆₄ v0) ∗ ((s0.sp - 88#64) ↦₆₄ v1) ∗
          ((s0.sp - 80#64) ↦₆₄ v2) ∗ ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ v4) ∗ ((s0.sp - 56#64) ↦₆₄ v5) ∗
          ((s0.sp - 48#64) ↦₆₄ v6) ∗ ((s0.sp - 40#64) ↦₆₄ v7) ∗
          ((s0.sp - 32#64) ↦₆₄ v8) ∗ ((s0.sp - 24#64) ↦₆₄ v9) ∗
          ((s0.sp - 16#64) ↦₆₄ v10) ∗ ((s0.sp - 8#64) ↦₆₄ v11) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
          arrayAt (dirEntryAt A) 48 ptr (hd :: rest) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗
             memRegion (ptr + BitVec.ofNat 64 ((hd :: rest).length * 48))
               ((cap.toNat - (hd :: rest).length) * 48)) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool) by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hlen_le, hcap48_lt, _, hptr_ne⟩ => ?_
    have hcap0 : cap ≠ 0 := by
      intro h0
      rw [h0] at hlen_le
      change (hd :: rest).length ≤ 0 at hlen_le
      rw [List.length_cons] at hlen_le
      omega
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_542).base + 80#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    intro hinv_p
    have hx27_eq :
        ((BitVec.ofNat 64 (hd :: rest).length +
            (BitVec.ofNat 64 (hd :: rest).length <<< 1)) <<< 4) =
          BitVec.ofNat 64 (48 * (hd :: rest).length) := by
      rw [mul_48_bv, show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_mul]
    refine SepWPp.weaken_pre ?_
      (step_loop_p (A := A) (H := H) (growStk := growStk) (stk := stk)
        (v3 := v3) (cap := cap) (ptr := ptr) (nameCap := nameCap) (namePtr := namePtr) (R := R)
        (putCalleeOkPlaced_get hbcmp0) (putCalleeOkPlaced_get hdealloc0)
        (putCalleeOkPlaced_get hgrow0)
        h96 hhook96 hgrow_stk hstk_le hlen_lt32
        (by rw [hchanged]; exact hlen_le) hcap48_lt hptr_ne hna_le hna_lt hna_ptr halign
        rest [] hd _ _
        (by rw [hchanged, List.nil_append])
        (fun _ h => nomatch h)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [hchanged]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp [arm64_norm])
        (by simp only [arm64_norm]; exact hx27_eq)
        ((PutCalleeSavedPlaced.refl s0).step (by simp only [arm64_norm]) hinv_p)
        rfl)
    have hname_mem :
        (x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
          ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length) ⊢
        memRegion x.nameV 24 :=
      vecHeader_entails_memRegion x.nameV nameCap namePtr (BitVec.ofNat 64 x.name.length)
    simp only [hcap0, ↓reduceIte, arrayAt_cons, arrayAt_nil, emp_sepConj]
    unfold putSavedCells vecHeader
    rw [hchanged]
    have h0ptr : ptr + BitVec.ofNat 64 (([] : List (List (BitVec 8) × List (BitVec 8))).length * 48) = ptr := by
      simp
    rw [h0ptr]
    refine Entails.trans (Entails.of_eq (show _ =
      (((x.nameV ↦₆₄ nameCap) ∗ ((x.nameV + 8#64) ↦₆₄ namePtr) ∗
        ((x.nameV + 16#64) ↦₆₄ BitVec.ofNat 64 x.name.length)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ v3) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          stackAt (s0.sp - 96#64) (stk - 96) ∗
          (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          dirEntryAt A hd ptr ∗
          arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 48) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((hd :: rest).length * 48))
            ((cap.toNat - (hd :: rest).length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          vecU8Rest A nameCap namePtr x.name ∗
          vecU8 A x.bytesV x.bytes ∗ A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hname_mem) (Entails.of_eq (by ac_rfl)))

theorem dirPut_placed_caller_ok_of_deps [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {A : RustAlloc} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {growProg : Program} {jGrow : Nat} [IsLsBlockProg growProg jGrow H]
    (hjGrow : jGrow < 619 := by decide)
    (hjGrow_unmut : (jGrow ∈ libsignalMutatedBlocks) = false := by decide)
    (hGrow : subroutine_ok growProg (lsmpl.base 586) (growOneDirSpecPlaced A growStk))
    (hstk : 0x60 + max growStk extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 542) (dirPutSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg)
    (dirPut_placed_ok_of_deps hC hBcmp hjGrow hjGrow_unmut hGrow hstk) hi

end CryptoVerification.SignalSession.Cli.Put
