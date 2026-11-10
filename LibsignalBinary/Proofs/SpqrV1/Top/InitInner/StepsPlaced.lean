/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Steps
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `spqr::init_inner` (`Block 324`): Relocatable `[LibsignalPlacement]` Basic-Block Step Lemmas

Relocatable counterparts of the basic-block step lemmas in `InitInner/Steps.lean` on `Block 324`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Top.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

theorem initInner_seq_sepWP_placed {prog : Program}
    {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      Post s' → SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP (mid := mid) ?_
  refine SepWP.mono hstep ?_
  intro s' P1 hpc' hrun' ⟨hent, hpost⟩
  exact SepWPp.weaken_pre hent (hnext s' hpc' hrun' hpost)

/-! ## 1. Version `.v0` Branch (`+0 -> +28 -> +92 -> +116`) and Epilogue (`+416 -> +432`) -/

/-- Full execution of `spqr::init_inner` (`Block 324`) for `v = .v0` (`w1 = 0#32`):
    `+0 -> +28 -> +92 -> +116 -> ret`. -/
theorem init_inner_v0_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 : State) (out : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_324).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v0.toI32) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (memRegion out optProtoInnerStateSize ∗
       stackAt s0.sp initInnerStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          initInnerResultAt A (F := F) out .v0 d authKey ∗
          stackAt s0.sp initInnerStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      stackAt s0.sp initInnerStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono_left (stack_restore_initInner s0))
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [Version.toI32, State.readReg32, Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at hpc hx0 hw1 ⊢
  rw [memRegion_out_224_split_8 out, stackAt_initInner_split s0.sp]
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerResultAt, initInnerValue, Option.map,
    optProtoPqRatchetInnerAt, none3Cap',
    initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Epilogue of `spqr::init_inner` (`Block 324`) for `v = .v1` (`+416 -> +432 -> ret`). -/
theorem init_inner_epilogue_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0 ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp initInnerStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      stackAt s0.sp initInnerStack ∗ Rest :=
    sepConj_mono_left (stack_restore_initInner s0)
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 2. Version `.v1` Prologue (`+0 -> +36`) and Post-`Authenticator::new` Construction -/

/-- Prologue of `spqr::init_inner` (`Block 324`) for `v = .v1` (`w1 = 1#32`):
    `+0 -> +36` (9 instructions). -/
theorem init_inner_prologue_v1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_324).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v1.toI32)
    (hw2 : s0.readReg32 .x2 = d.toI32)
    (hx3 : s0.readReg64 .x3 = akPtr)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 authKey.length) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 36#64) s0
      (cells (s0.sp - 48#64) 6 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ initInnerSavedCells s0 ∗ Rest) ∧
        s1.sp = s0.sp - 1040#64 ∧
        s1.readReg64 .x29 = s0.sp - 48#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length ∧
        s1.readReg32 .x2 = d.toI32 ∧
        s1.readReg64 .x3 = akPtr ∧
        (s1.readReg64 .x22 = s0.readReg64 .x22 ∧
         s1.readReg64 .x23 = s0.readReg64 .x23 ∧
         s1.readReg64 .x24 = s0.readReg64 .x24 ∧
         s1.readReg64 .x25 = s0.readReg64 .x25 ∧
         s1.readReg64 .x26 = s0.readReg64 .x26 ∧
         s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.trace = s0.trace) := by
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  dsimp only [Version.toI32,
    State.readReg32, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hw1 hw2 hx3 hx4 ⊢
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Post-`Authenticator::new` construction for `d = .a2b` (`+368 -> +412`, 11 instructions) on `Block 324`. -/
theorem init_inner_a2b_post_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 368#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 1032#64) 8 ∗
       memRegion (s0.sp - 968#64) 864 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
          memRegion (s0.sp - 104#64) 48 ∗
          Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       memRegion (s0.sp - 968#64) 864) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have h48 :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ⊢
        memRegion (s0.sp - 104#64) 48 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 6 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h64 : (s0.sp - 1032#64) + 64#64 = s0.sp - 968#64 := by bv_omega
    rw [h56, h64]
    refine sepConj_mono ?_ (sepConj_mono_left h48)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.strengthen_entails_const hst ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

set_option maxHeartbeats 1600000 in
/-- Post-`Authenticator::new` construction for `d = .b2a` (`+196 -> +340 -> +400 -> +412`, 41 instructions) on `Block 324`. -/
theorem init_inner_b2a_post_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 56#64) 1 ∗
       cells (s0.sp - 1032#64) 20 ∗
       cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗
       (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗
       memRegion (s0.sp - 568#64) 464 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
          memRegion (s0.sp - 104#64) 56 ∗
          Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 7#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       (emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7) ∗
       memRegion (s0.sp - 568#64) 464) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
       ((s0.sp - 56#64) ↦₆₄ 1#64)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have hpoly :
        emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7 ⊢
        polyDecoderAt A ((s0.sp - 1032#64) + 8#64 + 56#64) initHdrDecoder := by
      have h := polyDecoderAt_initHdrDecoder A (s0.sp - 968#64)
      simpa only [arm64_norm] using h
    have h56_cells :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
        ((s0.sp - 56#64) ↦₆₄ 1#64) ⊢
        memRegion (s0.sp - 104#64) 56 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 7 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5
            (Entails.sepExists_right 1#64 ?_))))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedNoHeaderReceivedAt, unchunkedNoHeaderReceivedAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h464 : (s0.sp - 1032#64) + 464#64 = s0.sp - 568#64 := by bv_omega
    rw [h56, h464]
    refine sepConj_mono ?_ (sepConj_mono_left h56_cells)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpoly)))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.strengthen_entails_const hst ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  simp (config := { maxSteps := 500000 }) only [ProofLib.cells_succ, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  wp_pull_exists
  simp only [emptySortedSetPtCells, arm64_norm, sepConj_emp]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 3. Slice-Clone Basic Blocks (`authKey` -> `vecU8 A (s0.sp - 1032#64) authKey`) -/

/-- `.a2b` empty-slice path (`+36 -> +120 -> +344 -> +364`) on `Block 324`. -/
theorem init_inner_a2b_empty_to_364_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 364#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [Direction.toI32, State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.b2a` empty-slice path (`+36 -> +40 -> +172 -> +192`) on `Block 324`. -/
theorem init_inner_b2a_empty_to_192_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 192#64) s
      (cells (s0.sp - 1032#64) 3 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) [] ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1024#64) ↦₆₄ 1#64) ∗
       ((s0.sp - 1016#64) ↦₆₄ 0#64)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) [] ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nil_of_cells A (s0.sp - 1032#64)
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [Direction.toI32, State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 1 (`+36 -> +120 -> +128`, 3 instructions) on `Block 324`. -/
theorem init_inner_a2b_to_128_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 128#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [Direction.toI32, State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 2 (`+132 -> +140`, 2 instructions) on `Block 324`. -/
theorem init_inner_a2b_132_to_140_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 140#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  wp_steps
  wp_done

/-- `.a2b` non-empty slice OOM branch (`+144 -> +436 -> +444`, 3 instructions) on `Block 324`. -/
theorem init_inner_a2b_144_oom_to_444_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  wp_steps
  wp_done

/-- `.a2b` non-empty slice step 3 (`+144 -> +160`, 4 instructions) on `Block 324`. -/
theorem init_inner_a2b_144_ok_to_160_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hx0 : s.readReg64 .x0 = ptr)
    (hptr_ne : (ptr == 0#64) = false)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 160#64) s
      (cells (s0.sp - 1032#64) 2 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((s0.sp - 1032#64) ↦₆₄ len) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x0 = ptr ∧
        s2.readReg64 .x1 = akPtr ∧
        s2.readReg64 .x2 = len ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.a2b` non-empty slice step 4 (`+164 -> +168 -> +356 -> +364`, 4 instructions) on `Block 324`. -/
theorem init_inner_a2b_164_to_364_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out ptr : BitVec 64) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpos : 0 < authKey.length)
    (hlt : authKey.length < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_324).base + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 364#64) s
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       cells (s0.sp - 1016#64) 1 ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey) ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) authKey ∗ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) authKey ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr authKey hpos hlt hptr
  refine SepWP.strengthen_entails_const hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `.b2a` non-empty slice step 1 (`+36 -> +48`, 3 instructions) on `Block 324`. -/
theorem init_inner_b2a_to_48_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hlen_ne : (len == 0#64) = false)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 48#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [Direction.toI32, State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 ⊢
  wp_steps
  wp_done

/-- `.b2a` non-empty slice step 2 (`+52 -> +60`, 2 instructions) on `Block 324`. -/
theorem init_inner_b2a_52_to_60_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 52#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 60#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x21 = akPtr ∧
        s2.readReg64 .x0 = len ∧
        s2.readReg64 .x1 = 1#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  wp_steps
  wp_done

/-- `.b2a` non-empty slice OOM branch (`+64 -> +436 -> +444`, 3 instructions) on `Block 324`. -/
theorem init_inner_b2a_64_oom_to_444_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (len : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = (blkPl_324).base + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx20 : s.readReg64 .x20 = len)
    (hx0 : s.readReg64 .x0 = 0#64)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 444#64) s
      Rest
      (fun s2 P2 =>
        (P2 ⊢ Rest) ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x0 = 1#64 ∧
        s2.readReg64 .x1 = len ∧
        s2.trace = s0.trace) := by
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.Top.InitInner
